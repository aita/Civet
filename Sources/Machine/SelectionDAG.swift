import COIL
import Tree

// MARK: - DAG Node

/// A node in the selection DAG. Represents either a leaf value (constant, variable)
/// or an operation whose children are other DAG nodes.
final class DAGNode {
    let id: Int
    let kind: DAGNodeKind
    var operands: [DAGNode]
    let type: CType

    /// How many other nodes reference this node as an operand.
    /// Used to determine if a node can be consumed by a multi-node pattern.
    var useCount: Int = 0

    /// Previous side-effect node in the chain (for ordering stores, calls, etc.).
    var chainDep: DAGNode? = nil

    // DP tiling results
    var bestCost: Int = Int.max
    var bestPattern: ISelPattern? = nil

    /// The machine operand produced when this node is emitted.
    /// Set during code emission phase.
    var emittedOperand: Operand? = nil

    init(id: Int, kind: DAGNodeKind, operands: [DAGNode], type: CType) {
        self.id = id
        self.kind = kind
        self.operands = operands
        self.type = type
        for child in operands {
            child.useCount += 1
        }
    }
}

/// The kind of operation a DAG node represents.
enum DAGNodeKind {
    // ── Leaves ──────────────────────────────────────────────────────
    /// A local variable (scalar in virtual register).
    case variable(id: Int, name: String)
    /// A stack-allocated variable (aggregate or address-taken).
    case stackSlot(offset: Int32)
    /// An integer constant.
    case intConst(Int64)
    /// A floating-point constant.
    case floatConst(Double)
    /// A global variable or function reference.
    case global(name: String, isFunction: Bool)
    /// Address of a local label (GNU `&&label`).
    case labelAddr(name: String)

    // ── Integer arithmetic ──────────────────────────────────────────
    case binary(BinaryOp)
    case unary(UnaryOp)

    // ── Memory ──────────────────────────────────────────────────────
    case load
    case store        // side effect: operands[0]=addr, operands[1]=value
    case addressOf
    case member(name: String, offset: Int32)
    case structCopy(size: Int)  // operands[0]=dstAddr, operands[1]=srcAddr
    case alloca                 // operands[0]=size; result = new RSP

    // ── Conversion ──────────────────────────────────────────────────
    case cast(from: CType, to: CType)

    // ── Calls ───────────────────────────────────────────────────────
    case call(argCount: Int, argTypes: [CType])   // operands[0]=callee, rest=args

    // ── Atomics ─────────────────────────────────────────────────────
    case cas          // operands: addr, old, new
    case exchange     // operands: addr, value

    // ── Flags / control ─────────────────────────────────────────────
    case compare      // operands: lhs, rhs (sets flags)
    case test         // operands: value (test for zero)
    case inlineAsm(String)

    /// Whether this operation has side effects beyond producing a value.
    var hasSideEffects: Bool {
        switch self {
        case .store, .call, .cas, .exchange, .compare, .test, .inlineAsm, .structCopy, .alloca:
            return true
        default:
            return false
        }
    }
}

// MARK: - DAG Builder

/// Builds a selection DAG from a COIL basic block.
struct DAGBuilder {
    private var nextNodeId: Int = 0
    /// Maps COIL variable ID → DAG node that defines it in this block.
    private var defMap: [Int: DAGNode] = [:]
    /// Maps COIL variable ID → virtual register (for variables defined before this block).
    private let varMap: [Int: Reg]
    /// Maps COIL variable ID → stack offset (for aggregates).
    private let stackSlots: [Int: Int32]

    /// All nodes created (for iteration/tiling order).
    private(set) var allNodes: [DAGNode] = []
    /// Root nodes that must be emitted (side-effect nodes + live-out values).
    private(set) var roots: [DAGNode] = []
    /// Last side-effect node in the chain.
    private var lastSideEffect: DAGNode? = nil
    /// Load CSE cache: maps address node ID → load node.
    /// Invalidated conservatively on any store (no alias analysis).
    private var loadCache: [Int: DAGNode] = [:]
    /// Cache for varMap variable leaf nodes (deduplication).
    private var varMapNodes: [Int: DAGNode] = [:]
    /// Member node CSE: maps (base node ID, offset) → member node.
    private var memberCache: [Int64: DAGNode] = [:]

    init(varMap: [Int: Reg], stackSlots: [Int: Int32]) {
        self.varMap = varMap
        self.stackSlots = stackSlots
    }

    /// Returns (varMap vreg, DAG node) for variables defined in this block
    /// that have varMap entries. Used to materialize cross-block values.
    func varMapDefs() -> [(vreg: Reg, node: DAGNode)] {
        var result: [(vreg: Reg, node: DAGNode)] = []
        for (id, node) in defMap {
            if let reg = varMap[id] {
                result.append((vreg: reg, node: node))
            }
        }
        return result
    }

    // MARK: - Build

    /// Build DAG from COIL instructions in a basic block.
    mutating func build(instructions: [COIL.Instr], blockLabel: String = "") {
        for instr in instructions {
            buildInstruction(instr)
        }
    }

    private mutating func buildInstruction(_ instr: COIL.Instr) {
        switch instr {
        case .assign(let dest, let src):
            let srcNode = operandNode(src)
            if stackSlots[dest.id] != nil {
                let slotNode = makeNode(.stackSlot(offset: stackSlots[dest.id]!),
                                        operands: [], type: dest.type)
                // Struct/union assignment: emit structCopy (memcpy-like)
                // If src comes from a load (e.g. y = *p), use the load's address
                // as the structCopy source, not the loaded value.
                if case .structType = dest.type {
                    let copySrc = { if case .load = srcNode.kind { return srcNode.operands[0] } else { return srcNode } }()
                    let copyNode = makeNode(.structCopy(size: typeSize(dest.type)),
                                             operands: [slotNode, copySrc], type: .void)
                    addSideEffect(copyNode)
                } else if case .unionType = dest.type {
                    let copySrc = { if case .load = srcNode.kind { return srcNode.operands[0] } else { return srcNode } }()
                    let copyNode = makeNode(.structCopy(size: typeSize(dest.type)),
                                             operands: [slotNode, copySrc], type: .void)
                    addSideEffect(copyNode)
                } else if case .array = dest.type {
                    // Array memzero: use structCopy to zero-fill all bytes.
                    let copyNode = makeNode(.structCopy(size: typeSize(dest.type)),
                                             operands: [slotNode, srcNode], type: .void)
                    addSideEffect(copyNode)
                } else {
                    // Scalar stack-slot variable: emit a store (visible side effect).
                    let storeNode = makeNode(.store, operands: [slotNode, srcNode], type: .void)
                    addSideEffect(storeNode)
                }
            }
            // Don't cache values for stack-slot variables in defMap. They must
            // always be accessed through their stack slot (load/store). Caching
            // is dangerous because memzero lowers as assign(x, 0) with uint type
            // even for struct variables, which would poison subsequent struct
            // member accesses with intConst(0) as the "address".
            if stackSlots[dest.id] == nil {
                defMap[dest.id] = srcNode
            }

        case .binary(let dest, let op, let lhs, let rhs):
            let lNode = operandNode(lhs)
            let rNode = operandNode(rhs)
            let node = makeNode(.binary(op), operands: [lNode, rNode], type: dest.type)
            defMap[dest.id] = node

        case .unary(let dest, let op, let src):
            let srcNode = operandNode(src)
            let node = makeNode(.unary(op), operands: [srcNode], type: dest.type)
            defMap[dest.id] = node

        case .load(let dest, let addr):
            let addrNode = operandNode(addr)
            // Load CSE: reuse existing load from the same address if no
            // intervening store has invalidated the cache.
            if let cached = loadCache[addrNode.id], typeSize(cached.type) == typeSize(dest.type) {
                defMap[dest.id] = cached
            } else {
                let node = makeNode(.load, operands: [addrNode], type: dest.type)
                defMap[dest.id] = node
                loadCache[addrNode.id] = node
            }

        case .store(let addr, let value):
            let addrNode = operandNode(addr)
            let valNode = operandNode(value)
            // Struct/union store through pointer: emit structCopy instead of scalar store.
            if case .structType = value.type {
                // If the value comes from a load (e.g. *q = *p), use the load's
                // source address directly. structCopy needs src ADDRESS, not VALUE.
                let srcNode = { if case .load = valNode.kind { return valNode.operands[0] } else { return valNode } }()
                let node = makeNode(.structCopy(size: typeSize(value.type)),
                                     operands: [addrNode, srcNode], type: .void)
                addSideEffect(node)
            } else if case .unionType = value.type {
                let srcNode = { if case .load = valNode.kind { return valNode.operands[0] } else { return valNode } }()
                let node = makeNode(.structCopy(size: typeSize(value.type)),
                                     operands: [addrNode, srcNode], type: .void)
                addSideEffect(node)
            } else {
                let node = makeNode(.store, operands: [addrNode, valNode], type: .void)
                addSideEffect(node)
            }
            // A store through a pointer may modify any stack-slot variable.
            // Invalidate defMap entries so subsequent uses reload from memory.
            invalidateStackSlotDefs()

        case .addressOf(let dest, let src):
            // addressOf needs the *location* of the variable, not its current value.
            // Bypass defMap to get the stack slot or variable node directly.
            let srcNode = locationNode(src)
            let node = makeNode(.addressOf, operands: [srcNode], type: dest.type)
            defMap[dest.id] = node

        case .cast(let dest, let src, let toType):
            let srcNode = operandNode(src)
            let node = makeNode(.cast(from: src.type, to: toType), operands: [srcNode], type: toType)
            defMap[dest.id] = node

        case .call(let dest, let callee, let args):
            let calleeNode = operandNode(callee)
            let argNodes = args.map { operandNode($0) }
            let argTypes = args.map { $0.type }
            let resultType = dest?.type ?? .void
            let node = makeNode(.call(argCount: args.count, argTypes: argTypes),
                                operands: [calleeNode] + argNodes, type: resultType)
            addSideEffect(node)
            // A call may modify any memory through pointers passed to it.
            invalidateStackSlotDefs()
            if let dest = dest {
                defMap[dest.id] = node
            }

        case .compare(let lhs, let rhs):
            let lNode = operandNode(lhs)
            let rNode = operandNode(rhs)
            let node = makeNode(.compare, operands: [lNode, rNode], type: .void)
            addSideEffect(node)

        case .test(let v):
            let vNode = operandNode(v)
            let node = makeNode(.test, operands: [vNode], type: .void)
            addSideEffect(node)

        case .member(let dest, let base, let name, let offset):
            let baseNode = operandNode(base)
            let memberKey = Int64(baseNode.id) << 32 | Int64(UInt32(bitPattern: offset))
            if let cached = memberCache[memberKey] {
                defMap[dest.id] = cached
            } else {
                let node = makeNode(.member(name: name, offset: offset),
                                    operands: [baseNode], type: dest.type)
                defMap[dest.id] = node
                memberCache[memberKey] = node
            }

        case .alloca(let dest, let size):
            let sizeNode = operandNode(size)
            let node = makeNode(.alloca, operands: [sizeNode], type: dest.type)
            addSideEffect(node)
            defMap[dest.id] = node

        case .asm(let text):
            let node = makeNode(.inlineAsm(text), operands: [], type: .void)
            addSideEffect(node)

        case .cas(let dest, let addr, let old, let new_):
            let addrNode = operandNode(addr)
            let oldNode = operandNode(old)
            let newNode = operandNode(new_)
            let node = makeNode(.cas, operands: [addrNode, oldNode, newNode], type: dest.type)
            addSideEffect(node)
            defMap[dest.id] = node

        case .exchange(let dest, let addr, let value):
            let addrNode = operandNode(addr)
            let valNode = operandNode(value)
            let node = makeNode(.exchange, operands: [addrNode, valNode], type: dest.type)
            addSideEffect(node)
            defMap[dest.id] = node
        }
    }

    // MARK: - Operand → DAG Node

    private mutating func operandNode(_ op: COIL.Operand) -> DAGNode {
        switch op {
        case .variable(let name, let id, let type):
            // Check if defined within this block.
            // Skip defMap for aggregate types — their "value" is their address
            // (array-to-pointer decay / struct address), not a stored scalar.
            // defMap is not set for struct/union in .assign, and arrays skip here.
            if case .array = type {
                // fall through to stackSlots lookup
            } else if let node = defMap[id] {
                return node
            }
            // Check if it's a register-allocated variable
            if varMap[id] != nil {
                if let cached = varMapNodes[id] { return cached }
                let node = makeNode(.variable(id: id, name: name), operands: [], type: type)
                varMapNodes[id] = node
                return node
            }
            // Check if it's a stack slot
            if let offset = stackSlots[id] {
                // Array/struct/union types on the stack: their "value" is their address.
                // Emit addressOf to get the stack slot address (array decay, struct/union pointer).
                switch type {
                case .array, .structType, .unionType:
                    let slot = makeNode(.stackSlot(offset: offset), operands: [], type: type)
                    return makeNode(.addressOf, operands: [slot], type: .pointer(type))
                default:
                    // Scalar stack variable: load its value from the stack slot.
                    // This ensures load/store patterns see a register-based value.
                    let slot = makeNode(.stackSlot(offset: offset), operands: [], type: type)
                    return makeNode(.load, operands: [slot], type: type)
                }
            }
            // Global variable or function
            let isFunc: Bool
            if case .function = type { isFunc = true } else { isFunc = false }
            return makeNode(.global(name: name, isFunction: isFunc), operands: [], type: type)

        case .intConst(let value, let type):
            return makeNode(.intConst(value), operands: [], type: type)

        case .floatConst(let value, let type):
            return makeNode(.floatConst(value), operands: [], type: type)

        case .labelAddr(let label, let type):
            return makeNode(.labelAddr(name: label), operands: [], type: type)
        }
    }

    /// Invalidate defMap entries for all stack-slot variables.
    /// Called after a store, which may alias any address-taken variable.
    private mutating func invalidateStackSlotDefs() {
        for id in stackSlots.keys {
            defMap.removeValue(forKey: id)
        }
    }

    /// Resolve an operand to its *location* (stack slot or variable node),
    /// bypassing the value defMap. Used for `addressOf`.
    private mutating func locationNode(_ op: COIL.Operand) -> DAGNode {
        if case .variable(let name, let id, let type) = op {
            if let offset = stackSlots[id] {
                return makeNode(.stackSlot(offset: offset), operands: [], type: type)
            }
            if varMap[id] != nil {
                return makeNode(.variable(id: id, name: name), operands: [], type: type)
            }
        }
        // Fallback: use the regular operand resolution
        return operandNode(op)
    }

    // MARK: - Helpers

    private mutating func makeNode(_ kind: DAGNodeKind, operands: [DAGNode], type: CType) -> DAGNode {
        let node = DAGNode(id: nextNodeId, kind: kind, operands: operands, type: type)
        nextNodeId += 1
        allNodes.append(node)
        return node
    }

    private mutating func addSideEffect(_ node: DAGNode) {
        node.chainDep = lastSideEffect
        lastSideEffect = node
        roots.append(node)
        // Conservatively invalidate load cache on any store/call/side-effect,
        // since any memory write may alias with cached loads.
        loadCache.removeAll()
    }

    /// Mark nodes whose values are used by the terminator or live-out of the block.
    mutating func markLiveOuts(terminator: COIL.Terminator) {
        for op in terminator.operands {
            if case .variable(_, let id, _) = op, let node = defMap[id] {
                if !roots.contains(where: { $0 === node }) {
                    roots.append(node)
                }
            }
        }
    }

    /// Mark variables that flow into successor phi functions as live-out.
    mutating func markPhiLiveOuts(_ phiOperands: [COIL.Operand]) {
        for op in phiOperands {
            if case .variable(_, let id, _) = op, let node = defMap[id] {
                if !roots.contains(where: { $0 === node }) {
                    roots.append(node)
                }
            }
        }
    }

    /// Look up the DAG node for a variable defined in this block.
    func lookupDef(_ id: Int) -> DAGNode? {
        return defMap[id]
    }

}
