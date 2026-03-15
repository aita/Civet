/// Converts a `CTranslationUnit` (Tree) into a COIL `Program` (CFG form).
///
/// For each function:
/// - Every `CExpr` sub-term is flattened into a fresh temporary operand.
/// - `CStmt` control flow is mapped to basic blocks with `Terminator` edges.
/// - Dead blocks (after a `goto`/`return` with no label) are discarded.
import Tree

public final class TreeConverter {

    // MARK: - Per-function state

    private var completedBlocks: [Block] = []
    private var currentLabel: String = ""
    private var currentInstrs: [Instr] = []
    private var synthLocals: [CVar] = []
    private var genCounter = 0
    /// IDs of local variables and parameters in the current function.
    /// Variables not in this set are globals and need store-through-address.
    private var localIDs: Set<Int> = []

    // MARK: - Public API

    public init() {}

    public func convert(_ unit: CTranslationUnit) -> Program {
        let functions = unit.functions.map { convertFunction($0) }
        return Program(functions: functions, globals: unit.globals)
    }

    public func convertFunction(_ f: CFunction) -> Function {
        // Reset per-function state.
        completedBlocks = []
        currentLabel = "entry"
        currentInstrs = []
        synthLocals = []
        localIDs = []
        for v in f.params + f.locals {
            if case .local(let id) = v.storage {
                localIDs.insert(id)
            }
        }

        if let body = f.body {
            emitStmt(body)
            // If the last block has no explicit terminator, add an implicit return.
            sealCurrentBlock(with: .return(nil))
        }

        return Function(
            name: f.name,
            returnType: f.returnType,
            params: f.params,
            locals: f.locals + synthLocals,
            blocks: completedBlocks,
            isStatic: f.isStatic,
            isInline: f.isInline)
    }

    // MARK: - Statement emission

    private func emitStmt(_ stmt: CStmt) {
        switch stmt {

        case .expr(let e):
            _ = emitExpr(e)  // evaluate for side effects; result discarded

        case .assign(let lhs, let rhs):
            emitAssign(lhs: lhs, rhs: rhs)

        case .return(let val):
            let op = val.map { emitExpr($0) }
            sealCurrentBlock(with: .return(op))
            startDeadBlock()

        case .block(let stmts):
            for s in stmts { emitStmt(s) }

        case .if(let cond, let then, let els):
            let condition = emitCondition(cond)
            let thenLabel = freshLabel("then")
            let joinLabel = freshLabel("join")

            if let els {
                let elseLabel = freshLabel("else")
                sealCurrentBlock(with: .branch(cond: condition, then: thenLabel, else: elseLabel))

                startBlock(label: thenLabel)
                emitStmt(then)
                sealCurrentBlock(with: .goto(joinLabel))

                startBlock(label: elseLabel)
                emitStmt(els)
                sealCurrentBlock(with: .goto(joinLabel))
            } else {
                sealCurrentBlock(with: .branch(cond: condition, then: thenLabel, else: joinLabel))

                startBlock(label: thenLabel)
                emitStmt(then)
                sealCurrentBlock(with: .goto(joinLabel))
            }

            startBlock(label: joinLabel)

        case .label(let l):
            // Seal the current block and start a new one with the given label.
            sealCurrentBlock(with: .goto(l))
            startBlock(label: l)

        case .goto(let l):
            sealCurrentBlock(with: .goto(l))
            startDeadBlock()

        case .computedGoto(let e):
            let op = emitExpr(e)
            sealCurrentBlock(with: .computedGoto(op))
            startDeadBlock()

        case .asm(let text):
            emit(.asm(text))
        }
    }

    // MARK: - Expression emission (flattening)

    /// Lowers `expr` into the current block, returning an `Operand` that holds
    /// the result. For compound expressions a fresh temporary is allocated.
    @discardableResult
    private func emitExpr(_ expr: CExpr) -> Operand {
        switch expr {

        // ── Leaves ────────────────────────────────────────────────────────────

        case .intLiteral(let v, let t):
            return .intConst(v, type: t)

        case .floatLiteral(let v, let t):
            return .floatConst(v, type: t)

        case .variable(let name, let t, let id):
            return .variable(name: name, id: id, type: t)

        // ── Arithmetic / bitwise ──────────────────────────────────────────────

        case .binary(let op, let lhs, let rhs, let t):
            let l = emitExpr(lhs)
            let r = emitExpr(rhs)
            let tmp = freshTemp(type: t)
            emit(.binary(dest: tmp, op: op, lhs: l, rhs: r))
            return tmp.asOperand

        case .unary(let op, let operand, let t):
            let v = emitExpr(operand)
            let tmp = freshTemp(type: t)
            emit(.unary(dest: tmp, op: op, src: v))
            return tmp.asOperand

        // ── Memory ────────────────────────────────────────────────────────────

        case .addressOf(let operand, let t):
            // &(*ptr) → ptr (cancel out addressOf + deref)
            if case .deref(let inner, _) = operand {
                return emitExpr(inner)
            }
            // &(base->member) or &(base.member) → compute member address directly.
            // Don't load the member value — just return its address.
            if case .member(let base, let name, let memberOffset, let memberType) = operand {
                let b: Operand
                if case .deref(let inner, _) = base {
                    b = emitExpr(inner)
                } else {
                    b = emitExpr(base)
                }
                let addrTmp = freshTemp(type: .pointer(memberType))
                emit(.member(dest: addrTmp, base: b, name: name, offset: memberOffset))
                return addrTmp.asOperand
            }
            let v = emitExpr(operand)
            let tmp = freshTemp(type: t)
            emit(.addressOf(dest: tmp, src: v))
            return tmp.asOperand

        case .deref(let operand, let t):
            let addr = emitExpr(operand)
            // Arrays are always passed by address — dereferencing a pointer-to-array
            // (e.g. *(x+0) with type int[3]) just yields the address itself.
            // Structs/unions are NOT included: *ptr for struct must load/copy the value.
            switch t {
            case .array, .vla:
                return addr
            default: break
            }
            let tmp = freshTemp(type: t)
            emit(.load(dest: tmp, addr: addr))
            return tmp.asOperand

        case .member(let base, let name, let memberOffset, let t):
            // member(deref(ptr), name) → use ptr directly as base address.
            // .member treats base as a struct address and computes base + offset.
            // deref would load the struct VALUE, but we need the ADDRESS.
            let b: Operand
            let structType: CType
            if case .deref(let inner, let derefType) = base {
                b = emitExpr(inner)
                structType = derefType
            } else {
                b = emitExpr(base)
                structType = base.type
            }
            let addrTmp = freshTemp(type: .pointer(t))
            emit(.member(dest: addrTmp, base: b, name: name, offset: memberOffset))
            // For scalar types, load the value; for aggregates, the address IS the value.
            switch t {
            case .structType, .unionType, .array:
                return addrTmp.asOperand
            default:
                let valTmp = freshTemp(type: t)
                emit(.load(dest: valTmp, addr: addrTmp.asOperand))
                // Bitfield read: extract bits with shift and mask, then sign-extend.
                let member = Self.findMember(structType, name: name)
                if let m = member, let bitOff = m.bitOffset, let bitW = m.bitWidth {
                    return emitBitfieldRead(val: valTmp.asOperand, type: t,
                                            bitOffset: bitOff, bitWidth: bitW)
                }
                return valTmp.asOperand
            }

        // ── Cast ──────────────────────────────────────────────────────────────

        case .cast(let operand, let toType):
            let v = emitExpr(operand)
            let tmp = freshTemp(type: toType)
            emit(.cast(dest: tmp, src: v, to: toType))
            return tmp.asOperand

        // ── Call ──────────────────────────────────────────────────────────────

        case .call(let callee, let args, let t):
            // Intercept alloca() calls → emit inline stack allocation.
            if case .variable(let name, _, _) = callee, name == "alloca",
               args.count == 1 {
                let sizeOp = emitExpr(args[0])
                let tmp = freshTemp(type: t)
                emit(.alloca(dest: tmp, size: sizeOp))
                return tmp.asOperand
            }
            let calleeOp = emitExpr(callee)
            let argOps = args.map { emitExpr($0) }
            if case .void = t {
                emit(.call(dest: nil, callee: calleeOp, args: argOps))
                return .intConst(0, type: .int(signed: true))
            } else {
                let tmp = freshTemp(type: t)
                emit(.call(dest: tmp, callee: calleeOp, args: argOps))
                return tmp.asOperand
            }

        // ── GNU label address ─────────────────────────────────────────────────

        case .labelAddress(let label, let t):
            return .labelAddr(label, type: t)

        // ── Atomic operations ─────────────────────────────────────────────────

        case .cas(let addr, let old, let new, let t):
            let a = emitExpr(addr)
            let o = emitExpr(old)
            let n = emitExpr(new)
            let tmp = freshTemp(type: t)
            emit(.cas(dest: tmp, addr: a, old: o, new: n))
            return tmp.asOperand

        case .exchange(let addr, let value, let t):
            let a = emitExpr(addr)
            let v = emitExpr(value)
            let tmp = freshTemp(type: t)
            emit(.exchange(dest: tmp, addr: a, value: v))
            return tmp.asOperand
        }
    }

    // MARK: - Assignment emission

    /// Emit an assignment statement. `lhs` is an lvalue:
    ///   variable → assign instruction (copy into named slot)
    ///   deref    → store instruction  (write through pointer)
    ///   other    → evaluate to get variable info, then assign
    private func emitAssign(lhs: CExpr, rhs: CExpr) {
        let rOp = emitExpr(rhs)
        switch lhs {
        case .deref(let ptrExpr, _):
            let addr = emitExpr(ptrExpr)
            emit(.store(addr: addr, value: rOp))
        case .variable(let name, let lhsType, let id):
            if localIDs.contains(id) || id < 0 {
                // Local variable or synthetic temp: use assign (SSA-eligible).
                let place = Place(name: name, id: id, type: lhsType)
                emit(.assign(dest: place, src: rOp))
            } else {
                // Global variable: store through address.
                let globalAddr = Operand.variable(name: name, id: id, type: .pointer(lhsType))
                emit(.store(addr: globalAddr, value: rOp))
            }
        case .member(let base, let name, let memberOffset, let t):
            // Member write: compute address of the member, then store through it.
            // Same deref-cancellation as in emitExpr: member(deref(ptr), name) → use ptr.
            let b: Operand
            let structType: CType
            if case .deref(let inner, let derefType) = base {
                b = emitExpr(inner)
                structType = derefType
            } else {
                b = emitExpr(base)
                structType = base.type
            }
            let addrTmp = freshTemp(type: .pointer(t))
            emit(.member(dest: addrTmp, base: b, name: name, offset: memberOffset))
            // Bitfield write: read-modify-write with mask/shift.
            let member = Self.findMember(structType, name: name)
            if let m = member, let bitOff = m.bitOffset, let bitW = m.bitWidth {
                emitBitfieldWrite(addr: addrTmp.asOperand, value: rOp, type: t,
                                  bitOffset: bitOff, bitWidth: bitW)
            } else {
                emit(.store(addr: addrTmp.asOperand, value: rOp))
            }
        default:
            let lOp = emitExpr(lhs)
            if case .variable(let n, let i, let lt) = lOp {
                if localIDs.contains(i) || i < 0 {
                    let place = Place(name: n, id: i, type: lt)
                    emit(.assign(dest: place, src: rOp))
                } else {
                    let globalAddr = Operand.variable(name: n, id: i, type: .pointer(lt))
                    emit(.store(addr: globalAddr, value: rOp))
                }
            }
        }
    }

    // MARK: - Block management

    private func emit(_ instr: Instr) {
        currentInstrs.append(instr)
    }

    /// Seal `currentBlock` with `terminator` and add it to `completedBlocks`.
    private func sealCurrentBlock(with terminator: Terminator) {
        // Only seal if we are in an active (non-dead) block.
        guard !currentLabel.isEmpty else { return }
        completedBlocks.append(
            Block(
                label: currentLabel,
                instructions: currentInstrs,
                terminator: terminator))
        currentLabel = ""
        currentInstrs = []
    }

    /// Start a new named block. If a previous block was not yet sealed,
    /// an implicit `goto` edge is inserted.
    private func startBlock(label: String) {
        if !currentLabel.isEmpty {
            sealCurrentBlock(with: .goto(label))
        }
        currentLabel = label
        currentInstrs = []
    }

    /// Start an anonymous "dead" block to absorb unreachable instructions.
    private func startDeadBlock() {
        currentLabel = ""
        currentInstrs = []
    }

    // MARK: - Condition emission

    /// Map a Tree `BinaryOp` to a COIL `Condition` if it is a comparison.
    private static func compareCondition(for op: BinaryOp) -> Condition? {
        switch op {
        case .eq: return .eq
        case .ne: return .ne
        case .lt: return .lt
        case .le: return .le
        default: return nil
        }
    }

    /// Emit a condition for a branch. If the expression is a comparison,
    /// emits a `compare` instruction and returns the appropriate `Condition`.
    /// Otherwise emits a `test` instruction and returns `.nonZero`.
    private func emitCondition(_ expr: CExpr) -> Condition {
        if case .binary(let op, let lhs, let rhs, _) = expr,
            let cond = Self.compareCondition(for: op)
        {
            let l = emitExpr(lhs)
            let r = emitExpr(rhs)
            emit(.compare(lhs: l, rhs: r))
            return cond
        }
        let v = emitExpr(expr)
        emit(.test(v))
        return .nonZero
    }

    // MARK: - Bitfield helpers

    /// Extract a bitfield value: shift right by bitOffset, mask to bitWidth bits,
    /// then sign-extend if the type is signed.
    private func emitBitfieldRead(val: Operand, type: CType, bitOffset: Int, bitWidth: Int) -> Operand {
        var v = val
        let intType = type  // the containing storage type (int/short/long)
        // Shift right to position the field at bit 0
        if bitOffset > 0 {
            let shTmp = freshTemp(type: intType)
            emit(.binary(dest: shTmp, op: .shr, lhs: v, rhs: .intConst(Int64(bitOffset), type: intType)))
            v = shTmp.asOperand
        }
        // Mask to bitWidth bits
        let mask = (Int64(1) << bitWidth) - 1
        let maskTmp = freshTemp(type: intType)
        emit(.binary(dest: maskTmp, op: .bitAnd, lhs: v, rhs: .intConst(mask, type: intType)))
        v = maskTmp.asOperand
        // Sign-extend for signed types: shift left then arithmetic shift right.
        // .shr on signed types produces arithmetic shift (sar) at machine level.
        if isSigned(intType) {
            let totalBits = intType.size * 8
            let shiftAmt = totalBits - bitWidth
            if shiftAmt > 0 {
                let shlTmp = freshTemp(type: intType)
                emit(.binary(dest: shlTmp, op: .shl, lhs: v, rhs: .intConst(Int64(shiftAmt), type: intType)))
                let sarTmp = freshTemp(type: intType)
                emit(.binary(dest: sarTmp, op: .shr, lhs: shlTmp.asOperand, rhs: .intConst(Int64(shiftAmt), type: intType)))
                v = sarTmp.asOperand
            }
        }
        return v
    }

    /// Write a bitfield value: read-modify-write the containing storage unit.
    private func emitBitfieldWrite(addr: Operand, value: Operand, type: CType,
                                    bitOffset: Int, bitWidth: Int) {
        let intType = type
        let mask = (Int64(1) << bitWidth) - 1
        // old = load(addr)
        let old = freshTemp(type: intType)
        emit(.load(dest: old, addr: addr))
        // clearMask = ~(mask << bitOffset)
        let clearMask = ~(mask << Int64(bitOffset))
        let cleared = freshTemp(type: intType)
        emit(.binary(dest: cleared, op: .bitAnd, lhs: old.asOperand, rhs: .intConst(clearMask, type: intType)))
        // maskedVal = (value & mask) << bitOffset
        let masked = freshTemp(type: intType)
        emit(.binary(dest: masked, op: .bitAnd, lhs: value, rhs: .intConst(mask, type: intType)))
        let shifted: Operand
        if bitOffset > 0 {
            let shTmp = freshTemp(type: intType)
            emit(.binary(dest: shTmp, op: .shl, lhs: masked.asOperand, rhs: .intConst(Int64(bitOffset), type: intType)))
            shifted = shTmp.asOperand
        } else {
            shifted = masked.asOperand
        }
        // result = cleared | shifted
        let result = freshTemp(type: intType)
        emit(.binary(dest: result, op: .bitOr, lhs: cleared.asOperand, rhs: shifted))
        // store(addr, result)
        emit(.store(addr: addr, value: result.asOperand))
    }

    // MARK: - Name generation

    private func freshLabel(_ hint: String) -> String {
        defer { genCounter += 1 }
        return "%\(hint).\(genCounter)"
    }

    private func freshTemp(type: CType) -> Place {
        defer { genCounter += 1 }
        let name = "%\(genCounter)"
        let id = -(genCounter + 1)
        synthLocals.append(CVar(name: name, type: type, storage: .local(id: id)))
        return Place(name: name, id: id, type: type)
    }

    /// Compute byte offset of a named member within a struct/union type.
    /// Uses chibicc's precomputed offset stored in CStructMember.
    static func computeMemberOffset(_ type: CType, name: String) -> Int32 {
        if let m = findMember(type, name: name) {
            return Int32(m.offset)
        }
        return 0
    }

    /// Find CStructMember by name within a struct/union type.
    /// Recursively searches anonymous struct/union members.
    static func findMember(_ type: CType, name: String) -> CStructMember? {
        switch type {
        case .structType(let r), .unionType(let r):
            // Direct match first.
            if let m = r.members.first(where: { $0.name == name }) {
                return m
            }
            // Recurse into anonymous struct/union members.
            for m in r.members where m.name == nil {
                if let found = findMember(m.type, name: name) {
                    return found
                }
            }
            return nil
        case .pointer(let inner):
            return findMember(inner, name: name)
        default:
            return nil
        }
    }

}
