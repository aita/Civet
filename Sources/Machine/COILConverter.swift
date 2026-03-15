import COIL
import Tree

/// Round `value` up to the nearest multiple of `alignment`.
func alignUp(_ value: Int32, to alignment: Int32) -> Int32 {
    guard alignment > 0 else { return value }
    return (value + alignment - 1) / alignment * alignment
}

/// Converts a COIL program (CFG with virtual operands) to a Machine program
/// (x86-64 instructions with virtual registers).
public struct COILConverter {

    // MARK: - Per-function state

    /// Maps COIL variable ID → virtual register (for scalar types).
    private var varMap: [Int: Reg] = [:]

    /// Maps COIL variable ID → stack offset from rbp (for aggregates / address-taken).
    private var stackSlots: [Int: Int32] = [:]

    /// Running stack allocation offset (positive, used as -offset(%rbp)).
    private var currentStackOffset: Int32 = 0

    /// The machine function being built.
    private var mfunc: Function = Function(name: "")

    /// Accumulated floating-point constant globals.
    private var floatGlobals: [GlobalVar] = []
    private var floatConstCounter: Int = 0

    /// Counter for generating unique float constant labels.
    private var constLabelCounter: Int = 0

    // MARK: - Public API

    public init() {}

    /// Convert an entire COIL program to Machine IR.
    public mutating func convert(_ program: COIL.Program) -> Program {
        let emittableGlobals = program.globals.filter { shouldEmitGlobal($0) }

        // Lower functions (skipping declaration-only functions with no body).
        var functions: [Function] = []
        for f in program.functions where !f.blocks.isEmpty {
            functions.append(lowerFunction(f))
        }

        // Lower globals.
        var globals = emittableGlobals.map { lowerGlobalVar($0) }
        globals.append(contentsOf: floatGlobals)

        // Remove unreferenced static globals (e.g. unused __func__ strings)
        var referenced = referencedSymbols(in: functions)
        // Also collect symbols referenced by global variable relocations
        // (e.g. compound literal globals referenced through pointer initializers).
        for g in globals {
            for r in g.relocations {
                referenced.insert(r.label)
            }
        }
        globals.removeAll { $0.isStatic && !referenced.contains($0.name) }

        return Program(functions: functions, globals: globals)
    }

    /// Collect all symbol names referenced by memory operands in the program.
    private func referencedSymbols(in functions: [Function]) -> Set<String> {
        var syms: Set<String> = []
        for f in functions {
            for block in f.blocks {
                for instr in block.instructions {
                    collectSymbols(instr, into: &syms)
                }
            }
        }
        return syms
    }

    private func collectSymbols(_ instr: Instr, into syms: inout Set<String>) {
        for op in allOperands(of: instr) {
            if case .mem(let m) = op, let s = m.symbol {
                syms.insert(s)
            } else if case .label(let s) = op {
                syms.insert(s)
            }
        }
    }

    /// Extract all operands (src + dst) from an instruction for symbol scanning.
    private func allOperands(of instr: Instr) -> [Operand] {
        switch instr {
        case .imul(_, let s, let d):
            return [s, .reg(d)]
        case .lea(_, let s, let d):
            return [.mem(s), .reg(d)]
        case .movRR(_, let s, let d):
            return [.reg(s), .reg(d)]
        case .movRM(_, let s, let m):
            return [.reg(s), .mem(m)]
        case .movMR(_, let m, let d):
            return [.mem(m), .reg(d)]
        case .movIR(_, let v, let d):
            return [.imm(v), .reg(d)]
        case .movIM(_, let v, let m):
            return [.imm(v), .mem(m)]
        case .movMM(_, let s, let d):
            return [.mem(s), .mem(d)]
        case .aluRmiR(_, _, let s, let d), .cmpRmiR(_, _, let s, let d),
             .shiftR(_, _, let s, let d):
            return [s, .reg(d)]
        case .movsxRmR(_, _, let s, let d), .movzxRmR(_, _, let s, let d):
            return [s, .reg(d)]
        case .cmove(_, _, let s, let d), .cvt(_, _, let s, let d):
            return [s, .reg(d)]
        case .xmmRmR(_, _, let s, let d),
             .xmmCmp(_, let s, let d):
            return [s, .reg(d)]
        case .xmmMovRR(_, let s, let d):
            return [.reg(s), .reg(d)]
        case .xmmMovRM(_, let s, let m):
            return [.reg(s), .mem(m)]
        case .xmmMovMR(_, let m, let d):
            return [.mem(m), .reg(d)]
        case .unaryRm(_, _, let r),
             .pop(_, let r),
             .gpDiv(_, let r, _), .setcc(_, let r),
             .jmpIndirect(let r):
            return [.reg(r)]
        case .push(_, let o), .call(let o), .tailCall(let o):
            return [o]
        case .pcopy(let copies):
            return copies.flatMap { [$0.src, $0.dst] }
        case .signExtendData, .ret, .prologue, .epilogue, .jmp, .jmpIf, .inlineAsm:
            return []
        case .idivRemSeq(_, let d, let a, let b, _, _):
            return [d, a, b]
        }
    }

    // MARK: - Global variable conversion

    private func shouldEmitGlobal(_ v: CVar) -> Bool {
        // Skip function declarations — they are not data globals
        if case .function = v.type { return false }
        // Only emit definitions
        if case .global(_, _, let isDef, _, _, _) = v.storage { return isDef }
        return false
    }

    private mutating func lowerGlobalVar(_ v: CVar) -> GlobalVar {
        let size = v.type.size
        let align = max(v.align ?? v.type.align, 1)
        var initData: [UInt8]? = nil
        var isStatic = false
        var isTentative = false
        var relocations: [GlobalRelocation] = []
        if case .global(let stat, _, _, let tent, let data, let relocs) = v.storage {
            isStatic = stat
            isTentative = tent
            initData = data
            relocations = relocs.map { GlobalRelocation(offset: $0.offset, label: $0.label, addend: $0.addend) }
        }
        let name = v.name
        return GlobalVar(name: name, size: size, alignment: align,
                         initData: initData, relocations: relocations,
                         isStatic: isStatic,
                         isTentative: isTentative)
    }


    // MARK: - Function lowering (DAG + DP instruction selection)

    private mutating func lowerFunction(_ f: COIL.Function) -> Function {
        // Reset per-function state
        varMap = [:]
        stackSlots = [:]
        currentStackOffset = 0
        mfunc = Function(name: f.name, isStatic: f.isStatic)

        // Find address-taken variables (targets of addressOf instructions).
        var addressTaken: Set<Int> = []
        for block in f.blocks {
            for instr in block.instructions {
                if case .addressOf(_, let src) = instr,
                   case .variable(_, let id, _) = src {
                    addressTaken.insert(id)
                }
            }
        }

        // Compute stack offsets for ALL locals first (matching chibicc's layout
        // where all locals are on the stack), then classify each variable as
        // register or stack slot. This preserves relative positions between
        // adjacent variables, which is required for pointer arithmetic like
        // `&y - &z` to work correctly.
        // Allocate locals in reverse order to match chibicc's layout
        // (last declared variable gets the highest stack address).
        let allVars = f.params + f.locals.reversed()
        var precomputedOffsets: [Int: Int32] = [:]
        var tempOffset: Int32 = 0
        for v in allVars {
            guard case .local(let id) = v.storage else { continue }
            let size = max(Int32(v.type.size), 1)
            var align = max(Int32(v.align ?? v.type.align), 1)
            // GCC/System V convention: arrays ≥ 16 bytes are 16-byte aligned.
            if case .array = v.type, size >= 16 { align = max(align, 16) }
            tempOffset = alignUp(tempOffset + size, to: align)
            precomputedOffsets[id] = tempOffset
        }

        for v in allVars {
            guard case .local(let id) = v.storage else { continue }
            if isScalar(v.type) && !addressTaken.contains(id) {
                let reg = mfunc.freshVirtual()
                varMap[id] = reg
            } else {
                let offset = precomputedOffsets[id]!
                stackSlots[id] = offset
                currentStackOffset = max(currentStackOffset, offset)
            }
        }

        // Ensure all SSA variables (phi destinations, instruction dests)
        // have varMap entries. SSA builder creates new variable IDs that
        // aren't in f.locals/f.params.
        for block in f.blocks {
            for phi in block.phis {
                let id = phi.dest.id
                if varMap[id] == nil && stackSlots[id] == nil && !addressTaken.contains(id) {
                    varMap[id] = mfunc.freshVirtual()
                }
            }
            for instr in block.instructions {
                if let dest = instr.dest {
                    let id = dest.id
                    if varMap[id] == nil && stackSlots[id] == nil && !addressTaken.contains(id) {
                        varMap[id] = mfunc.freshVirtual()
                    }
                }
            }
        }

        // Use DAG-based instruction selection
        var isel = InstructionSelector()
        let (blocks, floatGlobs) = isel.selectFunction(
            f,
            varMap: varMap,
            stackSlots: stackSlots,
            mfunc: &mfunc,
            currentStackOffset: &currentStackOffset,
            constLabelCounter: &constLabelCounter
        )
        floatGlobals.append(contentsOf: floatGlobs)

        mfunc.blocks = blocks
        mfunc.stackSize = alignUp(currentStackOffset, to: 16)
        return mfunc
    }

    // MARK: - Helpers

    private func isScalar(_ type: CType) -> Bool {
        switch type {
        case .structType, .unionType, .array, .vla:
            return false
        default:
            return true
        }
    }

}
