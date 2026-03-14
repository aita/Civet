import Tree

// MARK: - Registers

/// A machine register — either a fixed physical register or an
/// unlimited virtual register awaiting allocation.
public enum Reg: Hashable, Sendable {
    case physical(PhysReg)
    case virtual(Int)              // v0, v1, v2, ...
}

/// All x86-64 physical registers the compiler may reference.
public enum PhysReg: UInt8, CaseIterable, Hashable, Sendable {
    // ── General-purpose ──────────────────────────────────────────
    case rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi
    case r8, r9, r10, r11, r12, r13, r14, r15

    // ── SSE ──────────────────────────────────────────────────────
    case xmm0, xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7
    case xmm8, xmm9, xmm10, xmm11, xmm12, xmm13, xmm14, xmm15

    public var isGP: Bool { rawValue <= PhysReg.r15.rawValue }
    public var isXMM: Bool { !isGP }

    /// AT&T name for this register at the given operand width.
    public func name(size: Size) -> String {
        if isXMM { return "%\(self)" }
        return "%\(gpName(size: size))"
    }

    private func gpName(size: Size) -> String {
        switch (self, size) {
        // 8-bit
        case (.rax, .byte): return "al"
        case (.rcx, .byte): return "cl"
        case (.rdx, .byte): return "dl"
        case (.rbx, .byte): return "bl"
        case (.rsp, .byte): return "spl"
        case (.rbp, .byte): return "bpl"
        case (.rsi, .byte): return "sil"
        case (.rdi, .byte): return "dil"
        case (.r8,  .byte): return "r8b"
        case (.r9,  .byte): return "r9b"
        case (.r10, .byte): return "r10b"
        case (.r11, .byte): return "r11b"
        case (.r12, .byte): return "r12b"
        case (.r13, .byte): return "r13b"
        case (.r14, .byte): return "r14b"
        case (.r15, .byte): return "r15b"
        // 16-bit
        case (.rax, .word): return "ax"
        case (.rcx, .word): return "cx"
        case (.rdx, .word): return "dx"
        case (.rbx, .word): return "bx"
        case (.rsp, .word): return "sp"
        case (.rbp, .word): return "bp"
        case (.rsi, .word): return "si"
        case (.rdi, .word): return "di"
        case (.r8,  .word): return "r8w"
        case (.r9,  .word): return "r9w"
        case (.r10, .word): return "r10w"
        case (.r11, .word): return "r11w"
        case (.r12, .word): return "r12w"
        case (.r13, .word): return "r13w"
        case (.r14, .word): return "r14w"
        case (.r15, .word): return "r15w"
        // 32-bit
        case (.rax, .dword): return "eax"
        case (.rcx, .dword): return "ecx"
        case (.rdx, .dword): return "edx"
        case (.rbx, .dword): return "ebx"
        case (.rsp, .dword): return "esp"
        case (.rbp, .dword): return "ebp"
        case (.rsi, .dword): return "esi"
        case (.rdi, .dword): return "edi"
        case (.r8,  .dword): return "r8d"
        case (.r9,  .dword): return "r9d"
        case (.r10, .dword): return "r10d"
        case (.r11, .dword): return "r11d"
        case (.r12, .dword): return "r12d"
        case (.r13, .dword): return "r13d"
        case (.r14, .dword): return "r14d"
        case (.r15, .dword): return "r15d"
        // 64-bit (default)
        default: return "\(self)"
        }
    }
}

// MARK: - System V ABI register lists

extension PhysReg {
    /// Integer argument registers in System V AMD64 ABI order.
    public static let intArgRegs: [PhysReg] = [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

    /// SSE argument registers in System V AMD64 ABI order.
    public static let sseArgRegs: [PhysReg] = [.xmm0, .xmm1, .xmm2, .xmm3,
                                                .xmm4, .xmm5, .xmm6, .xmm7]

    /// All SSE registers (all caller-saved in System V AMD64 ABI).
    public static let allSSE: [PhysReg] = [
        .xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
        .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15,
    ]

    /// Caller-saved GP registers (volatile across calls).
    public static let callerSavedGP: [PhysReg] = [.rax, .rcx, .rdx, .rsi, .rdi,
                                                    .r8, .r9, .r10, .r11]

    /// Callee-saved GP registers (must be preserved across calls).
    public static let calleeSavedGP: [PhysReg] = [.rbx, .r12, .r13, .r14, .r15]

    /// GP registers available for allocation (excludes rsp, rbp).
    public static let allocatableGP: [PhysReg] = callerSavedGP + calleeSavedGP
}

// MARK: - Operands

/// Operand width. Determines the AT&T instruction suffix and
/// which sub-register slice is accessed.
public enum Size: UInt8, Sendable {
    case byte  = 1    // 8-bit   suffix "b"
    case word  = 2    // 16-bit  suffix "w"
    case dword = 4    // 32-bit  suffix "l"
    case qword = 8    // 64-bit  suffix "q"
    case single = 14  // 32-bit float  suffix "ss"
    case double_ = 18 // 64-bit float  suffix "sd"

    /// AT&T instruction suffix.
    public var suffix: String {
        switch self {
        case .byte:    return "b"
        case .word:    return "w"
        case .dword:   return "l"
        case .qword:   return "q"
        case .single:  return "ss"
        case .double_: return "sd"
        }
    }

    /// Map a C type to its machine size on x86-64.
    public static func from(_ type: CType) -> Size {
        switch type {
        case .void:              return .dword  // shouldn't happen, fallback
        case .bool, .char:       return .byte
        case .short:             return .word
        case .int, .enumType:    return .dword
        case .long:              return .qword
        case .float:             return .single
        case .double:            return .double_
        case .longDouble:        return .double_ // treat as double for now
        case .pointer:           return .qword
        case .array:             return .qword   // decays to pointer
        case .vla:               return .qword
        case .function:          return .qword   // function pointer
        case .structType:        return .qword   // pointer to struct
        case .unionType:         return .qword
        }
    }
}

/// A machine operand: register, immediate, or memory location.
public enum Operand: Sendable {
    /// A register (physical or virtual).
    case reg(Reg)

    /// An integer immediate.
    case imm(Int64)

    /// A memory location using x86 addressing modes.
    case mem(Memory)

    /// A symbolic reference (function name, global label).
    case label(String)
}

/// x86-64 memory addressing mode.
///
///   `[base + index*scale + displacement]`
///   `symbol(%rip)` for globals (RIP-relative)
///   `-offset(%rbp)` for stack slots
public struct Memory: Hashable, Sendable {
    public var base: Reg?
    public var index: Reg?
    public var scale: UInt8       // 1, 2, 4, or 8
    public var displacement: Int32
    public var symbol: String?    // for RIP-relative addressing

    public init(base: Reg? = nil, index: Reg? = nil, scale: UInt8 = 1,
                displacement: Int32 = 0, symbol: String? = nil) {
        self.base = base
        self.index = index
        self.scale = scale
        self.displacement = displacement
        self.symbol = symbol
    }

    /// Stack slot at `[rbp - offset]`.
    public static func stack(_ offset: Int32) -> Memory {
        Memory(base: .physical(.rbp), displacement: -offset)
    }

    /// RIP-relative global reference.
    public static func global(_ name: String) -> Memory {
        Memory(symbol: name)
    }

    /// Whether this is a stack-relative memory operand (base is rbp, no symbol).
    public var isStack: Bool {
        if case .physical(.rbp) = base, symbol == nil { return true }
        return false
    }
}

// MARK: - Sub-opcode enums

/// ALU binary operation sub-opcodes (add, sub, and, or, xor).
public enum AluOp: UInt8, Sendable {
    case add, sub, and, or, xor
}

/// Shift operation sub-opcodes (shl, shr, sar).
public enum ShiftOp: UInt8, Sendable {
    case shl, shr, sar
}

/// Unary operation sub-opcodes (neg, not).
public enum GpUnaryOp: UInt8, Sendable {
    case neg, not
}

/// Compare/test sub-opcodes.
public enum CmpOp: UInt8, Sendable {
    case cmp, test
}

/// SSE binary operation sub-opcodes.
public enum SseOp: UInt8, Sendable {
    case add, sub, mul, div
}

// MARK: - Instructions

/// x86-64 condition codes for Jcc, CMOVcc, SETcc.
public enum CondCode: String, Sendable {
    case e   = "e"     // equal (ZF=1)
    case ne  = "ne"    // not equal
    case l   = "l"     // less (signed)
    case le  = "le"    // less or equal (signed)
    case g   = "g"     // greater (signed)
    case ge  = "ge"    // greater or equal (signed)
    case b   = "b"     // below (unsigned)
    case be  = "be"    // below or equal (unsigned)
    case a   = "a"     // above (unsigned)
    case ae  = "ae"    // above or equal (unsigned)
    case s   = "s"     // sign (SF=1)
    case ns  = "ns"    // not sign
    case z   = "z"     // zero (alias of e)
    case nz  = "nz"    // not zero (alias of ne)
    case p   = "p"     // parity (PF=1, unordered float)
    case np  = "np"    // not parity (PF=0, ordered float)

    /// The inverted condition.
    public var inverted: CondCode {
        switch self {
        case .e:  return .ne;  case .ne: return .e
        case .l:  return .ge;  case .ge: return .l
        case .le: return .g;   case .g:  return .le
        case .b:  return .ae;  case .ae: return .b
        case .be: return .a;   case .a:  return .be
        case .s:  return .ns;  case .ns: return .s
        case .z:  return .nz;  case .nz: return .z
        case .p:  return .np;  case .np: return .p
        }
    }
}

/// A single x86-64 machine instruction.
///
/// Uses grouped instruction kinds for register-allocator-friendly
/// representation, inspired by wazero/Cranelift.
/// 2-address form (dst = dst OP src) matching x86 hardware.
public enum Instr: Sendable {

    // ── Grouped ALU (2-address: dst OP= src) ──────────────────────
    /// add/sub/and/or/xor grouped by AluOp sub-opcode.
    case aluRmiR(AluOp, Size, src: Operand, dst: Reg)
    case imul(Size, src: Operand, dst: Reg)
    /// cmp/test grouped by CmpOp sub-opcode. Sets flags only.
    case cmpRmiR(CmpOp, Size, src: Operand, dst: Reg)
    /// shl/shr/sar grouped by ShiftOp sub-opcode. src must be imm or cl.
    case shiftR(ShiftOp, Size, src: Operand, dst: Reg)
    /// neg/not grouped by GpUnaryOp sub-opcode.
    case unaryRm(GpUnaryOp, Size, Reg)

    // ── Data movement ─────────────────────────────────────────────
    /// Register-to-register move. Defines dst.
    case movRR(Size, src: Reg, dst: Reg)
    /// Store: register to memory. No register def.
    case movRM(Size, src: Reg, dst: Memory)
    /// Load: memory to register. Defines dst.
    case movMR(Size, src: Memory, dst: Reg)
    /// Immediate to register. Defines dst.
    case movIR(Size, imm: Int64, dst: Reg)
    /// Immediate to memory. No register def.
    case movIM(Size, imm: Int64, dst: Memory)
    /// Memory to memory (illegal in x86, expanded by fixIllegalInstrs).
    case movMM(Size, src: Memory, dst: Memory)
    /// Sign-extending move. src: Reg|Mem, dst always Reg. Defines dst.
    case movsxRmR(from: Size, to: Size, src: Operand, dst: Reg)
    /// Zero-extending move. src: Reg|Mem, dst always Reg. Defines dst.
    case movzxRmR(from: Size, to: Size, src: Operand, dst: Reg)
    case lea(Size, src: Memory, dst: Reg)
    case push(Size, Operand)
    case pop(Size, Reg)

    // ── Division ──────────────────────────────────────────────────
    /// Sign-extend rax into rdx:rax (cqo/cdq/cwd).
    case signExtendData(Size)
    /// Integer divide rdx:rax by operand. signed=true → idiv, false → div.
    /// Quotient → rax, remainder → rdx.
    case gpDiv(Size, Reg, signed: Bool)
    /// Division/modulo pseudo-instruction: expanded by ConstraintResolver.
    case idivRemSeq(Size, dst: Operand, dividend: Operand,
                    divisor: Operand, signed: Bool, isDiv: Bool)

    // ── Conditional ───────────────────────────────────────────────
    /// setcc dst — set byte to 0 or 1 based on flags.
    case setcc(CondCode, Reg)
    /// cmovcc src, dst — conditional move.
    case cmove(CondCode, Size, src: Operand, dst: Reg)

    // ── Control flow ──────────────────────────────────────────────
    case jmp(String)
    case jmpIf(CondCode, String)
    case jmpIndirect(Reg)
    case call(Operand)
    /// Tail call: jump to an external function (replaces call+ret).
    case tailCall(Operand)
    case ret

    // ── SSE floating-point ────────────────────────────────────────
    /// Grouped SSE binary: add/sub/mul/div by SseOp sub-opcode.
    case xmmRmR(SseOp, Size, src: Operand, dst: Reg)
    /// SSE register-to-register move. Defines dst.
    case xmmMovRR(Size, src: Reg, dst: Reg)
    /// SSE store: register to memory. No register def.
    case xmmMovRM(Size, src: Reg, dst: Memory)
    /// SSE load: memory to register. Defines dst.
    case xmmMovMR(Size, src: Memory, dst: Reg)
    /// SSE compare (ucomiss/ucomisd, distinguished by Size).
    case xmmCmp(Size, src: Operand, dst: Reg)
    case cvt(from: Size, to: Size, src: Operand, dst: Reg)

    // ── Pseudo-instructions ───────────────────────────────────────
    case prologue
    case epilogue
    case inlineAsm(String)
    /// Parallel copy: all copies happen simultaneously. Expanded after regalloc.
    case pcopy([(src: Operand, dst: Operand, sz: Size)])
}

extension Instr {
    /// Factory: dispatch a generic mov (Operand, Operand) to the appropriate
    /// typed variant (movRR/movRM/movMR/movIR/movIM).
    public static func mov(_ sz: Size, src: Operand, dst: Operand) -> Instr {
        switch (src, dst) {
        case (.reg(let s), .reg(let d)):  return .movRR(sz, src: s, dst: d)
        case (.reg(let s), .mem(let m)):  return .movRM(sz, src: s, dst: m)
        case (.mem(let m), .reg(let d)):  return .movMR(sz, src: m, dst: d)
        case (.imm(let v), .reg(let d)):  return .movIR(sz, imm: v, dst: d)
        case (.imm(let v), .mem(let m)):  return .movIM(sz, imm: v, dst: m)
        case (.mem(let m1), .mem(let m2)): return .movMM(sz, src: m1, dst: m2)
        // label is a symbolic address — use lea for RIP-relative address loading
        case (.label(let name), .reg(let d)):
            return .lea(sz, src: Memory(symbol: name), dst: d)
        default: fatalError("invalid mov operand combination: \(src) → \(dst)")
        }
    }

    /// Decompose any mov variant back to (sz, src: Operand, dst: Operand).
    /// Returns nil for non-mov instructions.
    public var movComponents: (sz: Size, src: Operand, dst: Operand)? {
        switch self {
        case .movRR(let sz, let s, let d): return (sz, .reg(s), .reg(d))
        case .movRM(let sz, let s, let m): return (sz, .reg(s), .mem(m))
        case .movMR(let sz, let m, let d): return (sz, .mem(m), .reg(d))
        case .movIR(let sz, let v, let d): return (sz, .imm(v), .reg(d))
        case .movIM(let sz, let v, let m): return (sz, .imm(v), .mem(m))
        case .movMM(let sz, let s, let d): return (sz, .mem(s), .mem(d))
        default: return nil
        }
    }

    /// True if this instruction is any mov variant.
    public var isMov: Bool { movComponents != nil }

    /// Factory: dispatch a generic xmmMov (Operand, Operand) to the appropriate
    /// typed variant (xmmMovRR/xmmMovRM/xmmMovMR).
    public static func xmmMov(_ sz: Size, src: Operand, dst: Operand) -> Instr {
        switch (src, dst) {
        case (.reg(let s), .reg(let d)):  return .xmmMovRR(sz, src: s, dst: d)
        case (.reg(let s), .mem(let m)):  return .xmmMovRM(sz, src: s, dst: m)
        case (.mem(let m), .reg(let d)):  return .xmmMovMR(sz, src: m, dst: d)
        default: fatalError("invalid xmmMov operand combination: \(src) → \(dst)")
        }
    }

    /// Transform all memory operands within this instruction.
    func mapMemory(_ transform: (Memory) -> Memory) -> Instr {
        func mapMem(_ m: Memory) -> Memory { transform(m) }
        func mapReg(_ r: Reg) -> Reg {
            // Registers are not affected by memory transforms
            return r
        }
        func mapOp(_ op: Operand) -> Operand {
            if case .mem(let m) = op { return .mem(transform(m)) }
            return op
        }
        switch self {
        // Grouped ALU
        case .aluRmiR(let op, let sz, let s, let d):
            return .aluRmiR(op, sz, src: mapOp(s), dst: d)
        case .imul(let sz, let s, let d):  return .imul(sz, src: mapOp(s), dst: d)
        case .cmpRmiR(let op, let sz, let s, let d):
            return .cmpRmiR(op, sz, src: mapOp(s), dst: d)
        case .shiftR(let op, let sz, let s, let d):
            return .shiftR(op, sz, src: mapOp(s), dst: d)
        case .unaryRm(let op, let sz, let r):
            return .unaryRm(op, sz, r)
        // Data movement
        case .movRR:                       return self  // no memory operands
        case .movRM(let sz, let s, let m): return .movRM(sz, src: s, dst: mapMem(m))
        case .movMR(let sz, let m, let d): return .movMR(sz, src: mapMem(m), dst: d)
        case .movIR:                       return self  // no memory operands
        case .movIM(let sz, let v, let m): return .movIM(sz, imm: v, dst: mapMem(m))
        case .movMM(let sz, let s, let d): return .movMM(sz, src: mapMem(s), dst: mapMem(d))
        case .movsxRmR(let f, let t, let s, let d): return .movsxRmR(from: f, to: t, src: mapOp(s), dst: d)
        case .movzxRmR(let f, let t, let s, let d): return .movzxRmR(from: f, to: t, src: mapOp(s), dst: d)
        case .lea(let sz, let m, let d):   return .lea(sz, src: mapMem(m), dst: d)
        case .push(let sz, let o):         return .push(sz, mapOp(o))
        case .pop:                         return self
        // Division
        case .gpDiv:                       return self
        case .idivRemSeq(let sz, let d, let a, let b, let s, let isDiv):
            return .idivRemSeq(sz, dst: mapOp(d), dividend: mapOp(a), divisor: mapOp(b), signed: s, isDiv: isDiv)
        // Conditional
        case .setcc:                       return self
        case .cmove(let cc, let sz, let s, let d):
            return .cmove(cc, sz, src: mapOp(s), dst: d)
        // Control flow
        case .jmpIndirect:                 return self
        case .call(let o):                 return .call(mapOp(o))
        case .tailCall(let o):             return .tailCall(mapOp(o))
        // SSE
        case .xmmRmR(let op, let sz, let s, let d):
            return .xmmRmR(op, sz, src: mapOp(s), dst: d)
        case .xmmMovRR:                    return self  // no memory operands
        case .xmmMovRM(let sz, let s, let m): return .xmmMovRM(sz, src: s, dst: mapMem(m))
        case .xmmMovMR(let sz, let m, let d): return .xmmMovMR(sz, src: mapMem(m), dst: d)
        case .xmmCmp(let sz, let s, let d):
            return .xmmCmp(sz, src: mapOp(s), dst: d)
        case .cvt(let f, let t, let s, let d): return .cvt(from: f, to: t, src: mapOp(s), dst: d)
        // Pseudo
        case .pcopy(let copies):
            return .pcopy(copies.map { (src: mapOp($0.src), dst: mapOp($0.dst), sz: $0.sz) })
        case .jmp, .jmpIf, .ret, .signExtendData, .prologue, .epilogue, .inlineAsm:
            return self
        }
    }
}

// MARK: - Machine Phi

/// A Machine SSA phi node, present before phi elimination.
/// After register allocation, phi elimination converts these into
/// parallel-copy instructions inserted at the end of each predecessor.
public struct MachPhi: Sendable {
    /// Destination virtual register (becomes physical after RA rewriting).
    public var dest: Reg
    public let size: Size
    /// One entry per predecessor: (predecessor block label, source operand).
    public var args: [(label: String, src: Operand)]

    public init(dest: Reg, size: Size, args: [(label: String, src: Operand)] = []) {
        self.dest = dest
        self.size = size
        self.args = args
    }
}

// MARK: - Function & Program

/// A machine basic block: a label and a sequence of instructions.
/// The last instruction is typically a control-flow instruction (jmp/jcc/ret).
/// `phis` holds Machine SSA phi nodes; non-empty only before phi elimination.
public struct Block: Sendable {
    public let label: String
    public var phis: [MachPhi]
    public var instructions: [Instr]

    public init(label: String, phis: [MachPhi] = [], instructions: [Instr] = []) {
        self.label = label
        self.phis = phis
        self.instructions = instructions
    }
}

/// A machine function: CFG plus stack frame metadata.
public struct Function: Sendable {
    public let name: String
    public var blocks: [Block]
    public var stackSize: Int32
    public var calleeSaved: [PhysReg]
    public let isStatic: Bool
    public var nextVirtual: Int

    public init(name: String, blocks: [Block] = [], isStatic: Bool = false) {
        self.name = name
        self.blocks = blocks
        self.stackSize = 0
        self.calleeSaved = []
        self.isStatic = isStatic
        self.nextVirtual = 0
    }

    /// Allocate a fresh virtual register.
    public mutating func freshVirtual() -> Reg {
        defer { nextVirtual += 1 }
        return .virtual(nextVirtual)
    }
}

/// A global variable with optional initial data.
public struct GlobalVar: Sendable {
    public let name: String
    public let size: Int
    public let alignment: Int
    public let initData: [UInt8]?
    public let isStatic: Bool
    public let isTentative: Bool

    public init(name: String, size: Int, alignment: Int,
                initData: [UInt8]? = nil, isStatic: Bool = false,
                isTentative: Bool = false) {
        self.name = name
        self.size = size
        self.alignment = alignment
        self.initData = initData
        self.isStatic = isStatic
        self.isTentative = isTentative
    }
}

/// The complete machine program.
public struct Program: Sendable {
    public var functions: [Function]
    public var globals: [GlobalVar]

    public init(functions: [Function] = [], globals: [GlobalVar] = []) {
        self.functions = functions
        self.globals = globals
    }
}

// MARK: - Register Constraints

/// Declarative description of an instruction's physical register requirements.
/// Used by the constraint resolver and the register allocator to correctly
/// handle implicit physical register usage.
public struct RegConstraint: Sendable {
    /// Physical registers that the instruction implicitly reads.
    public var inputs: [PhysReg]
    /// Physical registers that the instruction implicitly writes (results).
    public var outputs: [PhysReg]
    /// Physical registers that the instruction destroys but doesn't produce
    /// meaningful results in (e.g., caller-saved registers across a call).
    public var clobbers: Set<PhysReg>

    public init(inputs: [PhysReg] = [], outputs: [PhysReg] = [],
                clobbers: Set<PhysReg> = []) {
        self.inputs = inputs
        self.outputs = outputs
        self.clobbers = clobbers
    }

    /// True if this instruction has no physical register constraints.
    public var isEmpty: Bool {
        inputs.isEmpty && outputs.isEmpty && clobbers.isEmpty
    }

    /// All physical registers involved (inputs + outputs + clobbers).
    public var allPhysRegs: Set<PhysReg> {
        var s = clobbers
        for r in inputs { s.insert(r) }
        for r in outputs { s.insert(r) }
        return s
    }
}

/// Returns the physical register constraints for a given instruction.
public func regConstraint(for instr: Instr) -> RegConstraint {
    switch instr {
    // signExtendData: sign-extends rax into rdx:rax
    case .signExtendData:
        return RegConstraint(inputs: [.rax], outputs: [.rdx])

    // gpDiv: divides rdx:rax by operand, quotient→rax, remainder→rdx
    case .gpDiv:
        return RegConstraint(inputs: [.rax, .rdx], outputs: [.rax, .rdx])

    // Shifts with register count must use %cl (rcx)
    case .shiftR(_, _, let src, _):
        if case .reg(.physical(.rcx)) = src {
            return RegConstraint(inputs: [.rcx])
        }
        return RegConstraint()

    // call: clobbers all caller-saved GP + all SSE
    case .call:
        return RegConstraint(
            clobbers: Set(PhysReg.callerSavedGP + PhysReg.allSSE))

    default:
        return RegConstraint()
    }
}
