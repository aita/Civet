/// Emits x86-64 AT&T syntax assembly from a Machine program.
public struct AsmPrinter {

    public init() {}

    public func emit(_ program: Program) -> String {
        var out = ""
        out += "    .text\n"

        for f in program.functions {
            emitFunction(f, into: &out)
        }

        if !program.globals.isEmpty {
            out += "\n"
            for g in program.globals {
                emitGlobal(g, into: &out)
            }
        }

        return out
    }

    // MARK: - Function emission

    private func emitFunction(_ f: Function, into out: inout String) {
        out += "\n"
        if !f.isStatic {
            out += "    .globl \(f.name)\n"
        }
        out += "\(f.name):\n"

        for block in f.blocks {
            // Emit block label (skip if it's the function name itself)
            if block.label != "entry" {
                out += "\(blockLabel(block.label, in: f.name)):\n"
            }
            for instr in block.instructions {
                out += "    \(formatInstr(instr, functionName: f.name))\n"
            }
        }
    }

    // MARK: - Global emission

    private func emitGlobal(_ g: GlobalVar, into out: inout String) {
        // Tentative definitions use .comm (weak linkage, merged by linker)
        if g.isTentative {
            out += "    .comm \(g.name), \(g.size), \(g.alignment)\n"
            return
        }

        if g.isStatic {
            // Local symbol — use .local or just don't .globl
        } else {
            out += "    .globl \(g.name)\n"
        }

        if let data = g.initData {
            out += "    .data\n"
            out += "    .align \(g.alignment)\n"
            out += "\(g.name):\n"

            // Try to emit as a NUL-terminated string if the data looks like one
            if isNulTerminatedString(data) {
                let str = String(data.dropLast().map { Character(UnicodeScalar($0)) })
                out += "    .asciz \"\(escapeString(str))\"\n"
            } else {
                emitDataBytes(data, into: &out)
            }
        } else {
            // BSS (zero-initialized)
            out += "    .bss\n"
            out += "    .align \(g.alignment)\n"
            out += "\(g.name):\n"
            out += "    .zero \(g.size)\n"
        }
    }

    // MARK: - Instruction formatting

    private func formatInstr(_ instr: Instr, functionName: String) -> String {
        switch instr {
        // Data movement
        case .movRR(let sz, let s, let d):
            return "mov\(sz.suffix) \(fmtReg(s, size: sz)), \(fmtReg(d, size: sz))"
        case .movRM(let sz, let s, let m):
            return "mov\(sz.suffix) \(fmtReg(s, size: sz)), \(fmtMem(m))"
        case .movMR(let sz, let m, let d):
            return "mov\(sz.suffix) \(fmtMem(m)), \(fmtReg(d, size: sz))"
        case .movIR(let sz, let v, let d):
            return "mov\(sz.suffix) $\(v), \(fmtReg(d, size: sz))"
        case .movIM(let sz, let v, let m):
            return "mov\(sz.suffix) $\(v), \(fmtMem(m))"
        case .movMM:
            fatalError("movMM must be expanded before assembly printing")
        case .movsxRmR(let from, let to, let src, let dst):
            return "movs\(from.suffix)\(to.intSuffix) \(fmt(src, from)), \(fmtReg(dst, size: to))"
        case .movzxRmR(let from, let to, let src, let dst):
            // movzlq doesn't exist: 32-bit mov implicitly zero-extends to 64-bit.
            if from == .dword && to == .qword {
                return "movl \(fmt(src, .dword)), \(fmtReg(dst, size: .dword))"
            }
            return "movz\(from.suffix)\(to.intSuffix) \(fmt(src, from)), \(fmtReg(dst, size: to))"
        case .lea(let sz, let src, let dst):
            return "lea\(sz.suffix) \(fmtMem(src)), \(fmtReg(dst, size: sz))"
        case .push(let sz, let op):
            return "push\(sz.suffix) \(fmt(op, sz))"
        case .pop(let sz, let r):
            return "pop\(sz.suffix) \(fmtReg(r, size: sz))"

        // Grouped ALU (add/sub/and/or/xor)
        case .aluRmiR(let op, let sz, let src, let dst):
            return "\(op.mnemonic)\(sz.suffix) \(fmt(src, sz)), \(fmtReg(dst, size: sz))"
        case .imul(let sz, let src, let dst):
            return "imul\(sz.suffix) \(fmt(src, sz)), \(fmtReg(dst, size: sz))"
        case .signExtendData(let sz):
            switch sz {
            case .qword: return "cqo"
            case .dword: return "cdq"
            case .word:  return "cwd"
            default:     return "cqo"
            }
        case .gpDiv(let sz, let r, let signed):
            return "\(signed ? "idiv" : "div")\(sz.suffix) \(fmtReg(r, size: sz))"
        case .unaryRm(let op, let sz, let r):
            return "\(op.mnemonic)\(sz.suffix) \(fmtReg(r, size: sz))"

        // Shifts (shl/shr/sar)
        case .shiftR(let op, let sz, let src, let dst):
            return "\(op.mnemonic)\(sz.suffix) \(fmtShift(src)), \(fmtReg(dst, size: sz))"

        // Comparison / test
        case .cmpRmiR(let op, let sz, let src, let dst):
            return "\(op.mnemonic)\(sz.suffix) \(fmt(src, sz)), \(fmtReg(dst, size: sz))"

        // Conditional
        case .setcc(let cc, let r):
            return "set\(cc.rawValue) \(fmtReg(r, size: .byte))"
        case .cmove(let cc, let sz, let src, let dst):
            return "cmov\(cc.rawValue)\(sz.suffix) \(fmt(src, sz)), \(fmtReg(dst, size: sz))"

        // Control flow
        case .jmp(let label):
            return "jmp \(blockLabel(label, in: functionName))"
        case .jmpIf(let cc, let label):
            return "j\(cc.rawValue) \(blockLabel(label, in: functionName))"
        case .jmpIndirect(let r):
            return "jmp *\(fmtReg(r, size: .qword))"
        case .call(let op):
            return formatCall(op)
        case .tailCall(let op):
            return formatTailJmp(op)
        case .ret:
            return "ret"

        // SSE
        case .xmmMovRR(let sz, let s, let d):
            return "\(xmmMovMnemonic(sz)) \(fmtReg(s, size: sz)), \(fmtReg(d, size: sz))"
        case .xmmMovRM(let sz, let s, let m):
            return "\(xmmMovMnemonic(sz)) \(fmtReg(s, size: sz)), \(fmtMem(m))"
        case .xmmMovMR(let sz, let m, let d):
            return "\(xmmMovMnemonic(sz)) \(fmtMem(m)), \(fmtReg(d, size: sz))"
        case .xmmRmR(let op, let sz, let src, let dst):
            return "\(op.mnemonic)\(sseSuffix(sz)) \(fmt(src, sz)), \(fmtReg(dst, size: sz))"
        case .xmmCmp(let sz, let src, let dst):
            let cmpSuffix = sz == .single ? "s" : "d"
            return "ucomis\(cmpSuffix) \(fmt(src, sz)), \(fmtReg(dst, size: sz))"
        case .cvt(let from, let to, let src, let dst):
            return "cvt\(cvtMnemonic(from: from, to: to)) \(fmt(src, from)), \(fmtReg(dst, size: to))"

        // Pseudo
        case .prologue:
            return "# prologue (unexpanded)"
        case .epilogue:
            return "# epilogue (unexpanded)"
        case .inlineAsm(let text):
            return text

        case .pcopy:
            fatalError("pcopy must be expanded before assembly printing")
        case .idivRemSeq:
            fatalError("pseudo-instructions must be expanded before assembly printing")
        }
    }

    // MARK: - Operand formatting

    private func fmt(_ op: Operand, _ size: Size) -> String {
        switch op {
        case .reg(let r):
            return fmtReg(r, size: size)
        case .imm(let v):
            return "$\(v)"
        case .mem(let m):
            return fmtMem(m)
        case .label(let name):
            return "\(name)"
        }
    }

    private func fmtReg(_ reg: Reg, size: Size) -> String {
        switch reg {
        case .physical(let p):
            return p.name(size: size)
        case .virtual(let v):
            return "%v\(v)"  // Should not appear after regalloc
        }
    }

    private func fmtMem(_ m: Memory) -> String {
        if let sym = m.symbol {
            // RIP-relative: symbol(%rip)
            if let base = m.base {
                return "\(sym)(\(fmtReg(base, size: .qword)))"
            }
            return "\(sym)(%rip)"
        }

        var result = ""

        // Displacement
        if m.displacement != 0 {
            result += "\(m.displacement)"
        }

        // Base + index
        if let base = m.base {
            result += "(\(fmtReg(base, size: .qword))"
            if let index = m.index {
                result += ", \(fmtReg(index, size: .qword))"
                if m.scale > 1 {
                    result += ", \(m.scale)"
                }
            }
            result += ")"
        } else if let index = m.index {
            result += "(, \(fmtReg(index, size: .qword)), \(m.scale))"
        }

        return result.isEmpty ? "0" : result
    }

    /// Format shift source: cl register uses %cl regardless of operand size.
    private func fmtShift(_ op: Operand) -> String {
        switch op {
        case .imm(let v):
            return "$\(v)"
        case .reg(let r):
            // Shift amount is always byte-sized (cl)
            return fmtReg(r, size: .byte)
        default:
            return fmt(op, .byte)
        }
    }

    private func formatCall(_ op: Operand) -> String {
        switch op {
        case .label(let name):
            return "call \(name)"
        case .mem(let m):
            return "call *\(fmtMem(m))"
        case .reg(let r):
            return "call *\(fmtReg(r, size: .qword))"
        case .imm:
            return "call \(fmt(op, .qword))"
        }
    }

    private func formatTailJmp(_ op: Operand) -> String {
        switch op {
        case .label(let name):
            return "jmp \(name)"
        case .reg(let r):
            return "jmp *\(fmtReg(r, size: .qword))"
        case .mem(let m):
            return "jmp *\(fmtMem(m))"
        case .imm:
            return "jmp \(fmt(op, .qword))"
        }
    }

    // MARK: - SSE helpers

    private func sseSuffix(_ sz: Size) -> String {
        sz == .single ? "ss" : "sd"
    }

    private func xmmMovMnemonic(_ sz: Size) -> String {
        sz == .single ? "movss" : "movsd"
    }

    // MARK: - CVT mnemonic

    private func cvtMnemonic(from: Size, to: Size) -> String {
        let isFromFloat = (from == .single || from == .double_)
        let isToFloat = (to == .single || to == .double_)
        if !isFromFloat && isToFloat {
            return to == .single ? "si2ss" : "si2sd"
        }
        if isFromFloat && !isToFloat {
            return from == .single ? "tss2si" : "tsd2si"
        }
        // float↔float
        switch (from, to) {
        case (.single, .double_): return "ss2sd"
        case (.double_, .single): return "sd2ss"
        default:                  return "si2sd" // shouldn't happen
        }
    }

    /// Format a block label as a local assembly label: `.L<func>.<block>`
    /// Strips the COIL `%` prefix and replaces other invalid characters.
    private func blockLabel(_ block: String, in function: String) -> String {
        return ".L\(function).\(sanitize(block))"
    }

    private func sanitize(_ label: String) -> String {
        var result = ""
        for c in label {
            switch c {
            case "%":               continue          // strip COIL sigil
            case _ where c.isLetter || c.isNumber
                      || c == "_" || c == ".":
                result.append(c)
            default:                result.append("_")
            }
        }
        return result
    }

    // MARK: - Data emission helpers

    /// Check if byte array is printable ASCII followed by a NUL terminator.
    private func isNulTerminatedString(_ data: [UInt8]) -> Bool {
        guard data.last == 0, data.count >= 1 else { return false }
        return data.dropLast().allSatisfy { $0 >= 0x20 && $0 < 0x7F || $0 == 0x09 || $0 == 0x0A }
    }

    private func escapeString(_ s: String) -> String {
        var out = ""
        for c in s {
            switch c {
            case "\"": out += "\\\""
            case "\\": out += "\\\\"
            case "\n": out += "\\n"
            case "\t": out += "\\t"
            default:   out.append(c)
            }
        }
        return out
    }

    private func emitDataBytes(_ data: [UInt8], into out: inout String) {
        var i = 0
        while i < data.count {
            let remaining = data.count - i
            if remaining >= 8 {
                let val = data[i..<i+8].enumerated().reduce(UInt64(0)) {
                    $0 | (UInt64($1.element) << ($1.offset * 8))
                }
                out += "    .quad \(Int64(bitPattern: val))\n"
                i += 8
            } else if remaining >= 4 {
                let val = data[i..<i+4].enumerated().reduce(UInt32(0)) {
                    $0 | (UInt32($1.element) << ($1.offset * 8))
                }
                out += "    .long \(Int32(bitPattern: val))\n"
                i += 4
            } else {
                out += "    .byte \(data[i])\n"
                i += 1
            }
        }
    }
}

// MARK: - Sub-opcode mnemonic helpers

extension AluOp {
    var mnemonic: String {
        switch self {
        case .add: return "add"
        case .sub: return "sub"
        case .and: return "and"
        case .or:  return "or"
        case .xor: return "xor"
        }
    }
}

extension ShiftOp {
    var mnemonic: String {
        switch self {
        case .shl: return "shl"
        case .shr: return "shr"
        case .sar: return "sar"
        }
    }
}

extension GpUnaryOp {
    var mnemonic: String {
        switch self {
        case .neg: return "neg"
        case .not: return "not"
        }
    }
}

extension CmpOp {
    var mnemonic: String {
        switch self {
        case .cmp:  return "cmp"
        case .test: return "test"
        }
    }
}

extension SseOp {
    var mnemonic: String {
        switch self {
        case .add: return "add"
        case .sub: return "sub"
        case .mul: return "mul"
        case .div: return "div"
        }
    }
}

// MARK: - Size helper for movsx/movzx suffix

extension Size {
    /// Integer-only suffix for the target of movsx/movzx (no SSE suffixes).
    var intSuffix: String {
        switch self {
        case .byte:    return "b"
        case .word:    return "w"
        case .dword:   return "l"
        case .qword:   return "q"
        case .single:  return "l"
        case .double_: return "q"
        }
    }
}
