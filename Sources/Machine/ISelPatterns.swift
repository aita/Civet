import Tree

// MARK: - Pattern Definition

/// An instruction selection pattern that matches a DAG subtree and emits x86-64 instructions.
struct ISelPattern {
    let name: String
    let cost: Int
    /// Returns true if this pattern matches the given node.
    /// For multi-node patterns, also checks that consumed children have useCount == 1.
    let match: (DAGNode) -> Bool
    /// The set of child indices consumed by this pattern (not needing independent emission).
    /// For single-node patterns, this is empty.
    let consumedChildren: (DAGNode) -> [Int]
    /// Emit machine instructions for this pattern. Returns the operand holding the result.
    let emit: (DAGNode, inout ISelContext) -> Operand?
}

/// Context passed to pattern emit functions, providing access to emission utilities.
struct ISelContext {
    var mfunc: Function
    var instrs: [Instr] = []
    var varMap: [Int: Reg]
    var stackSlots: [Int: Int32]
    var floatGlobals: [GlobalVar] = []
    var constLabelCounter: Int
    var currentStackOffset: Int32
    var funcName: String = ""

    mutating func freshVirtual() -> Reg {
        return mfunc.freshVirtual()
    }

    /// Emit the instructions for a child node, returning its result operand.
    /// If the child was already emitted (shared node), returns the cached operand.
    mutating func emitChild(_ node: DAGNode) -> Operand? {
        if let cached = node.emittedOperand {
            return cached
        }
        guard let pattern = node.bestPattern else { return nil }
        let result = pattern.emit(node, &self)
        node.emittedOperand = result
        return result
    }
}

// MARK: - Helper predicates

private func isIntConst(_ node: DAGNode, value: Int64) -> Bool {
    if case .intConst(let v) = node.kind { return v == value }
    return false
}

private func intConstValue(_ node: DAGNode) -> Int64? {
    if case .intConst(let v) = node.kind { return v }
    return nil
}

private func isPowerOf2(_ v: Int64) -> Bool {
    return v > 0 && (v & (v - 1)) == 0
}

private func isAggregate(_ type: CType) -> Bool {
    switch type {
    case .array, .structType, .unionType, .vla: return true
    default: return false
    }
}

func isFloat(_ type: CType) -> Bool {
    switch type {
    case .float, .double, .longDouble: return true
    default: return false
    }
}

func isMachineSigned(_ type: CType) -> Bool {
    switch type {
    case .char(let s), .short(let s), .int(let s), .long(let s): return s
    default: return false
    }
}

func sizeOf(_ type: CType) -> Size {
    Size.from(type)
}

func isIntegerSize(_ sz: Size) -> Bool {
    switch sz {
    case .byte, .word, .dword, .qword: return true
    default: return false
    }
}

// MARK: - Emit helpers

/// Ensure an operand is in a register; if not, emit a mov.
private func ensureReg(_ op: Operand, size: Size, ctx: inout ISelContext) -> Reg {
    if case .reg(let r) = op { return r }
    // SSE instructions can't take immediate operands.
    // Materialize float constants from memory instead.
    if (size == .single || size == .double_), case .imm(let v) = op {
        let fop = materializeFloat(Double(v),
            type: size == .single ? .float : .double, ctx: &ctx)
        if case .reg(let r) = fop { return r }
    }
    let tmp = ctx.freshVirtual()
    if size == .single {
        ctx.instrs.append(.xmmMov(.single, src: op, dst: .reg(tmp)))
    } else if size == .double_ {
        ctx.instrs.append(.xmmMov(.double_, src: op, dst: .reg(tmp)))
    } else {
        ctx.instrs.append(.mov(size, src: op, dst: .reg(tmp)))
    }
    return tmp
}

private func ensureRegOrImm(_ op: Operand, size: Size, ctx: inout ISelContext) -> Operand {
    switch op {
    case .reg, .imm: return op
    default: return .reg(ensureReg(op, size: size, ctx: &ctx))
    }
}

/// Get the operand for a leaf node (variable, constant, etc.)
private func leafOperand(_ node: DAGNode, ctx: inout ISelContext) -> Operand {
    switch node.kind {
    case .variable(let id, _):
        if let reg = ctx.varMap[id] {
            return .reg(reg)
        }
        return .imm(0) // shouldn't happen
    case .stackSlot(let offset):
        return .mem(.stack(offset))
    case .intConst(let value):
        return .imm(value)
    case .floatConst(let value):
        return materializeFloat(value, type: node.type, ctx: &ctx)
    case .global(let name, let isFunction):
        if isFunction {
            return .label(name)
        }
        // Arrays, structs, unions: global holds inline data, need address (lea).
        if isAggregate(node.type) {
            let reg = ctx.freshVirtual()
            ctx.instrs.append(.lea(.qword, src: .global(name), dst: reg))
            return .reg(reg)
        }
        return .mem(.global(name))
    case .labelAddr(let name):
        // GNU &&label: load address of a local label into a register.
        let reg = ctx.freshVirtual()
        let asmLabel = ".L\(ctx.funcName).\(name)"
        ctx.instrs.append(.lea(.qword, src: .global(asmLabel), dst: reg))
        return .reg(reg)
    default:
        // Not a leaf — should have been emitted via emitChild
        return ctx.emitChild(node) ?? .imm(0)
    }
}

/// Materialize a float constant as a RIP-relative global.
func materializeFloat(_ value: Double, type: CType, ctx: inout ISelContext) -> Operand {
    let sz = sizeOf(type)
    let label = ".LFC\(ctx.constLabelCounter)"
    ctx.constLabelCounter += 1

    if sz == .single {
        let f = Float(value)
        let bytes = withUnsafeBytes(of: f) { Array($0) }
        ctx.floatGlobals.append(GlobalVar(name: label, size: 4, alignment: 4,
                                          initData: bytes, isStatic: true))
    } else {
        let bytes = withUnsafeBytes(of: value) { Array($0) }
        ctx.floatGlobals.append(GlobalVar(name: label, size: 8, alignment: 8,
                                          initData: bytes, isStatic: true))
    }

    let reg = ctx.freshVirtual()
    let mem = Memory.global(label)
    ctx.instrs.append(sz == .single
        ? .xmmMovMR(.single, src: mem, dst: reg)
        : .xmmMovMR(.double_, src: mem, dst: reg))
    return .reg(reg)
}

/// Get or emit the operand for a DAG node.
private func nodeOperand(_ node: DAGNode, ctx: inout ISelContext) -> Operand {
    if let cached = node.emittedOperand { return cached }
    // For leaf nodes, produce the operand directly
    switch node.kind {
    case .variable, .stackSlot, .intConst, .floatConst, .global:
        let op = leafOperand(node, ctx: &ctx)
        node.emittedOperand = op
        return op
    default:
        // Non-leaf: emit via its pattern
        return ctx.emitChild(node) ?? .imm(0)
    }
}

// MARK: - Pattern Table

/// Build the complete pattern table, ordered so that more specific (lower-cost)
/// patterns are tried first during DP tiling.
func buildPatternTable() -> [ISelPattern] {
    var patterns: [ISelPattern] = []

    // ── Leaf patterns ───────────────────────────────────────────────

    patterns.append(ISelPattern(
        name: "leaf",
        cost: 0,
        match: { node in
            switch node.kind {
            case .variable, .stackSlot, .intConst, .floatConst, .global:
                return true
            default:
                return false
            }
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            return leafOperand(node, ctx: &ctx)
        }
    ))

    // ── Compound patterns (multi-node, lower cost) ──────────────────

    // lea_add_mul: add(a, mul(b, const(2|4|8))) → lea (a, b, scale)
    patterns.append(ISelPattern(
        name: "lea_add_mul",
        cost: 1,
        match: { node in
            guard case .binary(.add) = node.kind,
                  !isFloat(node.type),
                  isIntegerSize(sizeOf(node.type)),
                  sizeOf(node.type) == .dword || sizeOf(node.type) == .qword
            else { return false }
            let rhs = node.operands[1]
            guard case .binary(.mul) = rhs.kind, rhs.useCount == 1 else { return false }
            guard let val = intConstValue(rhs.operands[1]),
                  [2, 4, 8].contains(val) else { return false }
            return true
        },
        consumedChildren: { node in [1] },  // consumes the mul child
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let a = nodeOperand(node.operands[0], ctx: &ctx)
            let mulNode = node.operands[1]
            let b = nodeOperand(mulNode.operands[0], ctx: &ctx)
            let scale = UInt8(intConstValue(mulNode.operands[1])!)
            let aReg = ensureReg(a, size: sz, ctx: &ctx)
            let bReg = ensureReg(b, size: sz, ctx: &ctx)
            let dst = ctx.freshVirtual()
            let mem = Memory(base: aReg, index: bReg, scale: scale)
            ctx.instrs.append(.lea(sz, src: mem, dst: dst))
            return .reg(dst)
        }
    ))

    // lea_add_shl: add(a, shl(b, const(1|2|3))) → lea (a, b, 1<<n)
    patterns.append(ISelPattern(
        name: "lea_add_shl",
        cost: 1,
        match: { node in
            guard case .binary(.add) = node.kind,
                  !isFloat(node.type),
                  sizeOf(node.type) == .dword || sizeOf(node.type) == .qword
            else { return false }
            let rhs = node.operands[1]
            guard case .binary(.shl) = rhs.kind, rhs.useCount == 1 else { return false }
            guard let val = intConstValue(rhs.operands[1]),
                  [1, 2, 3].contains(val) else { return false }
            return true
        },
        consumedChildren: { node in [1] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let a = nodeOperand(node.operands[0], ctx: &ctx)
            let shlNode = node.operands[1]
            let b = nodeOperand(shlNode.operands[0], ctx: &ctx)
            let shift = intConstValue(shlNode.operands[1])!
            let scale = UInt8(1 << shift)
            let aReg = ensureReg(a, size: sz, ctx: &ctx)
            let bReg = ensureReg(b, size: sz, ctx: &ctx)
            let dst = ctx.freshVirtual()
            let mem = Memory(base: aReg, index: bReg, scale: scale)
            ctx.instrs.append(.lea(sz, src: mem, dst: dst))
            return .reg(dst)
        }
    ))

    // lea_mul3: mul(x, const(3)) → lea (x, x, 2)
    patterns.append(ISelPattern(
        name: "lea_mul3",
        cost: 1,
        match: { node in
            guard case .binary(.mul) = node.kind,
                  !isFloat(node.type),
                  sizeOf(node.type) == .dword || sizeOf(node.type) == .qword
            else { return false }
            return isIntConst(node.operands[1], value: 3)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let xReg = ensureReg(x, size: sz, ctx: &ctx)
            let dst = ctx.freshVirtual()
            let mem = Memory(base: xReg, index: xReg, scale: 2)
            ctx.instrs.append(.lea(sz, src: mem, dst: dst))
            return .reg(dst)
        }
    ))

    // lea_mul5: mul(x, const(5)) → lea (x, x, 4)
    patterns.append(ISelPattern(
        name: "lea_mul5",
        cost: 1,
        match: { node in
            guard case .binary(.mul) = node.kind,
                  !isFloat(node.type),
                  sizeOf(node.type) == .dword || sizeOf(node.type) == .qword
            else { return false }
            return isIntConst(node.operands[1], value: 5)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let xReg = ensureReg(x, size: sz, ctx: &ctx)
            let dst = ctx.freshVirtual()
            let mem = Memory(base: xReg, index: xReg, scale: 4)
            ctx.instrs.append(.lea(sz, src: mem, dst: dst))
            return .reg(dst)
        }
    ))

    // lea_mul9: mul(x, const(9)) → lea (x, x, 8)
    patterns.append(ISelPattern(
        name: "lea_mul9",
        cost: 1,
        match: { node in
            guard case .binary(.mul) = node.kind,
                  !isFloat(node.type),
                  sizeOf(node.type) == .dword || sizeOf(node.type) == .qword
            else { return false }
            return isIntConst(node.operands[1], value: 9)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let xReg = ensureReg(x, size: sz, ctx: &ctx)
            let dst = ctx.freshVirtual()
            let mem = Memory(base: xReg, index: xReg, scale: 8)
            ctx.instrs.append(.lea(sz, src: mem, dst: dst))
            return .reg(dst)
        }
    ))

    // ── Multiply special cases ──────────────────────────────────────

    // mul_zero: mul(_, const(0)) → xor d, d
    patterns.append(ISelPattern(
        name: "mul_zero",
        cost: 1,
        match: { node in
            guard case .binary(.mul) = node.kind, !isFloat(node.type) else { return false }
            return isIntConst(node.operands[1], value: 0)
                || isIntConst(node.operands[0], value: 0)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.aluRmiR(.xor, sz, src: .reg(dst), dst: dst))
            return .reg(dst)
        }
    ))

    // mul_one: mul(x, const(1)) → x
    patterns.append(ISelPattern(
        name: "mul_one",
        cost: 1,
        match: { node in
            guard case .binary(.mul) = node.kind, !isFloat(node.type) else { return false }
            return isIntConst(node.operands[1], value: 1)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: x, dst: .reg(dst)))
            return .reg(dst)
        }
    ))

    // mul_pow2: mul(x, const(2^n)) → shl $n
    patterns.append(ISelPattern(
        name: "mul_pow2",
        cost: 2,
        match: { node in
            guard case .binary(.mul) = node.kind, !isFloat(node.type) else { return false }
            guard let val = intConstValue(node.operands[1]) else { return false }
            return val > 1 && isPowerOf2(val)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let val = intConstValue(node.operands[1])!
            let shift = val.trailingZeroBitCount
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: x, dst: .reg(dst)))
            ctx.instrs.append(.shiftR(.shl, sz, src: .imm(Int64(shift)), dst: dst))
            return .reg(dst)
        }
    ))

    // ── Division special cases ──────────────────────────────────────

    // div_one: div(x, const(1)) → x
    patterns.append(ISelPattern(
        name: "div_one",
        cost: 1,
        match: { node in
            guard case .binary(.div) = node.kind, !isFloat(node.type) else { return false }
            return isIntConst(node.operands[1], value: 1)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: x, dst: .reg(dst)))
            return .reg(dst)
        }
    ))

    // udiv_pow2: unsigned div(x, const(2^n)) → shr $n
    patterns.append(ISelPattern(
        name: "udiv_pow2",
        cost: 2,
        match: { node in
            guard case .binary(.div) = node.kind, !isFloat(node.type) else { return false }
            guard !isMachineSigned(node.operands[0].type) else { return false }
            guard let val = intConstValue(node.operands[1]) else { return false }
            return val > 1 && isPowerOf2(val)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let val = intConstValue(node.operands[1])!
            let shift = val.trailingZeroBitCount
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: x, dst: .reg(dst)))
            ctx.instrs.append(.shiftR(.shr, sz, src: .imm(Int64(shift)), dst: dst))
            return .reg(dst)
        }
    ))

    // sdiv_pow2: signed div(x, const(2^n)) → adjustment + sar $n
    patterns.append(ISelPattern(
        name: "sdiv_pow2",
        cost: 5,
        match: { node in
            guard case .binary(.div) = node.kind, !isFloat(node.type) else { return false }
            guard isMachineSigned(node.operands[0].type) else { return false }
            guard let val = intConstValue(node.operands[1]) else { return false }
            return val > 1 && isPowerOf2(val)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let val = intConstValue(node.operands[1])!
            let shift = val.trailingZeroBitCount
            let bitwidth: Int64
            switch sz {
            case .byte: bitwidth = 8
            case .word: bitwidth = 16
            case .dword: bitwidth = 32
            case .qword: bitwidth = 64
            default: bitwidth = 64
            }
            let dst = ctx.freshVirtual()
            let tmp = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: x, dst: .reg(dst)))
            ctx.instrs.append(.movRR(sz, src: dst, dst: tmp))
            ctx.instrs.append(.shiftR(.sar, sz, src: .imm(bitwidth - 1), dst: tmp))
            ctx.instrs.append(.aluRmiR(.and, sz, src: .imm(val - 1), dst: tmp))
            ctx.instrs.append(.aluRmiR(.add, sz, src: .reg(tmp), dst: dst))
            ctx.instrs.append(.shiftR(.sar, sz, src: .imm(Int64(shift)), dst: dst))
            return .reg(dst)
        }
    ))

    // udiv_magic: unsigned div(x, const(d)) → mulhi + shift (Hacker's Delight)
    patterns.append(ISelPattern(
        name: "udiv_magic",
        cost: 6,
        match: { node in
            guard case .binary(.div) = node.kind, !isFloat(node.type) else { return false }
            guard !isMachineSigned(node.operands[0].type) else { return false }
            guard let val = intConstValue(node.operands[1]) else { return false }
            let sz = sizeOf(node.type)
            // Only 32-bit supported; 64-bit magic division needs 128-bit multiply.
            guard sz == .dword else { return false }
            return val > 1 && !isPowerOf2(val)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let d = intConstValue(node.operands[1])!

            // 32-bit unsigned magic: x / d = (x * M) >> (32 + s)
            // Compute using 64-bit multiply.
            let (magic, shift) = unsignedMagic32(UInt32(d))
            let src = ctx.freshVirtual()
            let tmp = ctx.freshVirtual()
            let dst = ctx.freshVirtual()
            // Zero-extend x to 64-bit
            ctx.instrs.append(.movzxRmR(from: .dword, to: .qword, src: x, dst: src))
            // Multiply by magic constant (64-bit)
            ctx.instrs.append(.movIR(.qword, imm: Int64(magic), dst: tmp))
            ctx.instrs.append(.imul(.qword, src: .reg(src), dst: tmp))
            // Shift right
            ctx.instrs.append(.shiftR(.shr, .qword, src: .imm(Int64(shift)), dst: tmp))
            // Truncate to 32-bit
            ctx.instrs.append(.movRR(.dword, src: tmp, dst: dst))
            return .reg(dst)
        }
    ))

    // sdiv_magic: signed div(x, const(d)) → mulhi + adjustments (Hacker's Delight)
    patterns.append(ISelPattern(
        name: "sdiv_magic",
        cost: 6,
        match: { node in
            guard case .binary(.div) = node.kind, !isFloat(node.type) else { return false }
            guard isMachineSigned(node.operands[0].type) else { return false }
            guard let val = intConstValue(node.operands[1]) else { return false }
            let sz = sizeOf(node.type)
            guard sz == .dword else { return false }
            return val > 1 && !isPowerOf2(val)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let d = intConstValue(node.operands[1])!

            // 32-bit signed magic: x / d = mulhi(x, M) + adjustments >> s
            let (magic, shift) = signedMagic32(Int32(d))
            let src = ctx.freshVirtual()
            let tmp = ctx.freshVirtual()
            let dst = ctx.freshVirtual()

            // Sign-extend x to 64-bit
            ctx.instrs.append(.movsxRmR(from: .dword, to: .qword, src: x, dst: src))
            // Multiply by magic constant (64-bit), then take upper 32 bits
            ctx.instrs.append(.movIR(.qword, imm: Int64(magic), dst: tmp))
            ctx.instrs.append(.imul(.qword, src: .reg(src), dst: tmp))
            // Shift right by 32 to get the mulhi result
            ctx.instrs.append(.shiftR(.sar, .qword, src: .imm(32), dst: tmp))
            // Additional shift
            if shift > 0 {
                ctx.instrs.append(.shiftR(.sar, .qword, src: .imm(Int64(shift)), dst: tmp))
            }
            // Add sign bit correction: result += (result >> 31)
            let signFix = ctx.freshVirtual()
            ctx.instrs.append(.movRR(.dword, src: tmp, dst: dst))
            ctx.instrs.append(.movRR(.dword, src: dst, dst: signFix))
            ctx.instrs.append(.shiftR(.shr, .dword, src: .imm(31), dst: signFix))
            ctx.instrs.append(.aluRmiR(.add, .dword, src: .reg(signFix), dst: dst))
            return .reg(dst)
        }
    ))

    // umod_pow2: unsigned mod(x, const(2^n)) → and $(2^n - 1)
    patterns.append(ISelPattern(
        name: "umod_pow2",
        cost: 2,
        match: { node in
            guard case .binary(.mod) = node.kind, !isFloat(node.type) else { return false }
            guard !isMachineSigned(node.operands[0].type) else { return false }
            guard let val = intConstValue(node.operands[1]) else { return false }
            return val > 0 && isPowerOf2(val)
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let x = nodeOperand(node.operands[0], ctx: &ctx)
            let val = intConstValue(node.operands[1])!
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: x, dst: .reg(dst)))
            ctx.instrs.append(.aluRmiR(.and, sz, src: .imm(val - 1), dst: dst))
            return .reg(dst)
        }
    ))

    // ── Generic integer binary ops ──────────────────────────────────

    // add
    patterns.append(ISelPattern(
        name: "add",
        cost: 2,
        match: { node in
            guard case .binary(.add) = node.kind, !isFloat(node.type) else { return false }
            return true
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let l = nodeOperand(node.operands[0], ctx: &ctx)
            let r = nodeOperand(node.operands[1], ctx: &ctx)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: l, dst: .reg(dst)))
            ctx.instrs.append(.aluRmiR(.add, sz, src: r, dst: dst))
            return .reg(dst)
        }
    ))

    // sub
    patterns.append(ISelPattern(
        name: "sub",
        cost: 2,
        match: { node in
            guard case .binary(.sub) = node.kind, !isFloat(node.type) else { return false }
            return true
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let l = nodeOperand(node.operands[0], ctx: &ctx)
            let r = nodeOperand(node.operands[1], ctx: &ctx)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: l, dst: .reg(dst)))
            ctx.instrs.append(.aluRmiR(.sub, sz, src: r, dst: dst))
            return .reg(dst)
        }
    ))

    // mul (general)
    patterns.append(ISelPattern(
        name: "mul",
        cost: 4,
        match: { node in
            guard case .binary(.mul) = node.kind, !isFloat(node.type) else { return false }
            return true
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let l = nodeOperand(node.operands[0], ctx: &ctx)
            let r = nodeOperand(node.operands[1], ctx: &ctx)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: l, dst: .reg(dst)))
            ctx.instrs.append(.imul(sz, src: r, dst: dst))
            return .reg(dst)
        }
    ))

    // div (general) — emits pseudoDiv, expanded by ConstraintResolver
    patterns.append(ISelPattern(
        name: "div",
        cost: 20,
        match: { node in
            guard case .binary(.div) = node.kind, !isFloat(node.type) else { return false }
            return true
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let l = nodeOperand(node.operands[0], ctx: &ctx)
            let r = nodeOperand(node.operands[1], ctx: &ctx)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.idivRemSeq(sz, dst: .reg(dst), dividend: l, divisor: r,
                                         signed: isMachineSigned(node.operands[0].type), isDiv: true))
            return .reg(dst)
        }
    ))

    // mod (general) — emits pseudoMod, expanded by ConstraintResolver
    patterns.append(ISelPattern(
        name: "mod",
        cost: 20,
        match: { node in
            guard case .binary(.mod) = node.kind, !isFloat(node.type) else { return false }
            return true
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let l = nodeOperand(node.operands[0], ctx: &ctx)
            let r = nodeOperand(node.operands[1], ctx: &ctx)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.idivRemSeq(sz, dst: .reg(dst), dividend: l, divisor: r,
                                         signed: isMachineSigned(node.operands[0].type), isDiv: false))
            return .reg(dst)
        }
    ))

    // bitwise: and, or, xor
    for (op, instrName): (BinaryOp, String) in [(.bitAnd, "and"), (.bitOr, "or"), (.bitXor, "xor")] {
        let capturedOp = op
        patterns.append(ISelPattern(
            name: instrName,
            cost: 2,
            match: { node in
                guard case .binary(let o) = node.kind, o == capturedOp, !isFloat(node.type)
                else { return false }
                return true
            },
            consumedChildren: { _ in [] },
            emit: { node, ctx in
                let sz = sizeOf(node.type)
                let l = nodeOperand(node.operands[0], ctx: &ctx)
                let r = nodeOperand(node.operands[1], ctx: &ctx)
                let dst = ctx.freshVirtual()
                ctx.instrs.append(.mov(sz, src: l, dst: .reg(dst)))
                switch capturedOp {
                case .bitAnd: ctx.instrs.append(.aluRmiR(.and, sz, src: r, dst: dst))
                case .bitOr:  ctx.instrs.append(.aluRmiR(.or, sz, src: r, dst: dst))
                case .bitXor: ctx.instrs.append(.aluRmiR(.xor, sz, src: r, dst: dst))
                default: break
                }
                return .reg(dst)
            }
        ))
    }

    // shifts: shl, shr
    patterns.append(ISelPattern(
        name: "shl",
        cost: 2,
        match: { node in
            guard case .binary(.shl) = node.kind, !isFloat(node.type) else { return false }
            return true
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            return emitShift(.shl, node: node, ctx: &ctx)
        }
    ))

    patterns.append(ISelPattern(
        name: "shr",
        cost: 2,
        match: { node in
            guard case .binary(.shr) = node.kind, !isFloat(node.type) else { return false }
            return true
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            return emitShift(isMachineSigned(node.operands[0].type) ? .sar : .shr, node: node, ctx: &ctx)
        }
    ))

    // comparisons: eq, ne, lt, le
    for (op, cc): (BinaryOp, CondCode) in [(.eq, .e), (.ne, .ne), (.lt, .l), (.le, .le)] {
        let capturedOp = op
        let capturedCC = cc
        patterns.append(ISelPattern(
            name: "cmp_\(capturedOp)",
            cost: 3,
            match: { node in
                guard case .binary(let o) = node.kind, o == capturedOp else { return false }
                return true
            },
            consumedChildren: { _ in [] },
            emit: { node, ctx in
                let operandType = node.operands[0].type
                let sz = sizeOf(operandType)
                let l = nodeOperand(node.operands[0], ctx: &ctx)
                let r = nodeOperand(node.operands[1], ctx: &ctx)
                let dst = ctx.freshVirtual()
                if isFloat(operandType) {
                    let lReg = ensureReg(l, size: sz, ctx: &ctx)
                    let rReg = ensureReg(r, size: sz, ctx: &ctx)
                    ctx.instrs.append(sz == .single
                        ? .xmmCmp(.single, src: .reg(rReg), dst: lReg)
                        : .xmmCmp(.double_, src: .reg(rReg), dst: lReg))
                    let floatCC: CondCode = (capturedOp == .lt) ? .b
                        : (capturedOp == .le) ? .be : capturedCC
                    ctx.instrs.append(.setcc(floatCC, dst))
                    // NaN handling: ucomisd sets PF=1 for unordered (NaN).
                    // C semantics: NaN comparisons return false (eq/lt/le) or
                    // true (ne). Adjust by checking parity flag.
                    if capturedOp == .ne {
                        // ne: unordered counts as not-equal → OR with setp
                        let p = ctx.freshVirtual()
                        ctx.instrs.append(.setcc(.p, p))
                        ctx.instrs.append(.aluRmiR(.or, .byte, src: .reg(p), dst: dst))
                    } else {
                        // eq/lt/le: must also be ordered (PF=0) → AND with setnp
                        let np = ctx.freshVirtual()
                        ctx.instrs.append(.setcc(.np, np))
                        ctx.instrs.append(.aluRmiR(.and, .byte, src: .reg(np), dst: dst))
                    }
                } else {
                    let lReg = ensureReg(l, size: sz, ctx: &ctx)
                    ctx.instrs.append(.cmpRmiR(.cmp, sz, src: r, dst: lReg))
                    // Use unsigned condition codes (b/be) for unsigned or pointer types
                    let intCC: CondCode
                    if !isMachineSigned(operandType) && (capturedOp == .lt || capturedOp == .le) {
                        intCC = (capturedOp == .lt) ? .b : .be
                    } else {
                        intCC = capturedCC
                    }
                    ctx.instrs.append(.setcc(intCC, dst))
                }
                ctx.instrs.append(.movzxRmR(from: .byte, to: sizeOf(node.type),
                                         src: .reg(dst), dst: dst))
                return .reg(dst)
            }
        ))
    }

    // ── Float binary ops ────────────────────────────────────────────

    for (op, name): (BinaryOp, String) in [(.add, "fadd"), (.sub, "fsub"),
                                             (.mul, "fmul"), (.div, "fdiv")] {
        let capturedOp = op
        patterns.append(ISelPattern(
            name: name,
            cost: 4,
            match: { node in
                guard case .binary(let o) = node.kind, o == capturedOp,
                      isFloat(node.type) else { return false }
                return true
            },
            consumedChildren: { _ in [] },
            emit: { node, ctx in
                let sz = sizeOf(node.type)
                let isSingle = sz == .single
                let l = nodeOperand(node.operands[0], ctx: &ctx)
                let r = nodeOperand(node.operands[1], ctx: &ctx)
                let dst = ctx.freshVirtual()
                ctx.instrs.append(isSingle ? .xmmMov(.single, src: l, dst: .reg(dst))
                                           : .xmmMov(.double_, src: l, dst: .reg(dst)))
                switch capturedOp {
                case .add: ctx.instrs.append(isSingle ? .xmmRmR(.add, .single, src: r, dst: dst)
                                                      : .xmmRmR(.add, .double_, src: r, dst: dst))
                case .sub: ctx.instrs.append(isSingle ? .xmmRmR(.sub, .single, src: r, dst: dst)
                                                      : .xmmRmR(.sub, .double_, src: r, dst: dst))
                case .mul: ctx.instrs.append(isSingle ? .xmmRmR(.mul, .single, src: r, dst: dst)
                                                      : .xmmRmR(.mul, .double_, src: r, dst: dst))
                case .div: ctx.instrs.append(isSingle ? .xmmRmR(.div, .single, src: r, dst: dst)
                                                      : .xmmRmR(.div, .double_, src: r, dst: dst))
                default: break
                }
                return .reg(dst)
            }
        ))
    }

    // ── Unary ops ───────────────────────────────────────────────────

    patterns.append(ISelPattern(
        name: "neg",
        cost: 2,
        match: { node in
            guard case .unary(.neg) = node.kind else { return false }
            return true
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let src = nodeOperand(node.operands[0], ctx: &ctx)
            let dst = ctx.freshVirtual()
            if isFloat(node.type) {
                // Float negation: 0.0 - x
                let zeroOp = materializeFloat(0.0,
                    type: sz == .single ? .float : .double, ctx: &ctx)
                let zeroReg = ensureReg(zeroOp, size: sz, ctx: &ctx)
                if sz == .single {
                    ctx.instrs.append(.xmmMovRR(.single, src: zeroReg, dst: dst))
                    ctx.instrs.append(.xmmRmR(.sub, .single, src: src, dst: dst))
                } else {
                    ctx.instrs.append(.xmmMovRR(.double_, src: zeroReg, dst: dst))
                    ctx.instrs.append(.xmmRmR(.sub, .double_, src: src, dst: dst))
                }
            } else {
                ctx.instrs.append(.mov(sz, src: src, dst: .reg(dst)))
                ctx.instrs.append(.unaryRm(.neg, sz, dst))
            }
            return .reg(dst)
        }
    ))

    patterns.append(ISelPattern(
        name: "bitNot",
        cost: 2,
        match: { node in
            guard case .unary(.bitNot) = node.kind else { return false }
            return true
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let src = nodeOperand(node.operands[0], ctx: &ctx)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.mov(sz, src: src, dst: .reg(dst)))
            ctx.instrs.append(.unaryRm(.not, sz, dst))
            return .reg(dst)
        }
    ))

    // ── Memory ops ──────────────────────────────────────────────────

    patterns.append(ISelPattern(
        name: "load",
        cost: 1,
        match: { node in
            if case .load = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let addr = nodeOperand(node.operands[0], ctx: &ctx)
            let dst = ctx.freshVirtual()
            if case .reg(let base) = addr {
                let mem = Memory(base: base)
                if isFloat(node.type) {
                    ctx.instrs.append(sz == .single
                        ? .xmmMovMR(.single, src: mem, dst: dst)
                        : .xmmMovMR(.double_, src: mem, dst: dst))
                } else {
                    ctx.instrs.append(.movMR(sz, src: mem, dst: dst))
                }
            } else if case .mem(let mem) = addr {
                if mem.isStack {
                    // Stack slot: the mem operand IS the address, load directly.
                    if isFloat(node.type) {
                        ctx.instrs.append(sz == .single
                            ? .xmmMovMR(.single, src: mem, dst: dst)
                            : .xmmMovMR(.double_, src: mem, dst: dst))
                    } else {
                        ctx.instrs.append(.movMR(sz, src: mem, dst: dst))
                    }
                } else {
                    // Global/other: load the pointer, then dereference.
                    let tmp = ctx.freshVirtual()
                    ctx.instrs.append(.movMR(.qword, src: mem, dst: tmp))
                    let derefMem = Memory(base: tmp)
                    if isFloat(node.type) {
                        ctx.instrs.append(sz == .single
                            ? .xmmMovMR(.single, src: derefMem, dst: dst)
                            : .xmmMovMR(.double_, src: derefMem, dst: dst))
                    } else {
                        ctx.instrs.append(.movMR(sz, src: derefMem, dst: dst))
                    }
                }
            }
            return .reg(dst)
        }
    ))

    patterns.append(ISelPattern(
        name: "store",
        cost: 1,
        match: { node in
            if case .store = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let valType = node.operands[1].type
            let sz = sizeOf(valType)
            let addr = nodeOperand(node.operands[0], ctx: &ctx)
            let val = nodeOperand(node.operands[1], ctx: &ctx)
            if case .reg(let base) = addr {
                let mem = Memory(base: base)
                if isFloat(valType) {
                    let srcReg = ensureReg(val, size: sz, ctx: &ctx)
                    ctx.instrs.append(sz == .single
                        ? .xmmMovRM(.single, src: srcReg, dst: mem)
                        : .xmmMovRM(.double_, src: srcReg, dst: mem))
                } else {
                    let src = ensureRegOrImm(val, size: sz, ctx: &ctx)
                    ctx.instrs.append(.mov(sz, src: src, dst: .mem(mem)))
                }
            } else if case .mem(let mem) = addr {
                if mem.isStack {
                    // Stack slot: write directly to the memory operand.
                    if isFloat(valType) {
                        let srcReg = ensureReg(val, size: sz, ctx: &ctx)
                        ctx.instrs.append(sz == .single
                            ? .xmmMovRM(.single, src: srcReg, dst: mem)
                            : .xmmMovRM(.double_, src: srcReg, dst: mem))
                    } else {
                        let src = ensureRegOrImm(val, size: sz, ctx: &ctx)
                        ctx.instrs.append(.mov(sz, src: src, dst: .mem(mem)))
                    }
                } else if mem.symbol != nil && mem.base == nil {
                    // Global variable (RIP-relative): store directly.
                    if isFloat(valType) {
                        let srcReg = ensureReg(val, size: sz, ctx: &ctx)
                        ctx.instrs.append(sz == .single
                            ? .xmmMovRM(.single, src: srcReg, dst: mem)
                            : .xmmMovRM(.double_, src: srcReg, dst: mem))
                    } else {
                        let src = ensureRegOrImm(val, size: sz, ctx: &ctx)
                        ctx.instrs.append(.mov(sz, src: src, dst: .mem(mem)))
                    }
                } else {
                    // Other: load the pointer, then write through it.
                    let tmp = ctx.freshVirtual()
                    ctx.instrs.append(.movMR(.qword, src: mem, dst: tmp))
                    let derefMem = Memory(base: tmp)
                    let src = ensureRegOrImm(val, size: sz, ctx: &ctx)
                    ctx.instrs.append(.mov(sz, src: src, dst: .mem(derefMem)))
                }
            }
            return nil
        }
    ))

    patterns.append(ISelPattern(
        name: "addressOf",
        cost: 1,
        match: { node in
            if case .addressOf = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let src = node.operands[0]
            let dst = ctx.freshVirtual()
            switch src.kind {
            case .stackSlot(let offset):
                ctx.instrs.append(.lea(.qword, src: .stack(offset), dst: dst))
            case .variable(let id, _):
                if let reg = ctx.varMap[id] {
                    // Taking address of scalar: spill to stack
                    let sz = sizeOf(src.type)
                    let slotSize = Int32(max(sz.rawValue, 8))
                    ctx.currentStackOffset = alignUp(ctx.currentStackOffset + slotSize, to: 8)
                    let slot = ctx.currentStackOffset
                    ctx.instrs.append(.movRM(sz, src: reg, dst: .stack(slot)))
                    ctx.instrs.append(.lea(.qword, src: .stack(slot), dst: dst))
                } else if let offset = ctx.stackSlots[id] {
                    ctx.instrs.append(.lea(.qword, src: .stack(offset), dst: dst))
                }
            case .global(let name, _):
                // &globalVar → lea name(%rip), dst
                ctx.instrs.append(.lea(.qword, src: .global(name), dst: dst))
            default:
                break
            }
            return .reg(dst)
        }
    ))

    patterns.append(ISelPattern(
        name: "member",
        cost: 1,
        match: { node in
            if case .member = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            guard case .member(_, let precomputedOffset) = node.kind else { return nil }
            let base = nodeOperand(node.operands[0], ctx: &ctx)
            let mOffset = precomputedOffset
            let dst = ctx.freshVirtual()
            // For struct/union base on stack or in memory: use lea to get address,
            // don't load the value (which would read struct data, not address).
            if case .mem(let mem) = base {
                // Compute address = base_address + member_offset
                let newMem = Memory(base: mem.base, index: mem.index, scale: mem.scale,
                                    displacement: mem.displacement + mOffset, symbol: mem.symbol)
                ctx.instrs.append(.lea(.qword, src: newMem, dst: dst))
            } else {
                // Base is a register (pointer to struct): add member offset
                let baseReg = ensureReg(base, size: .qword, ctx: &ctx)
                ctx.instrs.append(.lea(.qword,
                                       src: Memory(base: baseReg, displacement: mOffset),
                                       dst: dst))
            }
            return .reg(dst)
        }
    ))

    // ── Cast ────────────────────────────────────────────────────────

    patterns.append(ISelPattern(
        name: "cast",
        cost: 1,
        match: { node in
            if case .cast = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            guard case .cast(let fromType, let toType) = node.kind else { return nil }
            let fromSz = sizeOf(fromType)
            let toSz = sizeOf(toType)
            let src = nodeOperand(node.operands[0], ctx: &ctx)
            let dst = ctx.freshVirtual()
            let fromFloat = isFloat(fromType)
            let toFloat = isFloat(toType)

            if case .bool = toType {
                // Cast to _Bool: normalize to 0 or 1.
                if fromFloat {
                    // float/double → _Bool: xorpd zero, ucomisd, setne
                    let sReg = ensureReg(src, size: fromSz, ctx: &ctx)
                    let zero = ctx.freshVirtual()
                    let floatType: CType = fromSz == .single ? .float : .double
                    let zeroImm = materializeFloat(0.0, type: floatType, ctx: &ctx)
                    ctx.instrs.append(fromSz == .single
                        ? .xmmCmp(.single, src: zeroImm, dst: sReg)
                        : .xmmCmp(.double_, src: zeroImm, dst: sReg))
                    ctx.instrs.append(.setcc(.ne, dst))
                    _ = zero  // unused, zero materialized via helper
                } else if case .imm(let val) = src {
                    ctx.instrs.append(.movIR(.byte, imm: val != 0 ? 1 : 0, dst: dst))
                } else {
                    let sReg = ensureReg(src, size: fromSz, ctx: &ctx)
                    ctx.instrs.append(.cmpRmiR(.test, fromSz, src: .reg(sReg), dst: sReg))
                    ctx.instrs.append(.setcc(.ne, dst))
                }
            } else if fromFloat && toFloat {
                if fromSz == toSz {
                    // Same float type — just move.
                    ctx.instrs.append(fromSz == .single
                        ? .xmmMov(.single, src: src, dst: .reg(dst))
                        : .xmmMov(.double_, src: src, dst: .reg(dst)))
                } else {
                    let sReg = ensureReg(src, size: fromSz, ctx: &ctx)
                    ctx.instrs.append(.cvt(from: fromSz, to: toSz, src: .reg(sReg), dst: dst))
                }
            } else if !fromFloat && toFloat {
                // cvtsi2ss/sd requires dword or qword source.
                var sReg = ensureReg(src, size: fromSz, ctx: &ctx)
                var actualFromSz = fromSz
                if fromSz == .byte || fromSz == .word {
                    let wide = ctx.freshVirtual()
                    if isMachineSigned(fromType) {
                        ctx.instrs.append(.movsxRmR(from: fromSz, to: .dword, src: .reg(sReg), dst: wide))
                    } else {
                        ctx.instrs.append(.movzxRmR(from: fromSz, to: .dword, src: .reg(sReg), dst: wide))
                    }
                    sReg = wide
                    actualFromSz = .dword
                }
                if !isMachineSigned(fromType) && actualFromSz == .dword {
                    // unsigned 32-bit → float: zero-extend to qword so
                    // cvtsi2sd sees a positive signed value.
                    let wide = ctx.freshVirtual()
                    ctx.instrs.append(.movRR(.dword, src: sReg, dst: wide))
                    sReg = wide
                    actualFromSz = .qword
                }
                if !isMachineSigned(fromType) && actualFromSz == .qword {
                    // unsigned long → float/double: branchless via high/low split.
                    // result = (double)(src >> 32) * 4294967296.0 + (double)(src & 0xFFFFFFFF)
                    let hi = ctx.freshVirtual()
                    let lo = ctx.freshVirtual()
                    ctx.instrs.append(.movRR(.qword, src: sReg, dst: hi))
                    ctx.instrs.append(.shiftR(.shr, .qword, src: .imm(32), dst: hi))
                    ctx.instrs.append(.movRR(.dword, src: sReg, dst: lo))
                    // Convert both halves (both ≤ 0xFFFFFFFF, fit in signed qword).
                    let hiF = ctx.freshVirtual()
                    let loF = ctx.freshVirtual()
                    ctx.instrs.append(.cvt(from: .qword, to: toSz, src: .reg(hi), dst: hiF))
                    ctx.instrs.append(.cvt(from: .qword, to: toSz, src: .reg(lo), dst: loF))
                    // Multiply high part by 2^32.
                    let scale = materializeFloat(4294967296.0,
                                                 type: toSz == .single ? .float : .double,
                                                 ctx: &ctx)
                    if toSz == .single {
                        ctx.instrs.append(.xmmRmR(.mul, .single, src: scale, dst: hiF))
                        ctx.instrs.append(.xmmRmR(.add, .single, src: .reg(loF), dst: hiF))
                        ctx.instrs.append(.xmmMovRR(.single, src: hiF, dst: dst))
                    } else {
                        ctx.instrs.append(.xmmRmR(.mul, .double_, src: scale, dst: hiF))
                        ctx.instrs.append(.xmmRmR(.add, .double_, src: .reg(loF), dst: hiF))
                        ctx.instrs.append(.xmmMovRR(.double_, src: hiF, dst: dst))
                    }
                } else {
                    ctx.instrs.append(.cvt(from: actualFromSz, to: toSz, src: .reg(sReg), dst: dst))
                }
            } else if fromFloat && !toFloat {
                // cvtts{s,d}2si only targets dword or qword registers.
                let sReg = ensureReg(src, size: fromSz, ctx: &ctx)
                let cvtToSz: Size = (toSz == .byte || toSz == .word) ? .dword : toSz
                ctx.instrs.append(.cvt(from: fromSz, to: cvtToSz, src: .reg(sReg), dst: dst))
                // If target was byte/word, the dword result is already truncated in the register.
            } else {
                // int → int
                if toSz.rawValue > fromSz.rawValue {
                    if case .imm(let val) = src {
                        // Immediate: sign/zero extend at compile time.
                        let extended: Int64
                        if isMachineSigned(fromType) {
                            switch fromSz {
                            case .byte:  extended = Int64(Int8(truncatingIfNeeded: val))
                            case .word:  extended = Int64(Int16(truncatingIfNeeded: val))
                            case .dword: extended = Int64(Int32(truncatingIfNeeded: val))
                            default:     extended = val
                            }
                        } else {
                            switch fromSz {
                            case .byte:  extended = Int64(UInt8(truncatingIfNeeded: val))
                            case .word:  extended = Int64(UInt16(truncatingIfNeeded: val))
                            case .dword: extended = Int64(UInt32(truncatingIfNeeded: val))
                            default:     extended = val
                            }
                        }
                        ctx.instrs.append(.movIR(toSz, imm: extended, dst: dst))
                    } else {
                        let sReg = ensureReg(src, size: fromSz, ctx: &ctx)
                        if isMachineSigned(fromType) {
                            ctx.instrs.append(.movsxRmR(from: fromSz, to: toSz, src: .reg(sReg), dst: dst))
                        } else {
                            ctx.instrs.append(.movzxRmR(from: fromSz, to: toSz, src: .reg(sReg), dst: dst))
                        }
                    }
                } else {
                    ctx.instrs.append(.mov(toSz, src: src, dst: .reg(dst)))
                }
            }
            return .reg(dst)
        }
    ))

    // ── Call ─────────────────────────────────────────────────────────

    patterns.append(ISelPattern(
        name: "call",
        cost: 10,
        match: { node in
            if case .call = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            guard case .call(let argCount, let argTypes) = node.kind else { return nil }
            var intIdx = 0
            var sseIdx = 0
            var stackArgs: [(Operand, Size)] = []

            // Collect register-bound args into a parallel copy.
            var regCopies: [(src: Operand, dst: Operand, sz: Size)] = []

            // Check if return type is a struct needing a return buffer (MEMORY class).
            let retStructSlot: Int32?
            if isAggregate(node.type) {
                let retABI = classifyStruct(node.type)
                if retABI.isMemory {
                    // Allocate stack space for return buffer, pass address in first int arg.
                    let retSize = Int32(typeSize(node.type))
                    let retAlign = Int32(max(typeAlign(node.type), 8))
                    ctx.currentStackOffset = alignUp(ctx.currentStackOffset + retSize, to: retAlign)
                    retStructSlot = ctx.currentStackOffset
                    let bufReg = ctx.freshVirtual()
                    ctx.instrs.append(.lea(.qword, src: .stack(retStructSlot!), dst: bufReg))
                    if intIdx < PhysReg.intArgRegs.count {
                        regCopies.append((src: .reg(bufReg), dst: .reg(.physical(PhysReg.intArgRegs[intIdx])), sz: .qword))
                        intIdx += 1
                    }
                } else {
                    // Small struct returned in registers; allocate temp stack slot for storing result.
                    let retSize = Int32(max(typeSize(node.type), 16)) // ensure room for 2 qwords
                    ctx.currentStackOffset = alignUp(ctx.currentStackOffset + retSize, to: 8)
                    retStructSlot = ctx.currentStackOffset
                }
            } else {
                retStructSlot = nil
            }

            for i in 1...max(argCount, 1) {
                guard i < node.operands.count else { break }
                let argNode = node.operands[i]
                let origType = (i - 1) < argTypes.count ? argTypes[i - 1] : argNode.type

                // Struct/union argument: pass by value per ABI classification.
                // Arrays are NOT passed by value — they decay to pointers.
                let isStructArg: Bool
                switch origType {
                case .structType, .unionType: isStructArg = true
                default: isStructArg = false
                }
                if isStructArg {
                    let abi = classifyStruct(origType)
                    let structSz = typeSize(origType)
                    // Get struct address: nodeOperand for struct vars returns the address.
                    let addrOp = nodeOperand(argNode, ctx: &ctx)
                    let addrReg = ensureReg(addrOp, size: .qword, ctx: &ctx)

                    if abi.isMemory {
                        // MEMORY class: push struct content to stack.
                        // Load qwords in forward order (a, b, c) so that the
                        // reversed push loop puts them on the stack in struct layout order.
                        let qwords = (structSz + 7) / 8
                        for qi in 0..<qwords {
                            let off = Int32(qi * 8)
                            let remaining = structSz - qi * 8
                            let ldSz: Size = remaining >= 8 ? .qword : (remaining >= 4 ? .dword : (remaining >= 2 ? .word : .byte))
                            let tmp = ctx.freshVirtual()
                            ctx.instrs.append(.movMR(ldSz, src: Memory(base: addrReg, displacement: off), dst: tmp))
                            stackArgs.append((.reg(tmp), .qword))
                        }
                    } else {
                        // Small struct: load eightbytes into registers.
                        for (ebIdx, cls) in abi.classes.enumerated() {
                            let off = Int32(ebIdx * 8)
                            let remaining = structSz - ebIdx * 8
                            let ldSz: Size = remaining >= 8 ? .qword : .dword
                            let tmp = ctx.freshVirtual()

                            if cls == .sse {
                                ctx.instrs.append(ldSz == .dword
                                    ? .xmmMovMR(.single, src: Memory(base: addrReg, displacement: off), dst: tmp)
                                    : .xmmMovMR(.double_, src: Memory(base: addrReg, displacement: off), dst: tmp))
                                if sseIdx < PhysReg.sseArgRegs.count {
                                    let target = PhysReg.sseArgRegs[sseIdx]; sseIdx += 1
                                    regCopies.append((src: .reg(tmp), dst: .reg(.physical(target)), sz: ldSz == .dword ? .single : .double_))
                                } else {
                                    stackArgs.append((.reg(tmp), ldSz == .dword ? .single : .double_))
                                }
                            } else {
                                // INTEGER class
                                ctx.instrs.append(.movMR(ldSz, src: Memory(base: addrReg, displacement: off), dst: tmp))
                                if intIdx < PhysReg.intArgRegs.count {
                                    let target = PhysReg.intArgRegs[intIdx]; intIdx += 1
                                    regCopies.append((src: .reg(tmp), dst: .reg(.physical(target)), sz: .qword))
                                } else {
                                    stackArgs.append((.reg(tmp), .qword))
                                }
                            }
                        }
                    }
                    continue
                }

                let sz = sizeOf(argNode.type)
                let a = nodeOperand(argNode, ctx: &ctx)
                let isF = Machine.isFloat(argNode.type)

                if isF {
                    if sseIdx < PhysReg.sseArgRegs.count {
                        let target = PhysReg.sseArgRegs[sseIdx]
                        sseIdx += 1
                        regCopies.append((src: a, dst: .reg(.physical(target)), sz: sz))
                    } else {
                        stackArgs.append((a, sz))
                    }
                } else {
                    if intIdx < PhysReg.intArgRegs.count {
                        let target = PhysReg.intArgRegs[intIdx]
                        intIdx += 1
                        regCopies.append((src: a, dst: .reg(.physical(target)), sz: sz))
                    } else {
                        stackArgs.append((a, sz))
                    }
                }
            }

            // Emit parallel copy for register args
            if regCopies.count == 1 {
                let c = regCopies[0]
                if c.sz == .single {
                    ctx.instrs.append(.xmmMov(.single, src: c.src, dst: c.dst))
                } else if c.sz == .double_ {
                    ctx.instrs.append(.xmmMov(.double_, src: c.src, dst: c.dst))
                } else {
                    ctx.instrs.append(.mov(c.sz, src: c.src, dst: c.dst))
                }
            } else if regCopies.count > 1 {
                ctx.instrs.append(.pcopy(regCopies))
            }

            // Push stack args in reverse.
            // System V ABI requires 16-byte stack alignment at the call instruction.
            // Prologue guarantees RSP is 16-aligned. Each push subtracts 8, so an odd
            // number of stack args would misalign RSP. Pad with 8 bytes if needed.
            let needPadding = stackArgs.count % 2 != 0
            if needPadding {
                ctx.instrs.append(.aluRmiR(.sub, .qword, src: .imm(8), dst: .physical(.rsp)))
            }
            for (a, sz) in stackArgs.reversed() {
                if sz == .single || sz == .double_ {
                    // Can't push XMM registers; use sub+mov instead.
                    ctx.instrs.append(.aluRmiR(.sub, .qword, src: .imm(8), dst: .physical(.rsp)))
                    ctx.instrs.append(sz == .single
                        ? .xmmMov(.single, src: a, dst: .mem(Memory(base: .physical(.rsp), displacement: 0)))
                        : .xmmMov(.double_, src: a, dst: .mem(Memory(base: .physical(.rsp), displacement: 0))))
                } else {
                    ctx.instrs.append(.push(.qword, a))
                }
            }

            // Call
            let calleeOp = nodeOperand(node.operands[0], ctx: &ctx)
            ctx.instrs.append(.call(calleeOp))

            // Clean up stack (args + alignment padding)
            let stackClean = Int64(stackArgs.count * 8 + (needPadding ? 8 : 0))
            if stackClean > 0 {
                ctx.instrs.append(.aluRmiR(.add, .qword, src: .imm(stackClean),
                                       dst: .physical(.rsp)))
            }

            // Move result
            if isAggregate(node.type), let slot = retStructSlot {
                // Struct return: store return registers to temp stack slot.
                let retABI = classifyStruct(node.type)
                let structSz = typeSize(node.type)
                if !retABI.isMemory {
                    var retIntIdx = 0
                    var retSseIdx = 0
                    let intRetRegs: [PhysReg] = [.rax, .rdx]
                    let sseRetRegs: [PhysReg] = [.xmm0, .xmm1]
                    for (ebIdx, cls) in retABI.classes.enumerated() {
                        let off = Int32(ebIdx * 8)
                        let remaining = structSz - ebIdx * 8
                        let stSz: Size = remaining >= 8 ? .qword : .dword
                        let mem = Memory(base: .physical(.rbp), displacement: -slot + off)
                        if cls == .sse {
                            let reg = sseRetRegs[retSseIdx]; retSseIdx += 1
                            ctx.instrs.append(stSz == .dword
                                ? .xmmMovRM(.single, src: .physical(reg), dst: mem)
                                : .xmmMovRM(.double_, src: .physical(reg), dst: mem))
                        } else {
                            let reg = intRetRegs[retIntIdx]; retIntIdx += 1
                            ctx.instrs.append(.movRM(stSz, src: .physical(reg), dst: mem))
                        }
                    }
                }
                // Return a memory operand pointing to the struct data.
                return .mem(.stack(slot))
            } else if case .void = node.type {
                return nil
            } else {
                let dst = ctx.freshVirtual()
                let sz = sizeOf(node.type)
                if isFloat(node.type) {
                    ctx.instrs.append(sz == .single
                        ? .xmmMovRR(.single, src: .physical(.xmm0), dst: dst)
                        : .xmmMovRR(.double_, src: .physical(.xmm0), dst: dst))
                } else {
                    ctx.instrs.append(.movRR(sz, src: .physical(.rax), dst: dst))
                }
                return .reg(dst)
            }
        }
    ))

    // ── Compare / test (flag-setting) ───────────────────────────────

    patterns.append(ISelPattern(
        name: "compare",
        cost: 1,
        match: { node in
            if case .compare = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let lhsType = node.operands[0].type
            let sz = sizeOf(lhsType)
            let l = nodeOperand(node.operands[0], ctx: &ctx)
            let r = nodeOperand(node.operands[1], ctx: &ctx)
            if isFloat(lhsType) {
                let lReg = ensureReg(l, size: sz, ctx: &ctx)
                let rReg = ensureReg(r, size: sz, ctx: &ctx)
                ctx.instrs.append(sz == .single
                    ? .xmmCmp(.single, src: .reg(rReg), dst: lReg)
                    : .xmmCmp(.double_, src: .reg(rReg), dst: lReg))
            } else {
                let lReg = ensureReg(l, size: sz, ctx: &ctx)
                ctx.instrs.append(.cmpRmiR(.cmp, sz, src: r, dst: lReg))
            }
            return nil
        }
    ))

    patterns.append(ISelPattern(
        name: "test",
        cost: 1,
        match: { node in
            if case .test = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let type = node.operands[0].type
            let sz = sizeOf(type)
            let op = nodeOperand(node.operands[0], ctx: &ctx)
            if isFloat(type) {
                // Float test: compare against zero. Materialize 0.0 and compare.
                let reg = ensureReg(op, size: sz, ctx: &ctx)
                let zeroConst = materializeFloat(0.0,
                    type: sz == .single ? .float : .double, ctx: &ctx)
                let zeroReg = ensureReg(zeroConst, size: sz, ctx: &ctx)
                ctx.instrs.append(sz == .single
                    ? .xmmCmp(.single, src: .reg(zeroReg), dst: reg)
                    : .xmmCmp(.double_, src: .reg(zeroReg), dst: reg))
            } else {
                let reg = ensureReg(op, size: sz, ctx: &ctx)
                ctx.instrs.append(.cmpRmiR(.test, sz, src: .reg(reg), dst: reg))
            }
            return nil
        }
    ))

    // ── Inline asm ──────────────────────────────────────────────────

    patterns.append(ISelPattern(
        name: "inlineAsm",
        cost: 1,
        match: { node in
            if case .inlineAsm = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            if case .inlineAsm(let text) = node.kind {
                ctx.instrs.append(.inlineAsm(text))
            }
            return nil
        }
    ))

    // ── Atomics ─────────────────────────────────────────────────────

    patterns.append(ISelPattern(
        name: "cas",
        cost: 10,
        match: { node in
            if case .cas = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let addr = nodeOperand(node.operands[0], ctx: &ctx)
            let old = nodeOperand(node.operands[1], ctx: &ctx)
            let new_ = nodeOperand(node.operands[2], ctx: &ctx)
            let addrReg = ensureReg(addr, size: .qword, ctx: &ctx)
            let rax = Reg.physical(.rax)
            ctx.instrs.append(.mov(sz, src: old, dst: .reg(rax)))
            let newReg = ensureReg(new_, size: sz, ctx: &ctx)
            ctx.instrs.append(.inlineAsm("lock cmpxchg\(sz.suffix) %\(newReg), (%\(addrReg))"))
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.setcc(.e, dst))
            ctx.instrs.append(.movzxRmR(from: .byte, to: sizeOf(node.type),
                                     src: .reg(dst), dst: dst))
            return .reg(dst)
        }
    ))

    patterns.append(ISelPattern(
        name: "exchange",
        cost: 10,
        match: { node in
            if case .exchange = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let addr = nodeOperand(node.operands[0], ctx: &ctx)
            let val = nodeOperand(node.operands[1], ctx: &ctx)
            let addrReg = ensureReg(addr, size: .qword, ctx: &ctx)
            let rax = Reg.physical(.rax)
            ctx.instrs.append(.mov(sz, src: val, dst: .reg(rax)))
            ctx.instrs.append(.inlineAsm("lock xchg\(sz.suffix) %\(rax), (%\(addrReg))"))
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.movRR(sz, src: rax, dst: dst))
            return .reg(dst)
        }
    ))

    // ── Struct copy ────────────────────────────────────────────────

    patterns.append(ISelPattern(
        name: "structCopy",
        cost: 5,
        match: { node in
            if case .structCopy = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            guard case .structCopy(let size) = node.kind else { return nil }

            // Get ADDRESS of dst (stackSlot → lea, otherwise use emitted operand).
            let dstReg: Reg
            if case .stackSlot(let off) = node.operands[0].kind {
                dstReg = ctx.freshVirtual()
                ctx.instrs.append(.lea(.qword, src: .stack(off), dst: dstReg))
            } else {
                let dstOp = nodeOperand(node.operands[0], ctx: &ctx)
                dstReg = ensureReg(dstOp, size: .qword, ctx: &ctx)
            }

            // Detect memzero: source is intConst(0) → zero-fill instead of copy.
            let isMemZero: Bool
            if case .intConst(0) = node.operands[1].kind {
                isMemZero = true
            } else {
                isMemZero = false
            }

            let srcReg: Reg
            if isMemZero {
                // Use a zero register for stores.
                srcReg = ctx.freshVirtual()  // not actually used as address
            } else {
                // Get ADDRESS of src. If the emitted operand is a memory reference
                // (e.g. from a call returning a struct), use lea to get its address
                // instead of mov which would load the value.
                let srcOp = nodeOperand(node.operands[1], ctx: &ctx)
                if case .mem(let m) = srcOp {
                    srcReg = ctx.freshVirtual()
                    ctx.instrs.append(.lea(.qword, src: m, dst: srcReg))
                } else {
                    srcReg = ensureReg(srcOp, size: .qword, ctx: &ctx)
                }
            }

            // Emit qword copies for bulk, then handle remainder.
            var offset: Int32 = 0
            var remaining = size
            if isMemZero {
                // Zero-fill: write zeros directly to destination.
                let zeroReg = ctx.freshVirtual()
                ctx.instrs.append(.movIR(.qword, imm: 0, dst: zeroReg))
                while remaining >= 8 {
                    ctx.instrs.append(.movRM(.qword,
                        src: zeroReg,
                        dst: Memory(base: dstReg, displacement: offset)))
                    offset += 8
                    remaining -= 8
                }
                if remaining >= 4 {
                    ctx.instrs.append(.movRM(.dword,
                        src: zeroReg,
                        dst: Memory(base: dstReg, displacement: offset)))
                    offset += 4
                    remaining -= 4
                }
                if remaining >= 2 {
                    ctx.instrs.append(.movRM(.word,
                        src: zeroReg,
                        dst: Memory(base: dstReg, displacement: offset)))
                    offset += 2
                    remaining -= 2
                }
                if remaining >= 1 {
                    ctx.instrs.append(.movRM(.byte,
                        src: zeroReg,
                        dst: Memory(base: dstReg, displacement: offset)))
                }
            } else {
                // Normal copy: load from src, store to dst.
                while remaining >= 8 {
                    let tmp = ctx.freshVirtual()
                    ctx.instrs.append(.movMR(.qword,
                        src: Memory(base: srcReg, displacement: offset),
                        dst: tmp))
                    ctx.instrs.append(.movRM(.qword,
                        src: tmp,
                        dst: Memory(base: dstReg, displacement: offset)))
                    offset += 8
                    remaining -= 8
                }
                if remaining >= 4 {
                    let tmp = ctx.freshVirtual()
                    ctx.instrs.append(.movMR(.dword,
                        src: Memory(base: srcReg, displacement: offset),
                        dst: tmp))
                    ctx.instrs.append(.movRM(.dword,
                        src: tmp,
                        dst: Memory(base: dstReg, displacement: offset)))
                    offset += 4
                    remaining -= 4
                }
                if remaining >= 2 {
                    let tmp = ctx.freshVirtual()
                    ctx.instrs.append(.movMR(.word,
                        src: Memory(base: srcReg, displacement: offset),
                        dst: tmp))
                    ctx.instrs.append(.movRM(.word,
                        src: tmp,
                        dst: Memory(base: dstReg, displacement: offset)))
                    offset += 2
                    remaining -= 2
                }
                if remaining >= 1 {
                    let tmp = ctx.freshVirtual()
                    ctx.instrs.append(.movMR(.byte,
                        src: Memory(base: srcReg, displacement: offset),
                        dst: tmp))
                    ctx.instrs.append(.movRM(.byte,
                        src: tmp,
                        dst: Memory(base: dstReg, displacement: offset)))
                }
            }
            return nil
        }
    ))

    return patterns
}

// MARK: - Shared emit helpers

private enum ShiftKind { case shl, shr, sar }

/// Emit a shift instruction. For non-immediate counts, emits the shift with
/// a virtual register source; the ConstraintResolver will insert the rcx copy.
private func emitShift(_ kind: ShiftKind, node: DAGNode, ctx: inout ISelContext) -> Operand {
    let sz = sizeOf(node.type)
    let lhs = nodeOperand(node.operands[0], ctx: &ctx)
    let rhs = nodeOperand(node.operands[1], ctx: &ctx)
    let dst = ctx.freshVirtual()
    ctx.instrs.append(.mov(sz, src: lhs, dst: .reg(dst)))
    switch kind {
    case .shl: ctx.instrs.append(.shiftR(.shl, sz, src: rhs, dst: dst))
    case .shr: ctx.instrs.append(.shiftR(.shr, sz, src: rhs, dst: dst))
    case .sar: ctx.instrs.append(.shiftR(.sar, sz, src: rhs, dst: dst))
    }
    return .reg(dst)
}

// emitDivMod removed — div/mod now use pseudoDiv/pseudoMod,
// expanded by ConstraintResolver.

// MARK: - Type layout helpers

func memberOffset(_ type: CType, name: String) -> Int32 {
    if case .pointer(let inner) = type, case .structType(let r) = inner {
        return computeMemberOffset(r, name: name)
    }
    if case .structType(let r) = type {
        return computeMemberOffset(r, name: name)
    }
    return 0
}

private func computeMemberOffset(_ r: CRecordType, name: String) -> Int32 {
    var offset = 0
    for m in r.members {
        let align = typeAlign(m.type)
        offset = (offset + align - 1) / align * align
        if m.name == name { return Int32(offset) }
        offset += typeSize(m.type)
    }
    return 0
}


