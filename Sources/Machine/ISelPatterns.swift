import Tree

// MARK: - BinaryOp extensions for ISel

extension BinaryOp {
    var sseOp: SseOp? {
        switch self {
        case .add: .add; case .sub: .sub; case .mul: .mul; case .div: .div
        default: nil
        }
    }
    var aluOp: AluOp? {
        switch self {
        case .bitAnd: .and; case .bitOr: .or; case .bitXor: .xor
        case .add: .add; case .sub: .sub
        default: nil
        }
    }
}

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
            type: floatType(for: size), ctx: &ctx)
        if case .reg(let r) = fop { return r }
    }
    let tmp = ctx.freshVirtual()
    if size == .single || size == .double_ {
        ctx.instrs.append(.xmmMov(size, src: op, dst: .reg(tmp)))
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
    ctx.instrs.append(.xmmMovMR(sz, src: mem, dst: reg))
    return .reg(reg)
}

/// Map a float Size (.single/.double_) to the corresponding CType.
private func floatType(for sz: Size) -> CType {
    sz == .single ? .float : .double
}

/// Emit a load from memory, choosing XMM or GP instruction based on float flag.
private func emitLoad(sz: Size, from mem: Memory, to dst: Reg, float: Bool, ctx: inout ISelContext) {
    if float {
        ctx.instrs.append(.xmmMovMR(sz, src: mem, dst: dst))
    } else {
        ctx.instrs.append(.movMR(sz, src: mem, dst: dst))
    }
}

/// Emit a store to memory, choosing XMM or GP instruction based on float flag.
private func emitStore(sz: Size, val: Operand, to mem: Memory, float: Bool, ctx: inout ISelContext) {
    if float {
        let srcReg = ensureReg(val, size: sz, ctx: &ctx)
        ctx.instrs.append(.xmmMovRM(sz, src: srcReg, dst: mem))
    } else {
        let src = ensureRegOrImm(val, size: sz, ctx: &ctx)
        ctx.instrs.append(.mov(sz, src: src, dst: .mem(mem)))
    }
}

/// Emit a block memory transfer (copy or zero-fill) using qword/dword/word/byte chunks.
/// If `srcReg` is nil, zero-fills the destination instead of copying.
func emitBlockTransfer(to dstReg: Reg, from srcReg: Reg?, size: Int, ctx: inout ISelContext) {
    var offset: Int32 = 0
    var remaining = size
    let zeroReg: Reg?
    if srcReg == nil {
        zeroReg = ctx.freshVirtual()
        ctx.instrs.append(.movIR(.qword, imm: 0, dst: zeroReg!))
    } else {
        zeroReg = nil
    }
    for (chunkBytes, chunkSz) in [(8, Size.qword), (4, Size.dword), (2, Size.word), (1, Size.byte)] as [(Int, Size)] {
        while remaining >= chunkBytes {
            if let src = srcReg {
                let tmp = ctx.freshVirtual()
                ctx.instrs.append(.movMR(chunkSz, src: Memory(base: src, displacement: offset), dst: tmp))
                ctx.instrs.append(.movRM(chunkSz, src: tmp, dst: Memory(base: dstReg, displacement: offset)))
            } else {
                ctx.instrs.append(.movRM(chunkSz, src: zeroReg!, dst: Memory(base: dstReg, displacement: offset)))
            }
            offset += Int32(chunkBytes)
            remaining -= chunkBytes
        }
    }
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

    // lea_mul3/5/9: mul(x, const(3|5|9)) → lea (x, x, scale)
    for (constVal, scale, name) in [(Int64(3), UInt8(2), "lea_mul3"),
                                     (Int64(5), UInt8(4), "lea_mul5"),
                                     (Int64(9), UInt8(8), "lea_mul9")] {
        patterns.append(ISelPattern(
            name: name,
            cost: 1,
            match: { node in
                guard case .binary(.mul) = node.kind,
                      !isFloat(node.type),
                      sizeOf(node.type) == .dword || sizeOf(node.type) == .qword
                else { return false }
                return isIntConst(node.operands[1], value: constVal)
            },
            consumedChildren: { _ in [] },
            emit: { node, ctx in
                let sz = sizeOf(node.type)
                let x = nodeOperand(node.operands[0], ctx: &ctx)
                let xReg = ensureReg(x, size: sz, ctx: &ctx)
                let dst = ctx.freshVirtual()
                ctx.instrs.append(.lea(sz, src: Memory(base: xReg, index: xReg, scale: scale), dst: dst))
                return .reg(dst)
            }
        ))
    }

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

    // mul by 3/5/9 → LEA (1 instruction instead of mov+imul)
    // x*3 = x+x*2 → lea (%r,%r,2), %r
    // x*5 = x+x*4 → lea (%r,%r,4), %r
    // x*9 = x+x*8 → lea (%r,%r,8), %r
    patterns.append(ISelPattern(
        name: "mulLea",
        cost: 2,
        match: { node in
            guard case .binary(.mul) = node.kind, !isFloat(node.type) else { return false }
            let sz = sizeOf(node.type)
            guard sz == .dword || sz == .qword else { return false }
            // Check if either operand is 3, 5, or 9
            if let c = intConstValue(node.operands[1]), c == 3 || c == 5 || c == 9 { return true }
            if let c = intConstValue(node.operands[0]), c == 3 || c == 5 || c == 9 { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sz = sizeOf(node.type)
            let (valNode, constNode) = intConstValue(node.operands[1]) != nil
                ? (node.operands[0], node.operands[1])
                : (node.operands[1], node.operands[0])
            let c = intConstValue(constNode)!
            let scale: UInt8 = c == 3 ? 2 : c == 5 ? 4 : 8  // scale = c - 1
            let val = nodeOperand(valNode, ctx: &ctx)
            let src = ensureReg(val, size: sz, ctx: &ctx)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.lea(sz, src: Memory(base: src, index: src, scale: scale), dst: dst))
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
        let aluOp = op.aluOp!
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
                ctx.instrs.append(.aluRmiR(aluOp, sz, src: r, dst: dst))
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
        // Precompute float condition code: lt→b, le→be, else same as int CC
        let floatCC: CondCode = (op == .lt) ? .b : (op == .le) ? .be : cc
        // Precompute unsigned int condition code: lt→b, le→be
        let unsignedCC: CondCode? = (op == .lt) ? .b : (op == .le) ? .be : nil
        let isNeParity = (op == .ne)
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
                    ctx.instrs.append(.xmmCmp(sz, src: .reg(rReg), dst: lReg))
                    ctx.instrs.append(.setcc(floatCC, dst))
                    // NaN handling: ucomisd sets PF=1 for unordered (NaN).
                    // C semantics: NaN comparisons return false (eq/lt/le) or
                    // true (ne). Adjust by checking parity flag.
                    if isNeParity {
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
                    if !isMachineSigned(operandType), let uCC = unsignedCC {
                        intCC = uCC
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
        let sseOp = op.sseOp!
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
                let l = nodeOperand(node.operands[0], ctx: &ctx)
                let r = nodeOperand(node.operands[1], ctx: &ctx)
                let dst = ctx.freshVirtual()
                ctx.instrs.append(.xmmMov(sz, src: l, dst: .reg(dst)))
                ctx.instrs.append(.xmmRmR(sseOp, sz, src: r, dst: dst))
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
                let zeroOp = materializeFloat(0.0, type: floatType(for: sz), ctx: &ctx)
                let zeroReg = ensureReg(zeroOp, size: sz, ctx: &ctx)
                ctx.instrs.append(.xmmMovRR(sz, src: zeroReg, dst: dst))
                ctx.instrs.append(.xmmRmR(.sub, sz, src: src, dst: dst))
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
            let fl = isFloat(node.type)
            if case .reg(let base) = addr {
                emitLoad(sz: sz, from: Memory(base: base), to: dst, float: fl, ctx: &ctx)
            } else if case .mem(let mem) = addr {
                if mem.isStack {
                    // Stack slot: the mem operand IS the address, load directly.
                    emitLoad(sz: sz, from: mem, to: dst, float: fl, ctx: &ctx)
                } else {
                    // Global/other: load the pointer, then dereference.
                    let tmp = ctx.freshVirtual()
                    ctx.instrs.append(.movMR(.qword, src: mem, dst: tmp))
                    emitLoad(sz: sz, from: Memory(base: tmp), to: dst, float: fl, ctx: &ctx)
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
            let fl = isFloat(valType)
            if case .reg(let base) = addr {
                emitStore(sz: sz, val: val, to: Memory(base: base), float: fl, ctx: &ctx)
            } else if case .mem(let mem) = addr {
                if mem.isStack {
                    // Stack slot: write directly to the memory operand.
                    emitStore(sz: sz, val: val, to: mem, float: fl, ctx: &ctx)
                } else if mem.symbol != nil && mem.base == nil {
                    // Global variable (RIP-relative): store directly.
                    emitStore(sz: sz, val: val, to: mem, float: fl, ctx: &ctx)
                } else {
                    // Other: load the pointer, then write through it.
                    let tmp = ctx.freshVirtual()
                    ctx.instrs.append(.movMR(.qword, src: mem, dst: tmp))
                    emitStore(sz: sz, val: val, to: Memory(base: tmp), float: fl, ctx: &ctx)
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
                // If the base is a global pointer (not a struct), we need to load
                // the pointer value first, then add offset. Global struct bases
                // (e.g. `s.field` where `s` is a global struct) use lea directly.
                if !mem.isStack, case .pointer = node.operands[0].type {
                    let tmp = ctx.freshVirtual()
                    ctx.instrs.append(.movMR(.qword, src: mem, dst: tmp))
                    ctx.instrs.append(.lea(.qword,
                                           src: Memory(base: tmp, displacement: mOffset),
                                           dst: dst))
                } else {
                    // Compute address = base_address + member_offset
                    let newMem = Memory(base: mem.base, index: mem.index, scale: mem.scale,
                                        displacement: mem.displacement + mOffset, symbol: mem.symbol)
                    ctx.instrs.append(.lea(.qword, src: newMem, dst: dst))
                }
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
                    // float/double → _Bool: compare against 0.0, setne
                    let sReg = ensureReg(src, size: fromSz, ctx: &ctx)
                    let zeroImm = materializeFloat(0.0, type: floatType(for: fromSz), ctx: &ctx)
                    ctx.instrs.append(.xmmCmp(fromSz, src: zeroImm, dst: sReg))
                    ctx.instrs.append(.setcc(.ne, dst))
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
                    ctx.instrs.append(.xmmMov(fromSz, src: src, dst: .reg(dst)))
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
                                                 type: floatType(for: toSz), ctx: &ctx)
                    ctx.instrs.append(.xmmRmR(.mul, toSz, src: scale, dst: hiF))
                    ctx.instrs.append(.xmmRmR(.add, toSz, src: .reg(loF), dst: hiF))
                    ctx.instrs.append(.xmmMovRR(toSz, src: hiF, dst: dst))
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
                    let retSize = Int32(node.type.size)
                    let retAlign = Int32(max(node.type.align, 8))
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
                    let retSize = Int32(max(node.type.size, 16)) // ensure room for 2 qwords
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
                    let structSz = origType.size
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
                if c.sz == .single || c.sz == .double_ {
                    ctx.instrs.append(.xmmMov(c.sz, src: c.src, dst: c.dst))
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
                    ctx.instrs.append(.xmmMov(sz, src: a, dst: .mem(Memory(base: .physical(.rsp), displacement: 0))))
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
                let structSz = node.type.size
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
                    ctx.instrs.append(.xmmMovRR(sz, src: .physical(.xmm0), dst: dst))
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
                ctx.instrs.append(.xmmCmp(sz, src: .reg(rReg), dst: lReg))
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
                let zeroConst = materializeFloat(0.0, type: floatType(for: sz), ctx: &ctx)
                let zeroReg = ensureReg(zeroConst, size: sz, ctx: &ctx)
                ctx.instrs.append(.xmmCmp(sz, src: .reg(zeroReg), dst: reg))
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

            let srcReg: Reg?
            if isMemZero {
                srcReg = nil
            } else {
                // Get ADDRESS of src. If the emitted operand is a memory reference
                // (e.g. from a call returning a struct), use lea to get its address
                // instead of mov which would load the value.
                let srcOp = nodeOperand(node.operands[1], ctx: &ctx)
                if case .mem(let m) = srcOp {
                    let r = ctx.freshVirtual()
                    ctx.instrs.append(.lea(.qword, src: m, dst: r))
                    srcReg = r
                } else {
                    srcReg = ensureReg(srcOp, size: .qword, ctx: &ctx)
                }
            }

            emitBlockTransfer(to: dstReg, from: srcReg, size: size, ctx: &ctx)
            return nil
        }
    ))

    // ── Alloca (dynamic stack allocation) ───────────────────────────

    patterns.append(ISelPattern(
        name: "alloca",
        cost: 1,
        match: { node in
            if case .alloca = node.kind { return true }
            return false
        },
        consumedChildren: { _ in [] },
        emit: { node, ctx in
            let sizeOp = nodeOperand(node.operands[0], ctx: &ctx)
            let sizeReg = ensureReg(sizeOp, size: .qword, ctx: &ctx)
            // Round up to 16-byte alignment: size = (size + 15) & ~15
            let alignedSize = ctx.freshVirtual()
            ctx.instrs.append(.movRR(.qword, src: sizeReg, dst: alignedSize))
            ctx.instrs.append(.aluRmiR(.add, .qword, src: .imm(15), dst: alignedSize))
            ctx.instrs.append(.aluRmiR(.and, .qword, src: .imm(-16), dst: alignedSize))
            // sub alignedSize, %rsp
            ctx.instrs.append(.aluRmiR(.sub, .qword, src: .reg(alignedSize), dst: .physical(.rsp)))
            // result = rsp (pointer to allocated space)
            let dst = ctx.freshVirtual()
            ctx.instrs.append(.movRR(.qword, src: .physical(.rsp), dst: dst))
            return .reg(dst)
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
    for m in r.members where m.name == name {
        return Int32(m.offset)
    }
    // Recurse into anonymous struct/union members.
    for m in r.members where m.name == nil {
        switch m.type {
        case .structType(let inner), .unionType(let inner):
            let off = computeMemberOffset(inner, name: name)
            if off != 0 || inner.members.contains(where: { $0.name == name }) {
                return off
            }
        default:
            break
        }
    }
    return 0
}


