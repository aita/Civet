import Tree

/// Algebraic identity simplification and power-of-2 strength reduction.
///
/// Replaces expensive or redundant binary operations with cheaper equivalents:
/// - Identity elements: x+0→x, x*1→x, x&allones→x, etc.
/// - Annihilators: x*0→0, x&0→0, etc.
/// - Self-operations: x-x→0, x^x→0, x==x→1, etc.
/// - Power-of-2: x*2^n→x<<n, unsigned x/2^n→x>>n, unsigned x%2^n→x&mask
///
/// This pass only fires when at least one operand is a constant OR both are the
/// same SSA variable. It does not fold all-constant binaries (ConstantFolding's job).
public func strengthReduction(in function: Function) -> Function {
    let newBlocks = function.blocks.map { block -> Block in
        let instrs = block.instructions.map { instr -> Instr in
            guard case .binary(let dest, let op, let lhs, let rhs) = instr else {
                return instr
            }
            return simplifyBinary(dest: dest, op: op, lhs: lhs, rhs: rhs) ?? instr
        }
        return block.with(instructions: instrs)
    }
    return withBlocks(function, newBlocks)
}

private func simplifyBinary(dest: Place, op: BinaryOp,
                             lhs: Operand, rhs: Operand) -> Instr? {
    let type = dest.type
    let signed = isSigned(type)
    let width = bitwidth(type)
    // All-ones bit pattern for this type's width.
    let allOnes: Int64 = width < 64
        ? Int64(bitPattern: UInt64.max >> (64 - width))
        : -1  // Int64(bitPattern: UInt64.max)

    func constVal(_ op: Operand) -> Int64? {
        if case .intConst(let v, _) = op { return v }
        return nil
    }
    func isZero(_ op: Operand) -> Bool {
        guard case .intConst(let v, _) = op else { return false }
        return truncateToType(v, type) == 0
    }
    func isOne(_ op: Operand) -> Bool {
        guard case .intConst(let v, _) = op else { return false }
        return truncateToType(v, type) == 1
    }
    // "allones" is -1 for signed types, and the max-unsigned-value for unsigned.
    func isAllOnes(_ op: Operand) -> Bool {
        guard case .intConst(let v, _) = op else { return false }
        let t = truncateToType(v, type)
        return signed ? t == -1 : t == allOnes
    }
    func sameVar(_ a: Operand, _ b: Operand) -> Bool {
        if case .variable(_, let id1, _) = a,
           case .variable(_, let id2, _) = b { return id1 == id2 }
        return false
    }
    func zero() -> Instr { .assign(dest: dest, src: .intConst(0, type: dest.type)) }
    func one()  -> Instr { .assign(dest: dest, src: .intConst(1, type: dest.type)) }
    func assign(_ src: Operand) -> Instr { .assign(dest: dest, src: src) }

    // ── Section 1: Identity / annihilator with constants ─────────────────
    switch op {
    case .add:
        if isZero(rhs) { return assign(lhs) }
        if isZero(lhs) { return assign(rhs) }
    case .sub:
        if isZero(rhs) { return assign(lhs) }
    case .mul:
        if isZero(rhs) { return zero() }
        if isZero(lhs) { return zero() }
        if isOne(rhs)  { return assign(lhs) }
        if isOne(lhs)  { return assign(rhs) }
    case .div:
        if isOne(rhs) { return assign(lhs) }
    case .bitAnd:
        if isZero(rhs) { return zero() }
        if isZero(lhs) { return zero() }
        if isAllOnes(rhs) { return assign(lhs) }
        if isAllOnes(lhs) { return assign(rhs) }
    case .bitOr:
        if isZero(rhs) { return assign(lhs) }
        if isZero(lhs) { return assign(rhs) }
        if isAllOnes(rhs) { return .assign(dest: dest, src: .intConst(allOnes, type: dest.type)) }
        if isAllOnes(lhs) { return .assign(dest: dest, src: .intConst(allOnes, type: dest.type)) }
    case .bitXor:
        if isZero(rhs) { return assign(lhs) }
        if isZero(lhs) { return assign(rhs) }
    case .shl:
        if isZero(rhs) { return assign(lhs) }
    case .shr:
        if isZero(rhs) { return assign(lhs) }
    default:
        break
    }

    // ── Section 2: Self-operation rules (same SSA variable, integers only) ──
    // Float/double do not satisfy these identities under IEEE 754
    // (e.g. NaN - NaN ≠ 0, NaN == NaN is false).
    // Check operand type (not dest type) — comparisons produce bool dest but float operands.
    let isFloatOperand: Bool
    switch lhs.type { case .float, .double: isFloatOperand = true; default: isFloatOperand = false }
    if !isFloatOperand, sameVar(lhs, rhs) {
        switch op {
        case .sub:    return zero()
        case .bitXor: return zero()
        case .bitAnd: return assign(lhs)
        case .bitOr:  return assign(lhs)
        case .eq:     return one()
        case .ne:     return zero()
        case .lt:     return zero()
        case .le:     return one()
        default:      break
        }
    }

    // ── Section 3: Power-of-2 strength reduction ──────────────────────────
    // rhs is a constant
    if let c = constVal(rhs) {
        let cv = truncateToType(c, type)
        switch op {
        case .mul:
            if let n = exactLog2(cv, width: width) {
                // x * 2^n → x << n
                return .binary(dest: dest, op: .shl,
                               lhs: lhs,
                               rhs: .intConst(Int64(n), type: dest.type))
            }
            // x * (-1) → neg x  (signed only)
            if signed && (cv == -1) {
                return .unary(dest: dest, op: .neg, src: lhs)
            }
        case .div:
            // unsigned x / 2^n → x >> n
            if !signed, let n = exactLog2(cv, width: width) {
                return .binary(dest: dest, op: .shr,
                               lhs: lhs,
                               rhs: .intConst(Int64(n), type: dest.type))
            }
        case .mod:
            // unsigned x % 2^n → x & (2^n - 1)
            if !signed, let n = exactLog2(cv, width: width) {
                let mask = Int64(bitPattern: (UInt64(1) << n) &- 1)
                return .binary(dest: dest, op: .bitAnd,
                               lhs: lhs,
                               rhs: .intConst(mask, type: dest.type))
            }
        default:
            break
        }
    }

    // lhs is a constant (commutative mul only)
    if let c = constVal(lhs), op == .mul {
        let cv = truncateToType(c, type)
        if let n = exactLog2(cv, width: width) {
            // 2^n * x → x << n
            return .binary(dest: dest, op: .shl,
                           lhs: rhs,
                           rhs: .intConst(Int64(n), type: dest.type))
        }
        if signed && cv == -1 {
            return .unary(dest: dest, op: .neg, src: rhs)
        }
    }

    // ── Section 4: Unsigned comparison trivia ────────────────────────────
    if !signed {
        if op == .lt, case .intConst(let v, _) = rhs, truncateToType(v, type) == 0 {
            return zero()  // unsigned x < 0 → false
        }
        if op == .le, case .intConst(let v, _) = lhs, truncateToType(v, type) == 0 {
            return one()   // unsigned 0 <= x → true
        }
    }

    return nil
}

/// Returns n if v == 2^n for some n in [1, width-1]; otherwise nil.
/// Masks to the type's width to avoid misinterpreting sign-extended values.
private func exactLog2(_ v: Int64, width: Int) -> Int? {
    let mask: UInt64 = width < 64 ? (UInt64(1) << width) &- 1 : UInt64.max
    let uv = UInt64(bitPattern: v) & mask
    guard uv > 1, uv & (uv &- 1) == 0 else { return nil }
    return Int(uv.trailingZeroBitCount)
}
