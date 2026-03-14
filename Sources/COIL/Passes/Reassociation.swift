import Tree

/// Reassociation of associative binary operations.
///
/// Reorders chains of associative operations with constants so that constant
/// subexpressions are adjacent and can be folded by ConstantFolding / SCCP:
///
///   (x + c1) + c2  →  x + (c1+c2)
///   (x * c1) * c2  →  x * (c1*c2)
///   (x + c1) - c2  →  x + (c1-c2)
///   c1 + (x + c2)  →  x + (c1+c2)   (commuted add)
///
/// Works only on integer types (float/double reassociation can change IEEE 754
/// rounding results and is not performed).
///
/// The pass is intra-block: it tracks variable definitions within each block
/// and looks one level back through the def-use chain.
public func reassociation(in function: Function) -> Function {
    let newBlocks = function.blocks.map { block -> Block in
        // Map from variable id → (op, lhs, rhs) of its defining binary instruction.
        var defMap: [Int: (BinaryOp, Operand, Operand)] = [:]
        for instr in block.instructions {
            if case .binary(let dest, let op, let lhs, let rhs) = instr {
                defMap[dest.id] = (op, lhs, rhs)
            }
        }

        let instrs = block.instructions.map { instr -> Instr in
            guard case .binary(let dest, let op, let lhs, let rhs) = instr else {
                return instr
            }
            return reassociateBinary(dest: dest, op: op, lhs: lhs, rhs: rhs,
                                     defMap: defMap) ?? instr
        }
        return block.with(instructions: instrs)
    }
    return withBlocks(function, newBlocks)
}

// ── Reassociation for a single binary instruction ────────────────────────────

private func reassociateBinary(dest: Place, op: BinaryOp,
                                lhs: Operand, rhs: Operand,
                                defMap: [Int: (BinaryOp, Operand, Operand)]) -> Instr? {
    let type = dest.type
    // Only integer types — float reassociation changes IEEE 754 rounding.
    switch type { case .float, .double: return nil; default: break }

    // Extract inner definition from a variable operand.
    func innerDef(_ operand: Operand) -> (BinaryOp, Operand, Operand)? {
        guard case .variable(_, let id, _) = operand else { return nil }
        return defMap[id]
    }
    func constVal(_ op: Operand) -> Int64? {
        guard case .intConst(let v, _) = op else { return nil }
        return v
    }

    switch op {

    // ── Addition ──────────────────────────────────────────────────────────
    case .add:
        // (x + c1) + c2  →  x + (c1+c2)
        if let c2 = constVal(rhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(lhs),
           innerOp == .add, let c1 = constVal(innerRhs),
           let folded = evalBinary(.add, c1, c2, type: type) {
            return .binary(dest: dest, op: .add, lhs: innerLhs,
                           rhs: .intConst(folded, type: type))
        }
        // c1 + (x + c2)  →  x + (c1+c2)  [commuted]
        if let c1 = constVal(lhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(rhs),
           innerOp == .add, let c2 = constVal(innerRhs),
           let folded = evalBinary(.add, c1, c2, type: type) {
            return .binary(dest: dest, op: .add, lhs: innerLhs,
                           rhs: .intConst(folded, type: type))
        }
        // (c1 + x) + c2  →  x + (c1+c2)  [inner lhs is const]
        if let c2 = constVal(rhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(lhs),
           innerOp == .add, let c1 = constVal(innerLhs),
           let folded = evalBinary(.add, c1, c2, type: type) {
            return .binary(dest: dest, op: .add, lhs: innerRhs,
                           rhs: .intConst(folded, type: type))
        }

    // ── Subtraction ───────────────────────────────────────────────────────
    case .sub:
        // (x + c1) - c2  →  x + (c1-c2)
        if let c2 = constVal(rhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(lhs),
           innerOp == .add, let c1 = constVal(innerRhs),
           let folded = evalBinary(.sub, c1, c2, type: type) {
            // If folded == 0, leave as assign(innerLhs); StrengthReduction handles that.
            return .binary(dest: dest, op: .add, lhs: innerLhs,
                           rhs: .intConst(folded, type: type))
        }
        // (x - c1) - c2  →  x - (c1+c2)
        if let c2 = constVal(rhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(lhs),
           innerOp == .sub, let c1 = constVal(innerRhs),
           let folded = evalBinary(.add, c1, c2, type: type) {
            return .binary(dest: dest, op: .sub, lhs: innerLhs,
                           rhs: .intConst(folded, type: type))
        }

    // ── Multiplication ────────────────────────────────────────────────────
    case .mul:
        // (x * c1) * c2  →  x * (c1*c2)
        if let c2 = constVal(rhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(lhs),
           innerOp == .mul, let c1 = constVal(innerRhs),
           let folded = evalBinary(.mul, c1, c2, type: type) {
            return .binary(dest: dest, op: .mul, lhs: innerLhs,
                           rhs: .intConst(folded, type: type))
        }
        // c1 * (x * c2)  →  x * (c1*c2)
        if let c1 = constVal(lhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(rhs),
           innerOp == .mul, let c2 = constVal(innerRhs),
           let folded = evalBinary(.mul, c1, c2, type: type) {
            return .binary(dest: dest, op: .mul, lhs: innerLhs,
                           rhs: .intConst(folded, type: type))
        }

    // ── Bitwise AND ───────────────────────────────────────────────────────
    case .bitAnd:
        // (x & c1) & c2  →  x & (c1&c2)
        if let c2 = constVal(rhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(lhs),
           innerOp == .bitAnd, let c1 = constVal(innerRhs),
           let folded = evalBinary(.bitAnd, c1, c2, type: type) {
            return .binary(dest: dest, op: .bitAnd, lhs: innerLhs,
                           rhs: .intConst(folded, type: type))
        }

    // ── Bitwise OR ────────────────────────────────────────────────────────
    case .bitOr:
        // (x | c1) | c2  →  x | (c1|c2)
        if let c2 = constVal(rhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(lhs),
           innerOp == .bitOr, let c1 = constVal(innerRhs),
           let folded = evalBinary(.bitOr, c1, c2, type: type) {
            return .binary(dest: dest, op: .bitOr, lhs: innerLhs,
                           rhs: .intConst(folded, type: type))
        }

    // ── Bitwise XOR ───────────────────────────────────────────────────────
    case .bitXor:
        // (x ^ c1) ^ c2  →  x ^ (c1^c2)
        if let c2 = constVal(rhs),
           let (innerOp, innerLhs, innerRhs) = innerDef(lhs),
           innerOp == .bitXor, let c1 = constVal(innerRhs),
           let folded = evalBinary(.bitXor, c1, c2, type: type) {
            return .binary(dest: dest, op: .bitXor, lhs: innerLhs,
                           rhs: .intConst(folded, type: type))
        }

    default:
        break
    }

    return nil
}
