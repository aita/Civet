import Tree

// MARK: - Constant folding utilities
//
// The `foldConstants` pass has been removed (subsumed by SCCP).
// The utility functions below (evalBinary, evalUnary, isSigned, etc.)
// are still used by SCCP, Reassociation, and other passes.

func isSigned(_ type: CType) -> Bool {
    switch type {
    case .bool: return false
    case .char(let signed): return signed
    case .short(let signed): return signed
    case .int(let signed): return signed
    case .long(let signed): return signed
    case .pointer, .enumType: return false
    default: return true
    }
}

func truncateToType(_ val: Int64, _ type: CType) -> Int64 {
    switch type {
    case .bool:             return val != 0 ? 1 : 0
    case .char(let signed):
        return signed ? Int64(Int8(truncatingIfNeeded: val)) : Int64(UInt8(truncatingIfNeeded: val))
    case .short(let signed):
        return signed ? Int64(Int16(truncatingIfNeeded: val)) : Int64(UInt16(truncatingIfNeeded: val))
    case .int(let signed):
        return signed ? Int64(Int32(truncatingIfNeeded: val)) : Int64(UInt32(truncatingIfNeeded: val))
    default:
        return val  // long, pointer — already 64-bit
    }
}

/// Bitwidth for the type.
func bitwidth(_ type: CType) -> Int {
    switch type {
    case .bool, .char: return 8
    case .short: return 16
    case .int: return 32
    default: return 64
    }
}

func evalBinary(_ op: BinaryOp, _ a: Int64, _ b: Int64, type: CType) -> Int64? {
    let signed = isSigned(type)
    let w = bitwidth(type)

    // For operations that depend on signedness, use unsigned arithmetic when needed.
    switch op {
    case .add:    return truncateToType(a &+ b, type)
    case .sub:    return truncateToType(a &- b, type)
    case .mul:    return truncateToType(a &* b, type)
    case .div:
        guard b != 0 else { return nil }
        if signed {
            return truncateToType(a / b, type)
        } else {
            // Unsigned division: interpret both as unsigned at the right width.
            let ua = UInt64(bitPattern: truncateToType(a, type))
            let ub = UInt64(bitPattern: truncateToType(b, type))
            return Int64(bitPattern: ua / ub)
        }
    case .mod:
        guard b != 0 else { return nil }
        if signed {
            return truncateToType(a % b, type)
        } else {
            let ua = UInt64(bitPattern: truncateToType(a, type))
            let ub = UInt64(bitPattern: truncateToType(b, type))
            return Int64(bitPattern: ua % ub)
        }
    case .bitAnd: return a & b
    case .bitOr:  return a | b
    case .bitXor: return truncateToType(a ^ b, type)
    case .shl:    return truncateToType(a << b, type)
    case .shr:
        if signed {
            // Arithmetic shift right on the truncated value.
            let tv = truncateToType(a, type)
            return truncateToType(tv >> b, type)
        } else {
            // Logical shift right: use unsigned value.
            let ua = UInt64(bitPattern: truncateToType(a, type))
            return Int64(bitPattern: ua >> b)
        }
    case .eq:     return a == b ? 1 : 0
    case .ne:     return a != b ? 1 : 0
    case .lt:
        if signed { return a < b ? 1 : 0 }
        let ua = UInt64(bitPattern: a), ub = UInt64(bitPattern: b)
        return ua < ub ? 1 : 0
    case .le:
        if signed { return a <= b ? 1 : 0 }
        let ua = UInt64(bitPattern: a), ub = UInt64(bitPattern: b)
        return ua <= ub ? 1 : 0
    }
}

func evalUnary(_ op: UnaryOp, _ a: Int64, type: CType) -> Int64? {
    switch op {
    case .neg:    return truncateToType(-a, type)
    case .bitNot: return truncateToType(~a, type)
    }
}
