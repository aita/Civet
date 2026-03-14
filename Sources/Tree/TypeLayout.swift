// MARK: - Canonical type layout computation for CType
//
// All modules (COIL, Machine) should use these functions instead of
// maintaining their own copies.

/// Compute the byte size of a C type.
public func typeSize(_ type: CType) -> Int {
    switch type {
    case .void: return 0
    case .bool, .char: return 1
    case .short: return 2
    case .int, .enumType, .float: return 4
    case .long, .double, .longDouble, .pointer, .function: return 8
    case .array(let elem, let count): return typeSize(elem) * count
    case .vla: return 8
    case .structType(let r):
        var offset = 0
        for m in r.members {
            let a = typeAlign(m.type)
            offset = (offset + a - 1) / a * a
            offset += typeSize(m.type)
        }
        let structAlign = r.members.map { typeAlign($0.type) }.max() ?? 1
        return (offset + structAlign - 1) / structAlign * structAlign
    case .unionType(let r):
        return r.members.map { typeSize($0.type) }.max() ?? 0
    }
}

/// Compute the alignment requirement of a C type.
public func typeAlign(_ type: CType) -> Int {
    switch type {
    case .void: return 1
    case .bool, .char: return 1
    case .short: return 2
    case .int, .enumType, .float: return 4
    case .long, .double, .longDouble, .pointer, .function: return 8
    case .array(let elem, _), .vla(let elem): return typeAlign(elem)
    case .structType(let r): return r.members.map { typeAlign($0.type) }.max() ?? 1
    case .unionType(let r): return r.members.map { typeAlign($0.type) }.max() ?? 1
    }
}

/// Round `value` up to the nearest multiple of `alignment`.
public func alignUp(_ value: Int32, to alignment: Int32) -> Int32 {
    guard alignment > 0 else { return value }
    return (value + alignment - 1) / alignment * alignment
}
