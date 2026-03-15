/// Struct or union type definition. Reference type to handle recursive C types
/// (e.g. a struct containing a pointer to itself). `members` is filled in after
/// the `CRecordType` instance is cached by `SyntaxConverter`.
public final class CRecordType: @unchecked Sendable {
    public let tag: String?
    public var members: [CStructMember]

    public init(tag: String?, members: [CStructMember] = []) {
        self.tag = tag
        self.members = members
    }
}

/// A single field of a struct or union.
public struct CStructMember: Sendable {
    /// Field name. `nil` for anonymous fields.
    public let name: String?
    public let type: CType
    /// Byte offset of this member within the struct (from chibicc layout).
    public let offset: Int
    /// Bit-field offset within the containing storage unit. `nil` for non-bit-fields.
    public let bitOffset: Int?
    /// Bit-field width in bits. `nil` for ordinary (non-bit-field) members.
    public let bitWidth: Int?

    public init(name: String?, type: CType, offset: Int = 0, bitOffset: Int? = nil, bitWidth: Int? = nil) {
        self.name = name
        self.type = type
        self.offset = offset
        self.bitOffset = bitOffset
        self.bitWidth = bitWidth
    }
}

/// Semantic representation of a C type.
///
/// Unlike `SyntaxType`, implementation details (`size`, `align`, `isAtomic`) are
/// omitted. Recursive struct/union types are broken by `CRecordType` (reference type).
public indirect enum CType: Sendable {
    case void
    case bool
    case char(signed: Bool)
    case short(signed: Bool)
    case int(signed: Bool)
    case long(signed: Bool)
    case float
    case double
    case longDouble
    /// A C `enum` type. Enumeration constants are represented as integers.
    case enumType
    case pointer(CType)
    case array(element: CType, count: Int)
    /// Variable-length array (VLA).
    case vla(element: CType)
    case function(returnType: CType, params: [CType], isVariadic: Bool)
    case structType(CRecordType)
    case unionType(CRecordType)

    // MARK: - Type layout

    /// Byte size of this C type.
    public var size: Int {
        switch self {
        case .void: return 0
        case .bool, .char: return 1
        case .short: return 2
        case .int, .enumType, .float: return 4
        case .long, .double, .longDouble, .pointer, .function: return 8
        case .array(let elem, let count): return elem.size * count
        case .vla: return 8
        case .structType(let r):
            var offset = 0
            for m in r.members {
                let a = m.type.align
                offset = (offset + a - 1) / a * a
                offset += m.type.size
            }
            let structAlign = r.members.map { $0.type.align }.max() ?? 1
            return (offset + structAlign - 1) / structAlign * structAlign
        case .unionType(let r):
            return r.members.map { $0.type.size }.max() ?? 0
        }
    }

    /// Alignment requirement of this C type.
    public var align: Int {
        switch self {
        case .void: return 1
        case .bool, .char: return 1
        case .short: return 2
        case .int, .enumType, .float: return 4
        case .long, .double, .longDouble, .pointer, .function: return 8
        case .array(let elem, _), .vla(let elem): return elem.align
        case .structType(let r): return r.members.map { $0.type.align }.max() ?? 1
        case .unionType(let r): return r.members.map { $0.type.align }.max() ?? 1
        }
    }
}
