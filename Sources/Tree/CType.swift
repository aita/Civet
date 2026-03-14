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
    /// Bit-field width in bits. `nil` for ordinary (non-bit-field) members.
    public let bitWidth: Int?

    public init(name: String?, type: CType, bitWidth: Int? = nil) {
        self.name = name
        self.type = type
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
}
