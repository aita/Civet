public struct SyntaxMember: Sendable {
    public let name: String?
    public let type: SyntaxType
    public let index: Int
    public let offset: Int
    public let align: Int
    public let bitfield: BitfieldInfo?

    public struct BitfieldInfo: Sendable {
        public let bitOffset: Int
        public let bitWidth: Int

        public init(bitOffset: Int, bitWidth: Int) {
            self.bitOffset = bitOffset
            self.bitWidth = bitWidth
        }
    }

    public init(name: String?, type: SyntaxType, index: Int, offset: Int,
                align: Int, bitfield: BitfieldInfo?) {
        self.name = name
        self.type = type
        self.index = index
        self.offset = offset
        self.align = align
        self.bitfield = bitfield
    }
}

public final class SyntaxType: Sendable {
    public nonisolated(unsafe) var kind: Kind
    public let size: Int
    public let align: Int
    public let isAtomic: Bool
    public let name: String?

    public enum Kind: Sendable {
        case void
        case bool
        case char(isUnsigned: Bool)
        case short(isUnsigned: Bool)
        case int(isUnsigned: Bool)
        case long(isUnsigned: Bool)
        case float
        case double
        case longDouble
        case `enum`
        case pointer(pointee: SyntaxType)
        case array(element: SyntaxType, length: Int)
        case vla(element: SyntaxType)
        case `struct`(members: [SyntaxMember], isFlexible: Bool, isPacked: Bool)
        case union(members: [SyntaxMember])
        case function(returnType: SyntaxType, params: [SyntaxType], isVariadic: Bool)
    }

    public init(kind: Kind, size: Int, align: Int,
                isAtomic: Bool = false, name: String? = nil) {
        self.kind = kind
        self.size = size
        self.align = align
        self.isAtomic = isAtomic
        self.name = name
    }
}
