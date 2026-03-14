public struct SyntaxTranslationUnit: Sendable {
    public let declarations: [SyntaxDeclaration]

    public init(declarations: [SyntaxDeclaration]) {
        self.declarations = declarations
    }
}

public enum SyntaxDeclaration: Sendable {
    case function(SyntaxFunction)
    case variable(SyntaxGlobalVariable)
}

public struct SyntaxFunction: Sendable {
    public let name: String
    public let type: SyntaxType
    public let isDefinition: Bool
    public let isStatic: Bool
    public let isInline: Bool
    public let isLive: Bool
    public let isRoot: Bool
    public let params: [SyntaxLocalVariable]
    public let locals: [SyntaxLocalVariable]
    public let body: SyntaxStmt?
    public let stackSize: Int
    public let vaArea: SyntaxVariableRef?
    public let allocaBottom: SyntaxVariableRef?
    public let loc: SourceLocation

    public init(name: String, type: SyntaxType, isDefinition: Bool,
                isStatic: Bool, isInline: Bool, isLive: Bool, isRoot: Bool,
                params: [SyntaxLocalVariable], locals: [SyntaxLocalVariable],
                body: SyntaxStmt?, stackSize: Int,
                vaArea: SyntaxVariableRef?, allocaBottom: SyntaxVariableRef?,
                loc: SourceLocation) {
        self.name = name
        self.type = type
        self.isDefinition = isDefinition
        self.isStatic = isStatic
        self.isInline = isInline
        self.isLive = isLive
        self.isRoot = isRoot
        self.params = params
        self.locals = locals
        self.body = body
        self.stackSize = stackSize
        self.vaArea = vaArea
        self.allocaBottom = allocaBottom
        self.loc = loc
    }
}

public struct SyntaxLocalVariable: Sendable {
    public let name: String
    public let type: SyntaxType
    public let offset: Int
    public let align: Int
    public let id: Int

    public init(name: String, type: SyntaxType, offset: Int, align: Int, id: Int) {
        self.name = name
        self.type = type
        self.offset = offset
        self.align = align
        self.id = id
    }
}

public struct SyntaxGlobalVariable: Sendable {
    public let name: String
    public let type: SyntaxType
    public let isDefinition: Bool
    public let isStatic: Bool
    public let isTentative: Bool
    public let isTLS: Bool
    public let align: Int
    public let initData: [UInt8]?
    public let relocations: [SyntaxRelocation]
    public let loc: SourceLocation

    public init(name: String, type: SyntaxType, isDefinition: Bool,
                isStatic: Bool, isTentative: Bool, isTLS: Bool, align: Int,
                initData: [UInt8]?, relocations: [SyntaxRelocation],
                loc: SourceLocation) {
        self.name = name
        self.type = type
        self.isDefinition = isDefinition
        self.isStatic = isStatic
        self.isTentative = isTentative
        self.isTLS = isTLS
        self.align = align
        self.initData = initData
        self.relocations = relocations
        self.loc = loc
    }
}

public struct SyntaxRelocation: Sendable {
    public let offset: Int
    public let label: String
    public let addend: Int64

    public init(offset: Int, label: String, addend: Int64) {
        self.offset = offset
        self.label = label
        self.addend = addend
    }
}
