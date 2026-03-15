import Syntax

/// Root node of a parsed C translation unit.
public struct CTranslationUnit: Sendable {
    public let functions: [CFunction]
    public let globals: [CVar]

    public init(functions: [CFunction], globals: [CVar]) {
        self.functions = functions
        self.globals = globals
    }
}

/// A function definition or forward declaration.
///
/// Implementation details removed from `SyntaxFunction`:
/// `stackSize`, `vaArea`, `allocaBottom`, `isLive`, `isRoot`.
public struct CFunction: Sendable {
    public let name: String
    public let returnType: CType
    public let params: [CVar]
    public let locals: [CVar]
    /// `nil` for forward declarations.
    public let body: CStmt?
    public let isStatic: Bool
    public let isInline: Bool
    public let loc: SourceLocation

    public init(name: String, returnType: CType, params: [CVar], locals: [CVar],
                body: CStmt?, isStatic: Bool, isInline: Bool, loc: SourceLocation) {
        self.name = name
        self.returnType = returnType
        self.params = params
        self.locals = locals
        self.body = body
        self.isStatic = isStatic
        self.isInline = isInline
        self.loc = loc
    }
}

/// Storage class of a variable.
public enum CStorage: Sendable {
    /// Local variable or parameter. `id` is unique within the translation unit.
    case local(id: Int)
    /// Global variable. `initData` is `nil` for zero-initialized or declared-only variables.
    case global(isStatic: Bool, isTLS: Bool, isDefinition: Bool, isTentative: Bool, initData: [UInt8]?, relocations: [CRelocation])
}

/// A relocation entry for a global variable's initializer data.
public struct CRelocation: Sendable {
    /// Byte offset within the initData where the relocation applies.
    public let offset: Int
    /// Symbol name to reference.
    public let label: String
    /// Addend to add to the symbol address.
    public let addend: Int64

    public init(offset: Int, label: String, addend: Int64) {
        self.offset = offset
        self.label = label
        self.addend = addend
    }
}

/// A variable — local, parameter, or global.
///
/// Replaces the separate `CLocal` / `CGlobal` types. Storage-specific
/// attributes are carried by `CStorage`; `name` and `type` are shared.
public struct CVar: Sendable {
    public let name: String
    public let type: CType
    public let storage: CStorage
    /// Source location. Typically `nil` for synthesised temporaries.
    public let loc: SourceLocation?
    /// Pre-computed stack offset from the C parser (chibicc), if available.
    /// Negative value = offset below rbp.
    public let stackOffset: Int?
    /// Alignment override from `_Alignas`. `nil` means use natural type alignment.
    public let align: Int?

    public init(name: String, type: CType, storage: CStorage, loc: SourceLocation? = nil,
                stackOffset: Int? = nil, align: Int? = nil) {
        self.name = name
        self.type = type
        self.storage = storage
        self.loc = loc
        self.stackOffset = stackOffset
        self.align = align
    }
}
