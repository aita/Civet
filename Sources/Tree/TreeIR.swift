import Syntax

// MARK: - Declarations

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

// MARK: - Statements

/// Minimal C statement node. Control flow is reduced to `if` and `goto` only.
///
/// The following `SyntaxStmt` cases are lowered by `SyntaxConverter`:
/// - `for`     → `block` of `[init, label(cond), if(!cond, goto(end)), body,
///                            label(continue), inc, goto(cond), label(end)]`
/// - `doWhile` → `block` of `[label(start), body, label(continue),
///                            if(cond, goto(start)), label(end)]`
/// - `switch`  → chain of `if` + `goto` for dispatch, then body with labels
/// - `case`    → `label` (dispatch target)
/// - `memzero` → `assign(var, 0)`
/// - `break` / `continue` → already `goto` in `SyntaxStmt`
public indirect enum CStmt: Sendable {
    /// Evaluate an expression and discard the result.
    case expr(CExpr)
    /// Assignment statement. `lhs` must be an lvalue (variable / deref / member).
    case assign(lhs: CExpr, rhs: CExpr)
    case `return`(CExpr?)
    case block([CStmt])
    /// Conditional branch. The only structured control-flow construct.
    case `if`(cond: CExpr, then: CStmt, else: CStmt?)
    /// Label definition (jump target). Not attached to the following statement.
    case label(String)
    /// Unconditional jump.
    case goto(String)
    /// GNU extension: computed goto `goto *expr`.
    case computedGoto(CExpr)
    /// Inline assembly.
    case asm(String)
}

// MARK: - Expressions

/// Minimal C expression node.
///
/// The following `SyntaxExpr` cases are lowered away by `SyntaxConverter`:
/// - `null`       → `intLiteral(0, ...)`
/// - `ternary`    → `if` statement + temporary variable
/// - `logical`    → `if` statement chain
/// - `comma`      → sequential statements
/// - `stmtExpr`   → inlined block statement
/// - `vlaPtr`     → dropped (VLA internal, codegen-only)
/// - `memzero`    → `CStmt.assign(var, 0)`
/// - `returnBuffer` (on `call`) → dropped (codegen-only)
/// - `logNot` (on `unary`) → `binary(.eq, x, 0)`
/// - `compoundAssign` → read-modify-write via temp pointer
/// - `preIncDec`  → compound assign + return new value
/// - `postIncDec` → save old value + compound assign + return old value
/// - `assign`     → `CStmt.assign` (assignment is a statement, not an expression)
public indirect enum CExpr: Sendable {
    case intLiteral(Int64, type: CType)
    case floatLiteral(Double, type: CType)
    /// Reference to a local or global variable. `id` is unique within the translation unit.
    case variable(name: String, type: CType, id: Int)
    case binary(BinaryOp, CExpr, CExpr, type: CType)
    case unary(UnaryOp, CExpr, type: CType)
    case addressOf(CExpr, type: CType)
    case deref(CExpr, type: CType)
    case member(CExpr, name: String, offset: Int32, type: CType)
    case cast(CExpr, to: CType)
    case call(callee: CExpr, args: [CExpr], type: CType)
    /// GNU extension: label address `&&label`.
    case labelAddress(String, type: CType)
    /// Atomic compare-and-swap.
    case cas(addr: CExpr, old: CExpr, new: CExpr, type: CType)
    /// Atomic exchange (fetch-and-store).
    case exchange(addr: CExpr, value: CExpr, type: CType)

    /// The type of this expression.
    public var type: CType {
        switch self {
        case .intLiteral(_, let t):             return t
        case .floatLiteral(_, let t):           return t
        case .variable(_, let t, _):            return t
        case .binary(_, _, _, let t):           return t
        case .unary(_, _, let t):               return t
        case .addressOf(_, let t):              return t
        case .deref(_, let t):                  return t
        case .member(_, _, _, let t):             return t
        case .cast(_, let t):                   return t
        case .call(_, _, let t):                return t
        case .labelAddress(_, let t):           return t
        case .cas(_, _, _, let t):              return t
        case .exchange(_, _, let t):            return t
        }
    }
}

/// Binary operators — shared with Syntax module (identical 14-case enum).
public typealias BinaryOp = Syntax.BinaryOp

/// Unary operators. Logical-not (`!`) is lowered to `binary(.eq, x, 0)`.
public enum UnaryOp: Sendable {
    case neg    // arithmetic negation `-x`
    case bitNot // bitwise complement `~x`
}
