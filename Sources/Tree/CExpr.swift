import Syntax

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
/// - Compound assignments and increment/decrement → already lowered to
///   `CStmt.assign(lhs, binary(...))` by chibicc before this stage.
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
    case member(CExpr, name: String, type: CType)
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
        case .member(_, _, let t):              return t
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
