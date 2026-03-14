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
