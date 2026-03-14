public indirect enum SyntaxStmt: Sendable {
    case expr(SyntaxExpr, loc: SourceLocation)
    case `return`(value: SyntaxExpr?, loc: SourceLocation)
    case block([SyntaxStmt], loc: SourceLocation)
    case `if`(cond: SyntaxExpr, then: SyntaxStmt, else: SyntaxStmt?,
              loc: SourceLocation)
    case `for`(init: SyntaxStmt?, cond: SyntaxExpr?, inc: SyntaxExpr?,
               body: SyntaxStmt, breakLabel: String?, continueLabel: String?,
               loc: SourceLocation)
    case doWhile(body: SyntaxStmt, cond: SyntaxExpr,
                 breakLabel: String?, continueLabel: String?,
                 loc: SourceLocation)
    case `switch`(cond: SyntaxExpr, body: SyntaxStmt, cases: [CaseInfo],
                  defaultLabel: String?, breakLabel: String?,
                  loc: SourceLocation)
    case `case`(begin: Int64, end: Int64, label: String, body: SyntaxStmt,
                loc: SourceLocation)
    case goto(uniqueLabel: String, loc: SourceLocation)
    case gotoExpr(target: SyntaxExpr, loc: SourceLocation)
    case label(name: String, uniqueLabel: String, body: SyntaxStmt,
               loc: SourceLocation)
    case memzero(variable: SyntaxVariableRef, type: SyntaxType, loc: SourceLocation)
    case asm(String, loc: SourceLocation)
}

public struct CaseInfo: Sendable {
    public let begin: Int64
    public let end: Int64
    public let label: String

    public init(begin: Int64, end: Int64, label: String) {
        self.begin = begin
        self.end = end
        self.label = label
    }
}
