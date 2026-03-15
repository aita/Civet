public indirect enum SyntaxExpr: Sendable {
    case nullExpr(type: SyntaxType, loc: SourceLocation)
    case intLiteral(value: Int64, type: SyntaxType, loc: SourceLocation)
    case floatLiteral(value: Double, type: SyntaxType, loc: SourceLocation)
    case variable(ref: SyntaxVariableRef, type: SyntaxType, loc: SourceLocation)
    case vlaPtr(ref: SyntaxVariableRef, type: SyntaxType, loc: SourceLocation)
    case binary(op: BinaryOp, lhs: SyntaxExpr, rhs: SyntaxExpr,
                type: SyntaxType, loc: SourceLocation)
    case unary(op: UnaryOp, operand: SyntaxExpr,
               type: SyntaxType, loc: SourceLocation)
    case logical(op: LogicalOp, lhs: SyntaxExpr, rhs: SyntaxExpr,
                 type: SyntaxType, loc: SourceLocation)
    case addressOf(operand: SyntaxExpr, type: SyntaxType, loc: SourceLocation)
    case deref(operand: SyntaxExpr, type: SyntaxType, loc: SourceLocation)
    case member(expr: SyntaxExpr, member: SyntaxMember,
                type: SyntaxType, loc: SourceLocation)
    case assign(lhs: SyntaxExpr, rhs: SyntaxExpr,
                type: SyntaxType, loc: SourceLocation)
    case ternary(cond: SyntaxExpr, then: SyntaxExpr, els: SyntaxExpr,
                 type: SyntaxType, loc: SourceLocation)
    case comma(lhs: SyntaxExpr, rhs: SyntaxExpr,
               type: SyntaxType, loc: SourceLocation)
    case cast(operand: SyntaxExpr, toType: SyntaxType,
              type: SyntaxType, loc: SourceLocation)
    case call(callee: SyntaxExpr, args: [SyntaxExpr], funcType: SyntaxType,
              returnBuffer: SyntaxVariableRef?, type: SyntaxType, loc: SourceLocation)
    case stmtExpr(body: [SyntaxStmt], type: SyntaxType, loc: SourceLocation)
    case labelValue(label: String, uniqueLabel: String,
                    type: SyntaxType, loc: SourceLocation)
    case cas(addr: SyntaxExpr, old: SyntaxExpr, new: SyntaxExpr,
             type: SyntaxType, loc: SourceLocation)
    case exchange(addr: SyntaxExpr, value: SyntaxExpr,
                  type: SyntaxType, loc: SourceLocation)
    case memzero(variable: SyntaxVariableRef, type: SyntaxType, loc: SourceLocation)
    /// Compound assignment: `x += y`, `x -= y`, etc. `op` is the underlying
    /// binary operator (`.add` for `+=`, `.sub` for `-=`, etc.).
    case compoundAssign(op: BinaryOp, lhs: SyntaxExpr, rhs: SyntaxExpr,
                        type: SyntaxType, loc: SourceLocation)
    /// Pre-increment/decrement: `++x` (addend=1) or `--x` (addend=-1).
    /// Result is the new value.
    case preIncDec(addend: Int, operand: SyntaxExpr,
                   type: SyntaxType, loc: SourceLocation)
    /// Post-increment/decrement: `x++` (addend=1) or `x--` (addend=-1).
    /// Result is the old value.
    case postIncDec(addend: Int, operand: SyntaxExpr,
                    type: SyntaxType, loc: SourceLocation)
}

public enum BinaryOp: Sendable {
    case add, sub, mul, div, mod
    case bitAnd, bitOr, bitXor, shl, shr
    case eq, ne, lt, le
}

public enum UnaryOp: Sendable {
    case neg, logNot, bitNot
}

public enum LogicalOp: Sendable {
    case and, or
}

public struct SyntaxVariableRef: Sendable {
    public let name: String
    public let isLocal: Bool
    public let id: Int

    public init(name: String, isLocal: Bool, id: Int) {
        self.name = name
        self.isLocal = isLocal
        self.id = id
    }
}
