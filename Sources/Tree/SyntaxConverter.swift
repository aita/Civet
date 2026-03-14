import Syntax

/// Converts a `SyntaxTranslationUnit` into a simplified `CTranslationUnit`.
///
/// Key transformations:
/// - `for` / `doWhile` / `switch` → `if` + `goto`
/// - `ternary` → temp variable + `if` (correct semantics: only one branch evaluated)
/// - `logical (&&/||)` → short-circuit `if` chain + temp variable
/// - `comma` → lhs emitted as statement, rhs returned as value
/// - `stmtExpr` → statements inlined into enclosing block
/// - `unary logNot (!x)` → `x == 0`
/// - `null` → `intLiteral(0)`
/// - `vlaPtr` → plain variable reference
/// - `memzero` (expr/stmt) → `assign(var, 0)`
public final class SyntaxConverter {

    // MARK: - Caches

    private var typeCache:   [ObjectIdentifier: CType]       = [:]
    private var recordCache: [ObjectIdentifier: CRecordType] = [:]

    // MARK: - Synthetic variable / label generation

    /// Synthetic temporaries introduced during expression lowering.
    /// Reset at the start of each function.
    private var synthLocals: [CVar] = []

    private var genCounter = 0

    /// Returns a fresh label string.
    private func freshLabel(_ hint: String) -> String {
        defer { genCounter += 1 }
        return "__\(hint)_\(genCounter)"
    }

    /// Allocates a synthetic local variable and returns a reference expression.
    /// Uses positive IDs in a high range (50000+) so they participate in SSA
    /// construction alongside source-level variables (which use small positive IDs).
    private func freshTempVar(type: CType) -> CExpr {
        defer { genCounter += 1 }
        let name = "__tmp_\(genCounter)"
        let id   = 50_000 + genCounter
        synthLocals.append(CVar(name: name, type: type, storage: .local(id: id)))
        return .variable(name: name, type: type, id: id)
    }

    // MARK: - Public API

    public init() {}

    public func convert(_ unit: SyntaxTranslationUnit) -> CTranslationUnit {
        var functions: [CFunction] = []
        var globals:   [CVar]      = []
        for decl in unit.declarations {
            switch decl {
            case .function(let f): functions.append(convertFunction(f))
            case .variable(let g): globals.append(convertGlobal(g))
            }
        }
        return CTranslationUnit(functions: functions, globals: globals)
    }

    // MARK: - Type conversion

    public func convertType(_ ty: SyntaxType) -> CType {
        let key = ObjectIdentifier(ty)
        if let cached = typeCache[key] { return cached }

        switch ty.kind {
        case .void:             return cache(.void,              for: key)
        case .bool:             return cache(.bool,              for: key)
        case .char(let u):      return cache(.char(signed: !u),  for: key)
        case .short(let u):     return cache(.short(signed: !u), for: key)
        case .int(let u):       return cache(.int(signed: !u),   for: key)
        case .long(let u):      return cache(.long(signed: !u),  for: key)
        case .float:            return cache(.float,             for: key)
        case .double:           return cache(.double,            for: key)
        case .longDouble:       return cache(.longDouble,        for: key)
        case .enum:             return cache(.enumType,          for: key)

        case .pointer(let pointee):
            return cache(.pointer(convertType(pointee)), for: key)

        case .array(let elem, let len):
            return cache(.array(element: convertType(elem), count: len), for: key)

        case .vla(let elem):
            return cache(.vla(element: convertType(elem)), for: key)

        case .function(let ret, let params, let variadic):
            return cache(.function(
                returnType: convertType(ret),
                params: params.map { convertType($0) },
                isVariadic: variadic), for: key)

        case .struct(let members, _, _):
            // Cache the CRecordType *before* converting members to break recursive cycles.
            let record = cachedRecord(for: key, tag: ty.name)
            typeCache[key] = .structType(record)
            record.members = members.map { convertMember($0) }
            return .structType(record)

        case .union(let members):
            let record = cachedRecord(for: key, tag: ty.name)
            typeCache[key] = .unionType(record)
            record.members = members.map { convertMember($0) }
            return .unionType(record)
        }
    }

    private func convertMember(_ m: SyntaxMember) -> CStructMember {
        CStructMember(name: m.name, type: convertType(m.type), bitWidth: m.bitfield?.bitWidth)
    }

    private func cache(_ type: CType, for key: ObjectIdentifier) -> CType {
        typeCache[key] = type; return type
    }

    private func cachedRecord(for key: ObjectIdentifier, tag: String?) -> CRecordType {
        if let r = recordCache[key] { return r }
        let r = CRecordType(tag: tag)
        recordCache[key] = r
        return r
    }

    // MARK: - Declaration conversion

    public func convertFunction(_ f: SyntaxFunction) -> CFunction {
        synthLocals = []

        let params    = f.params.map { CVar(name: $0.name, type: convertType($0.type), storage: .local(id: $0.id), stackOffset: $0.offset) }
        let srcLocals = f.locals.map { CVar(name: $0.name, type: convertType($0.type), storage: .local(id: $0.id), stackOffset: $0.offset) }
        let body      = f.body.map { convertStmt($0) }

        let retType: CType
        if case .function(let r, _, _) = f.type.kind { retType = convertType(r) }
        else { retType = .void }

        return CFunction(
            name:       f.name,
            returnType: retType,
            params:     params,
            locals:     srcLocals + synthLocals,  // include synthesised temps
            body:       body,
            isStatic:   f.isStatic,
            isInline:   f.isInline,
            loc:        f.loc)
    }

    public func convertGlobal(_ g: SyntaxGlobalVariable) -> CVar {
        CVar(
            name: g.name,
            type: convertType(g.type),
            storage: .global(
                isStatic:     g.isStatic,
                isTLS:        g.isTLS,
                isDefinition: g.isDefinition,
                isTentative:  g.isTentative,
                initData:     g.initData),
            loc: g.loc)
    }

    // MARK: - Statement conversion

    public func convertStmt(_ node: SyntaxStmt) -> CStmt {
        switch node {

        case .expr(let e, _):
            var pre: [CStmt] = []
            let expr = convertExpr(e, into: &pre)
            return withPre(pre, .expr(expr))

        case .return(let val, _):
            guard let val else { return .return(nil) }
            var pre: [CStmt] = []
            let expr = convertExpr(val, into: &pre)
            return withPre(pre, .return(expr))

        case .block(let stmts, _):
            return .block(stmts.flatMap { flattenStmt(convertStmt($0)) })

        case .if(let cond, let then, let els, _):
            var pre: [CStmt] = []
            let condExpr = convertExpr(cond, into: &pre)
            let ifStmt = CStmt.if(
                cond: condExpr,
                then: convertStmt(then),
                else: els.map { convertStmt($0) })
            return withPre(pre, ifStmt)

        case .for(let init_, let cond, let inc, let body,
                  let breakLabel, let continueLabel, _):
            return lowerFor(init: init_, cond: cond, inc: inc, body: body,
                            breakLabel: breakLabel, continueLabel: continueLabel)

        case .doWhile(let body, let cond, let breakLabel, let continueLabel, _):
            return lowerDoWhile(body: body, cond: cond,
                                breakLabel: breakLabel, continueLabel: continueLabel)

        case .switch(let cond, let body, let cases, let defaultLabel, let breakLabel, _):
            return lowerSwitch(cond: cond, body: body, cases: cases,
                               defaultLabel: defaultLabel, breakLabel: breakLabel)

        case .case(_, _, let label, let body, _):
            // The dispatch jump is produced by lowerSwitch; emit only the label.
            return .block([.label(label), convertStmt(body)])

        case .goto(let label, _):
            return .goto(label)

        case .gotoExpr(let target, _):
            var pre: [CStmt] = []
            let expr = convertExpr(target, into: &pre)
            return withPre(pre, .computedGoto(expr))

        case .label(_, let uniqueLabel, let body, _):
            return .block([.label(uniqueLabel), convertStmt(body)])

        case .memzero(let ref, let ty, _):
            let cty = convertType(ty)
            let v = CExpr.variable(name: ref.name, type: cty, id: ref.id)
            return .assign(lhs: v, rhs: .intLiteral(0, type: cty))

        case .asm(let text, _):
            return .asm(text)
        }
    }

    // MARK: - Loop / switch lowering

    /// ```
    /// init
    /// condLabel:
    ///   condPre...
    ///   if (!cond) goto endLabel
    ///   body
    /// continueLabel:
    ///   incPre...
    ///   inc
    ///   goto condLabel
    /// endLabel:
    /// ```
    private func lowerFor(
        init initStmt: SyntaxStmt?,
        cond: SyntaxExpr?,
        inc:  SyntaxExpr?,
        body: SyntaxStmt,
        breakLabel:    String?,
        continueLabel: String?
    ) -> CStmt {
        let condLabel = freshLabel("cond")
        let endLabel  = breakLabel    ?? freshLabel("end")
        let contLabel = continueLabel ?? freshLabel("cont")

        var s: [CStmt] = []
        if let init_ = initStmt { s.append(convertStmt(init_)) }
        s.append(.label(condLabel))
        if let c = cond {
            var pre: [CStmt] = []
            let cv = convertExpr(c, into: &pre)
            // Condition pre-statements must execute on every iteration.
            s.append(contentsOf: pre)
            s.append(.if(cond: isZero(cv), then: .goto(endLabel), else: nil))
        }
        s.append(convertStmt(body))
        s.append(.label(contLabel))
        if let i = inc {
            var pre: [CStmt] = []
            let iv = convertExpr(i, into: &pre)
            s.append(contentsOf: pre)
            s.append(.expr(iv))
        }
        s.append(.goto(condLabel))
        s.append(.label(endLabel))
        return .block(s)
    }

    /// ```
    /// startLabel:
    ///   body
    /// continueLabel:
    ///   condPre...
    ///   if (cond) goto startLabel
    /// endLabel:
    /// ```
    private func lowerDoWhile(
        body: SyntaxStmt,
        cond: SyntaxExpr,
        breakLabel:    String?,
        continueLabel: String?
    ) -> CStmt {
        let startLabel = freshLabel("do")
        let endLabel   = breakLabel    ?? freshLabel("end")
        let contLabel  = continueLabel ?? freshLabel("cont")

        var pre: [CStmt] = []
        let cv = convertExpr(cond, into: &pre)

        return .block([
            .label(startLabel),
            convertStmt(body),
            .label(contLabel),
        ] + pre + [
            .if(cond: isNonZero(cv), then: .goto(startLabel), else: nil),
            .label(endLabel),
        ])
    }

    /// Dispatch: one `if-goto` per case range, then `goto default/end`, then body.
    /// The switch condition is stored in a temp to avoid repeated evaluation.
    private func lowerSwitch(
        cond:         SyntaxExpr,
        body:         SyntaxStmt,
        cases:        [CaseInfo],
        defaultLabel: String?,
        breakLabel:   String?
    ) -> CStmt {
        let endLabel = breakLabel ?? freshLabel("end")

        var pre: [CStmt] = []
        let rawCv = convertExpr(cond, into: &pre)

        // Store cond in a temp so each case check re-reads a stable value.
        let cvType = rawCv.type
        let cv     = freshTempVar(type: cvType)
        pre.append(.assign(lhs: cv, rhs: rawCv))

        var s = pre
        let i1 = CType.int(signed: true)
        for info in cases {
            let check: CExpr
            if info.begin == info.end {
                check = .binary(.eq, cv, .intLiteral(info.begin, type: cvType), type: i1)
            } else {
                let lo = CExpr.binary(.le, .intLiteral(info.begin, type: cvType), cv, type: i1)
                let hi = CExpr.binary(.le, cv, .intLiteral(info.end,   type: cvType), type: i1)
                check  = .binary(.bitAnd, lo, hi, type: i1)
            }
            s.append(.if(cond: check, then: .goto(info.label), else: nil))
        }
        s.append(.goto(defaultLabel ?? endLabel))
        s.append(convertStmt(body))
        s.append(.label(endLabel))
        return .block(s)
    }

    // MARK: - Expression conversion
    //
    // `convertExpr(_:into:)` converts a `SyntaxExpr` and appends any required
    // pre-statements (e.g. from ternary / logical lowering) into `buf`.
    // The returned `CExpr` must be evaluated *after* `buf` has been executed.

    public func convertExpr(_ node: SyntaxExpr, into buf: inout [CStmt]) -> CExpr {
        switch node {

        // ── Literals ──────────────────────────────────────────────────────────

        case .nullExpr(let ty, _):
            return .intLiteral(0, type: convertType(ty))

        case .intLiteral(let v, let ty, _):
            return .intLiteral(v, type: convertType(ty))

        case .floatLiteral(let v, let ty, _):
            return .floatLiteral(v, type: convertType(ty))

        // ── Variables ─────────────────────────────────────────────────────────

        case .variable(let ref, let ty, _):
            return .variable(name: ref.name, type: convertType(ty), id: ref.id)

        case .vlaPtr(let ref, let ty, _):
            // VLA size pointer: treat as a plain variable reference.
            return .variable(name: ref.name, type: convertType(ty), id: ref.id)

        // ── Arithmetic / bitwise ──────────────────────────────────────────────

        case .binary(let op, let lhs, let rhs, let ty, _):
            let l = convertExpr(lhs, into: &buf)
            let r = convertExpr(rhs, into: &buf)
            return .binary(op, l, r, type: convertType(ty))

        case .unary(let op, let operand, let ty, _):
            let v   = convertExpr(operand, into: &buf)
            let cty = convertType(ty)
            switch op {
            case .neg:    return .unary(.neg,    v, type: cty)
            case .bitNot: return .unary(.bitNot, v, type: cty)
            case .logNot: return .binary(.eq, v, .intLiteral(0, type: v.type), type: cty)
            }

        // ── Logical (short-circuit) ────────────────────────────────────────────
        //
        // `a && b`:
        //   tmp = 0
        //   if (a != 0) { if (b != 0) { tmp = 1 } }
        //
        // `a || b`:
        //   tmp = 1
        //   if (a == 0) { if (b == 0) { tmp = 0 } }

        case .logical(let op, let lhs, let rhs, let ty, _):
            let cty  = convertType(ty)
            let tmp  = freshTempVar(type: cty)
            let zero = CExpr.intLiteral(0, type: cty)
            let one  = CExpr.intLiteral(1, type: cty)

            let lhsExpr = convertExpr(lhs, into: &buf)

            var rhsBuf: [CStmt] = []
            let rhsExpr = convertExpr(rhs, into: &rhsBuf)

            switch op {
            case .and:
                // init tmp = 0; if lhs { [rhs...]; if rhs { tmp = 1 } }
                buf.append(.assign(lhs: tmp, rhs: zero))
                let setTrue  = CStmt.assign(lhs: tmp, rhs: one)
                let innerIf  = CStmt.if(cond: isNonZero(rhsExpr), then: setTrue, else: nil)
                let outerIf  = CStmt.if(cond: isNonZero(lhsExpr),
                                        then: .block(rhsBuf + [innerIf]), else: nil)
                buf.append(outerIf)

            case .or:
                // init tmp = 1; if !lhs { [rhs...]; if !rhs { tmp = 0 } }
                buf.append(.assign(lhs: tmp, rhs: one))
                let setFalse = CStmt.assign(lhs: tmp, rhs: zero)
                let innerIf  = CStmt.if(cond: isZero(rhsExpr), then: setFalse, else: nil)
                let outerIf  = CStmt.if(cond: isZero(lhsExpr),
                                        then: .block(rhsBuf + [innerIf]), else: nil)
                buf.append(outerIf)
            }
            return tmp

        // ── Ternary ────────────────────────────────────────────────────────────
        //
        // `cond ? then : els`:
        //   (evaluate cond pre-stmts)
        //   if (cond) { (then pre-stmts); tmp = then }
        //   else      { (els  pre-stmts); tmp = els  }

        case .ternary(let cond, let then, let els, let ty, _):
            let cty     = convertType(ty)
            let tmp     = freshTempVar(type: cty)
            let condExpr = convertExpr(cond, into: &buf)

            var thenBuf: [CStmt] = []
            let thenExpr = convertExpr(then, into: &thenBuf)
            thenBuf.append(.assign(lhs: tmp, rhs: thenExpr))

            var elsBuf: [CStmt] = []
            let elsExpr = convertExpr(els, into: &elsBuf)
            elsBuf.append(.assign(lhs: tmp, rhs: elsExpr))

            buf.append(.if(cond: isNonZero(condExpr),
                           then: .block(thenBuf),
                           else: .block(elsBuf)))
            return tmp

        // ── Comma ──────────────────────────────────────────────────────────────
        //
        // `lhs, rhs`: evaluate lhs for side effects, return rhs value.

        case .comma(let lhs, let rhs, _, _):
            let lhsExpr = convertExpr(lhs, into: &buf)
            buf.append(.expr(lhsExpr))
            return convertExpr(rhs, into: &buf)

        // ── Memory / pointer ──────────────────────────────────────────────────

        case .addressOf(let operand, let ty, _):
            return .addressOf(convertExpr(operand, into: &buf), type: convertType(ty))

        case .deref(let operand, let ty, _):
            return .deref(convertExpr(operand, into: &buf), type: convertType(ty))

        case .member(let expr, let member, let ty, _):
            return .member(convertExpr(expr, into: &buf),
                           name: member.name ?? "",
                           type: convertType(ty))

        // ── Assignment ────────────────────────────────────────────────────────
        //
        // C's `x = y` is an expression, but Tree treats assignment as a
        // statement. Emit `assign(lhs, rhs)` into `buf` and return `lhs`
        // so that the value is still available (e.g. `a = b = c`).

        case .assign(let lhs, let rhs, _, _):
            let l = convertExpr(lhs, into: &buf)
            let r = convertExpr(rhs, into: &buf)
            buf.append(.assign(lhs: l, rhs: r))
            return l

        // ── Cast ──────────────────────────────────────────────────────────────

        case .cast(let operand, let toType, _, _):
            return .cast(convertExpr(operand, into: &buf), to: convertType(toType))

        // ── Call ──────────────────────────────────────────────────────────────

        case .call(let callee, let args, _, _, let ty, _):
            let calleeExpr = convertExpr(callee, into: &buf)
            let argExprs   = args.map { convertExpr($0, into: &buf) }
            return .call(callee: calleeExpr, args: argExprs, type: convertType(ty))

        // ── GNU statement expression `({ ... })` ─────────────────────────────
        //
        // Emit all statements into buf; return the value of the last expression.

        case .stmtExpr(let body, let ty, _):
            guard !body.isEmpty else { return .intLiteral(0, type: convertType(ty)) }
            for stmt in body.dropLast() { buf.append(convertStmt(stmt)) }
            if case .expr(let last, _) = body.last! {
                return convertExpr(last, into: &buf)
            }
            buf.append(convertStmt(body.last!))
            return .intLiteral(0, type: convertType(ty))

        // ── GNU label address `&&label` ───────────────────────────────────────

        case .labelValue(_, let uniqueLabel, let ty, _):
            return .labelAddress(uniqueLabel, type: convertType(ty))

        // ── Atomic operations ─────────────────────────────────────────────────

        case .cas(let addr, let old, let new, let ty, _):
            return .cas(
                addr: convertExpr(addr, into: &buf),
                old:  convertExpr(old,  into: &buf),
                new:  convertExpr(new,  into: &buf),
                type: convertType(ty))

        case .exchange(let addr, let value, let ty, _):
            return .exchange(
                addr:  convertExpr(addr,  into: &buf),
                value: convertExpr(value, into: &buf),
                type:  convertType(ty))

        // ── Zero initialisation ───────────────────────────────────────────────
        //
        // Emits the assignment as a side-effecting statement and returns the
        // resulting lvalue so the expression still has a value.

        case .memzero(let ref, let ty, _):
            let cty  = convertType(ty)
            let v    = CExpr.variable(name: ref.name, type: cty, id: ref.id)
            let zero = CExpr.intLiteral(0, type: cty)
            buf.append(.assign(lhs: v, rhs: zero))
            return v
        }
    }

    // MARK: - Helpers

    /// `expr != 0`
    private func isNonZero(_ expr: CExpr) -> CExpr {
        .binary(.ne, expr, .intLiteral(0, type: expr.type), type: .int(signed: true))
    }

    /// `expr == 0`
    private func isZero(_ expr: CExpr) -> CExpr {
        .binary(.eq, expr, .intLiteral(0, type: expr.type), type: .int(signed: true))
    }

    /// Prepends `pre` statements before `stmt`, flattening if possible.
    private func withPre(_ pre: [CStmt], _ stmt: CStmt) -> CStmt {
        pre.isEmpty ? stmt : .block(pre + flattenStmt(stmt))
    }

    /// Unwraps a single `.block` into its children; otherwise returns `[stmt]`.
    private func flattenStmt(_ stmt: CStmt) -> [CStmt] {
        if case .block(let ss) = stmt { return ss }
        return [stmt]
    }
}
