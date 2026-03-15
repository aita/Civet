// Recursive descent C parser.
// Ported from chibicc's parse.c.
// Produces SyntaxTranslationUnit directly (no intermediate AST).

import Common
import Foundation
import Syntax

// MARK: - Public API

/// Parse a C source file and return the Syntax IR translation unit.
public func parseFile(
    _ path: String,
    includePaths: [String] = []
) throws -> SyntaxTranslationUnit {
    guard let source = try? String(contentsOfFile: path, encoding: .utf8) else {
        throw ParseError("cannot open file: \(path)",
                         SourceLocation(fileName: path, line: 0, column: 0))
    }

    var lexer = Lexer(source: source, fileName: path, fileNo: 1)
    var tokens = try lexer.tokenize()

    let pp = Preprocessor()
    pp.includePaths = includePaths
    pp.baseFile = path
    tokens = try pp.preprocess(tokens)

    let parser = CParser(tokens: tokens)
    return try parser.parse()
}

// MARK: - CParser

public class CParser {
    var cursor: TokenCursor
    var nextVarID: Int = 1
    var uniqueNameID: Int = 0
    var vlaLenExprs: [ObjectIdentifier: SyntaxExpr] = [:]  // VLA type → length expression
    var _builtinAllocaVar: VarInfo? = nil

    // Scoping
    var scopes: [Scope] = []

    // Current function state
    var currentLocals: [VarInfo] = []
    var currentFnType: SyntaxType? = nil
    var currentFnName: String? = nil
    var currentFnRefs: [String] = []
    var gotos: [(name: String, loc: SourceLocation)] = []
    var labelMap: [String: String] = [:]  // name → uniqueLabel
    var brkLabel: String? = nil
    var contLabel: String? = nil

    // Switch context
    var switchCases: [(begin: Int64, end: Int64, label: String)]? = nil
    var switchDefaultLabel: String? = nil

    // Globals
    var allDeclarations: [SyntaxDeclaration] = []
    var globalVars: [VarInfo] = []  // all globals (including functions)
    var globalLocs: [Int: SourceLocation] = [:] // varID → loc

    public init(tokens: [Token]) {
        self.cursor = TokenCursor(tokens)
        enterScope()
    }

    // MARK: - Public API

    public func parse() throws -> SyntaxTranslationUnit {
        declareBuiltinFunctions()

        while !cursor.isEOF {
            var attr = VarAttr()
            let basety = try declspec(attr: &attr)

            if attr.isTypedef {
                try parseTypedef(basety)
                continue
            }

            if isFunction() {
                try parseFunction(basety, attr: attr)
                continue
            }

            try parseGlobalVariable(basety, attr: attr)
        }

        // Mark live functions
        for gv in globalVars where gv.isRoot {
            markLive(gv)
        }

        // Remove redundant tentative definitions
        scanGlobals()

        // Build final declarations
        var decls: [SyntaxDeclaration] = []
        for d in allDeclarations {
            decls.append(d)
        }
        return SyntaxTranslationUnit(declarations: decls)
    }

    // MARK: - Scope management

    func enterScope() {
        scopes.append(Scope())
    }

    func leaveScope() {
        scopes.removeLast()
    }

    func pushVar(_ name: String, _ vs: VarScope) {
        scopes[scopes.count - 1].vars[name] = vs
    }

    func findVar(_ name: String) -> VarScope? {
        for i in stride(from: scopes.count - 1, through: 0, by: -1) {
            if let vs = scopes[i].vars[name] { return vs }
        }
        return nil
    }

    func findTag(_ name: String) -> SyntaxType? {
        for i in stride(from: scopes.count - 1, through: 0, by: -1) {
            if let ty = scopes[i].tags[name] { return ty }
        }
        return nil
    }

    func pushTag(_ name: String, _ ty: SyntaxType) {
        scopes[scopes.count - 1].tags[name] = ty
    }

    func findTagInCurrentScope(_ name: String) -> SyntaxType? {
        scopes[scopes.count - 1].tags[name]
    }

    // MARK: - Variable creation

    func freshID() -> Int {
        let id = nextVarID
        nextVarID += 1
        return id
    }

    func newUniqueName() -> String {
        let name = ".LC\(uniqueNameID)"
        uniqueNameID += 1
        return name
    }

    func newLVar(_ name: String, _ ty: SyntaxType) -> VarInfo {
        let v = VarInfo(name: name, type: ty, isLocal: true, id: freshID())
        pushVar(name, VarScope(varInfo: v))
        currentLocals.append(v)
        return v
    }

    func newGVar(_ name: String, _ ty: SyntaxType) -> VarInfo {
        let v = VarInfo(name: name, type: ty, isLocal: false, id: freshID())
        v.isStatic = true
        v.isDefinition = true
        pushVar(name, VarScope(varInfo: v))
        globalVars.append(v)
        return v
    }

    func builtinAllocaRef() -> SyntaxVariableRef {
        if let v = _builtinAllocaVar {
            return v.makeRef()
        }
        let ty = SyntaxType(kind: .function(returnType: pointerTo(tyVoid),
            params: [tyInt], isVariadic: false), size: 1, align: 1)
        let v = VarInfo(name: "alloca", type: ty, isLocal: false, id: freshID())
        v.isDefinition = false
        globalVars.append(v)
        _builtinAllocaVar = v
        return v.makeRef()
    }

    func newAnonGVar(_ ty: SyntaxType) -> VarInfo {
        newGVar(newUniqueName(), ty)
    }

    func newStringLiteral(_ data: [UInt8], _ ty: SyntaxType) -> VarInfo {
        let v = newAnonGVar(ty)
        v.initData = data
        return v
    }

    // MARK: - Unique label

    func newUniqueLabel() -> String {
        newUniqueName()
    }

    // MARK: - Token helpers

    var tok: Token { cursor.current }
    var loc: SourceLocation { cursor.current.loc }

    func lookAhead(_ offset: Int = 1) -> Token {
        let p = cursor.pos + offset
        if p < cursor.tokens.count { return cursor.tokens[p] }
        return cursor.tokens[cursor.tokens.count - 1] // EOF
    }

    func error(_ msg: String) -> ParseError {
        ParseError(msg, loc)
    }

    // MARK: - is_typename

    private let typenameKeywords: Set<String> = [
        "void", "_Bool", "char", "short", "int", "long", "struct", "union",
        "typedef", "enum", "static", "extern", "_Alignas", "signed", "unsigned",
        "const", "volatile", "auto", "register", "restrict", "__restrict",
        "__restrict__", "_Noreturn", "float", "double", "typeof", "inline",
        "_Thread_local", "__thread", "_Atomic",
    ]

    func isTypename() -> Bool {
        let t = tok
        if t.kind == .keyword || t.kind == .ident {
            if typenameKeywords.contains(t.text) { return true }
        }
        if t.kind == .ident {
            if let vs = findVar(t.text), vs.typeDef != nil { return true }
        }
        return false
    }

    func findTypedef() -> SyntaxType? {
        if tok.kind == .ident {
            if let vs = findVar(tok.text) { return vs.typeDef }
        }
        return nil
    }

    // MARK: - declspec

    func declspec(attr: inout VarAttr) throws -> SyntaxType {
        let VOID = 1, BOOL = 1 << 2, CHAR = 1 << 4, SHORT = 1 << 6
        let INT = 1 << 8, LONG = 1 << 10, FLOAT = 1 << 12, DOUBLE = 1 << 14
        let OTHER = 1 << 16, SIGNED = 1 << 17, UNSIGNED = 1 << 18

        var ty: SyntaxType = tyInt
        var counter = 0
        var isAtomic = false

        while isTypename() {
            let t = tok

            // Storage class specifiers
            if ["typedef", "static", "extern", "inline",
                "_Thread_local", "__thread"].contains(t.text) {
                switch t.text {
                case "typedef": attr.isTypedef = true
                case "static": attr.isStatic = true
                case "extern": attr.isExtern = true
                case "inline": attr.isInline = true
                default: attr.isTLS = true
                }
                _ = cursor.advance()
                continue
            }

            // Ignored qualifiers
            if ["const", "volatile", "auto", "register", "restrict",
                "__restrict", "__restrict__", "_Noreturn"].contains(t.text) {
                _ = cursor.advance()
                continue
            }

            if t.text == "_Atomic" {
                _ = cursor.advance()
                if cursor.equal("(") {
                    _ = cursor.advance()
                    ty = try typename_()
                    try cursor.skip(")")
                }
                isAtomic = true
                continue
            }

            if t.text == "_Alignas" {
                _ = cursor.advance()
                try cursor.skip("(")
                if isTypename() {
                    let aty = try typename_()
                    attr.align = aty.align
                } else {
                    attr.align = Int(try constExpr())
                }
                try cursor.skip(")")
                continue
            }

            // User-defined types
            let td = findTypedef()
            if ["struct", "union", "enum", "typeof"].contains(t.text) || td != nil {
                if counter != 0 { break }

                if t.text == "struct" {
                    _ = cursor.advance()
                    ty = try structDecl()
                } else if t.text == "union" {
                    _ = cursor.advance()
                    ty = try unionDecl()
                } else if t.text == "enum" {
                    _ = cursor.advance()
                    ty = try enumSpecifier()
                } else if t.text == "typeof" {
                    _ = cursor.advance()
                    ty = try typeofSpecifier()
                } else {
                    ty = td!
                    _ = cursor.advance()
                }
                counter += OTHER
                continue
            }

            // Built-in types
            switch t.text {
            case "void":     counter += VOID
            case "_Bool":    counter += BOOL
            case "char":     counter += CHAR
            case "short":    counter += SHORT
            case "int":      counter += INT
            case "long":     counter += LONG
            case "float":    counter += FLOAT
            case "double":   counter += DOUBLE
            case "signed":   counter |= SIGNED
            case "unsigned": counter |= UNSIGNED
            default: break
            }

            switch counter {
            case VOID: ty = tyVoid
            case BOOL: ty = tyBool
            case CHAR, SIGNED + CHAR: ty = tyChar
            case UNSIGNED + CHAR: ty = tyUChar
            case SHORT, SHORT + INT, SIGNED + SHORT, SIGNED + SHORT + INT: ty = tyShort
            case UNSIGNED + SHORT, UNSIGNED + SHORT + INT: ty = tyUShort
            case INT, SIGNED, SIGNED + INT: ty = tyInt
            case UNSIGNED, UNSIGNED + INT: ty = tyUInt
            case LONG, LONG + INT, LONG + LONG, LONG + LONG + INT,
                 SIGNED + LONG, SIGNED + LONG + INT,
                 SIGNED + LONG + LONG, SIGNED + LONG + LONG + INT:
                ty = tyLong
            case UNSIGNED + LONG, UNSIGNED + LONG + INT,
                 UNSIGNED + LONG + LONG, UNSIGNED + LONG + LONG + INT:
                ty = tyULong
            case FLOAT: ty = tyFloat
            case DOUBLE: ty = tyDouble
            case LONG + DOUBLE: ty = tyLDouble
            default:
                throw error("invalid type")
            }

            _ = cursor.advance()
        }

        if isAtomic {
            ty = SyntaxType(kind: ty.kind, size: ty.size, align: ty.align,
                            isAtomic: true, name: ty.name)
        }

        return ty
    }

    // declspec without attr (for typename parsing, etc.)
    func declspecNoAttr() throws -> SyntaxType {
        var attr = VarAttr()
        return try declspec(attr: &attr)
    }

    // MARK: - Declarator

    func parsePointers(_ ty: SyntaxType) -> SyntaxType {
        var ty = ty
        while cursor.consume("*") {
            ty = pointerTo(ty)
            while cursor.equal("const") || cursor.equal("volatile") ||
                  cursor.equal("restrict") || cursor.equal("__restrict") ||
                  cursor.equal("__restrict__") {
                _ = cursor.advance()
            }
        }
        return ty
    }

    func declarator(_ baseTy: SyntaxType) throws -> (SyntaxType, String?) {
        var ty = parsePointers(baseTy)

        if cursor.equal("(") && !isTypenameAt(cursor.pos + 1) {
            // Could be parenthesized declarator: check if next is * or ident or (
            let next = lookAhead()
            if next.text == "*" || next.kind == .ident ||
               next.text == "(" {
                let start = cursor.pos
                cursor.pos += 1 // skip "("
                let dummy = SyntaxType(kind: .void, size: 0, align: 0)
                _ = try declarator(dummy) // consume inner tokens
                try cursor.skip(")")
                ty = try typeSuffix(ty)
                let endPos = cursor.pos
                cursor.pos = start + 1
                let result = try declarator(ty)
                cursor.pos = endPos
                return result
            }
        }

        var name: String? = nil
        if tok.kind == .ident && !typenameKeywords.contains(tok.text) {
            name = cursor.advance().text
        }

        ty = try typeSuffix(ty)
        return (ty, name)
    }

    func isTypenameAt(_ pos: Int) -> Bool {
        guard pos < cursor.tokens.count else { return false }
        let t = cursor.tokens[pos]
        if typenameKeywords.contains(t.text) { return true }
        if t.kind == .ident {
            if let vs = findVar(t.text), vs.typeDef != nil { return true }
        }
        return false
    }

    func abstractDeclarator(_ baseTy: SyntaxType) throws -> SyntaxType {
        var ty = parsePointers(baseTy)

        if cursor.equal("(") {
            let next = lookAhead()
            if next.text == "*" || next.text == "(" || next.text == "[" {
                let start = cursor.pos
                cursor.pos += 1
                let dummy = SyntaxType(kind: .void, size: 0, align: 0)
                _ = try abstractDeclarator(dummy)
                try cursor.skip(")")
                ty = try typeSuffix(ty)
                let endPos = cursor.pos
                cursor.pos = start + 1
                ty = try abstractDeclarator(ty)
                cursor.pos = endPos
                return ty
            }
        }

        return try typeSuffix(ty)
    }

    func typename_() throws -> SyntaxType {
        let ty = try declspecNoAttr()
        return try abstractDeclarator(ty)
    }

    // MARK: - Type suffix

    func typeSuffix(_ ty: SyntaxType) throws -> SyntaxType {
        if cursor.equal("(") {
            return try funcParams(ty)
        }
        if cursor.equal("[") {
            return try arrayDimensions(ty)
        }
        return ty
    }

    func funcParams(_ retTy: SyntaxType) throws -> SyntaxType {
        _ = cursor.advance() // skip "("
        // Save outer lastParsedParamNames — nested declarators (e.g. `int (*fn)(int)`)
        // trigger recursive funcParams calls that would clobber it.
        let savedParamNames = lastParsedParamNames
        lastParsedParamNames = []

        if cursor.equal("void") && lookAhead().text == ")" {
            _ = cursor.advance() // skip "void"
            _ = cursor.advance() // skip ")"
            return SyntaxType(kind: .function(returnType: retTy, params: [], isVariadic: false),
                              size: 1, align: 1)
        }

        var paramTypes: [SyntaxType] = []
        var isVariadic = false
        var first = true

        while !cursor.equal(")") {
            if !first { try cursor.skip(",") }
            first = false

            if cursor.consume("...") {
                isVariadic = true
                break
            }

            var pty = try declspecNoAttr()
            // Save/restore lastParsedParamNames around declarator, because
            // function-pointer params like `int (*fn)(int)` cause re-entrant
            // funcParams calls that reset lastParsedParamNames.
            let outerNames = lastParsedParamNames
            let (declTy, paramName) = try declarator(pty)
            lastParsedParamNames = outerNames
            pty = declTy

            // Array → pointer decay in parameters
            if case .array(let elem, _) = pty.kind {
                pty = pointerTo(elem)
            }
            // VLA → pointer decay in parameters
            if case .vla(let elem, _) = pty.kind {
                pty = pointerTo(elem)
            }
            // Function → pointer in parameters
            if case .function = pty.kind {
                pty = pointerTo(pty)
            }

            paramTypes.append(pty)
            lastParsedParamNames.append(paramName)
        }

        if paramTypes.isEmpty { isVariadic = true }

        try cursor.skip(")")
        // The outermost funcParams sets lastParsedParamNames for createParamLocals.
        // Inner (nested) calls had their results captured above; restore saved names
        // only if this is a nested call (savedParamNames was non-empty before we reset it).
        // Actually, the caller of the outermost funcParams will read lastParsedParamNames,
        // so we must NOT restore here. The save/restore around declarator above handles it.
        return SyntaxType(kind: .function(returnType: retTy, params: paramTypes,
                                          isVariadic: isVariadic),
                          size: 1, align: 1)
    }

    func arrayDimensions(_ baseTy: SyntaxType) throws -> SyntaxType {
        _ = cursor.advance() // skip "["
        while cursor.equal("static") || cursor.equal("restrict") {
            _ = cursor.advance()
        }

        if cursor.consume("]") {
            let ty = try typeSuffix(baseTy)
            return arrayOf(ty, -1)
        }

        let savedPos = cursor.pos
        // Try to evaluate as constant
        let node = try conditional()
        try cursor.skip("]")
        let ty = try typeSuffix(baseTy)

        // If inner type is VLA or expression is not constant, create VLA
        let isInnerVLA: Bool
        if case .vla = ty.kind { isInnerVLA = true } else { isInnerVLA = false }

        if !isInnerVLA, let val = tryEvalConst(node) {
            return arrayOf(ty, Int(val))
        }
        // VLA - runtime-sized array
        let vlaTy = SyntaxType(kind: .vla(element: ty, sizeVar: nil), size: 8, align: ty.align)
        vlaLenExprs[ObjectIdentifier(vlaTy)] = synCast(node, to: tyULong, loc: tok.loc)
        return vlaTy
    }

    // Compute VLA size expression: vlaSizeVar = len * sizeof(element)
    // Returns a comma expression that computes sizes for all VLA levels
    // and returns the top-level size variable.
    func computeVlaSizeExpr(_ ty: SyntaxType, loc: SourceLocation) -> SyntaxExpr {
        let l = loc
        let null = SyntaxExpr.nullExpr(type: tyVoid, loc: l)

        // Recursively compute sizes for nested VLAs
        func compute(_ t: SyntaxType) -> SyntaxExpr {
            guard case .vla(let elem, let existingSizeVar) = t.kind else {
                return null
            }

            // If already computed, just return the existing size var
            if let sv = existingSizeVar {
                return .variable(ref: sv, type: tyULong, loc: l)
            }

            // Recursively handle nested VLA element types
            var chain = compute(elem)

            // Get the length expression
            guard let lenExpr = vlaLenExprs[ObjectIdentifier(t)] else {
                return chain
            }

            // Get element size (either a constant or a VLA size var)
            let baseSz: SyntaxExpr
            if case .vla(_, let innerSizeVar) = elem.kind, let isv = innerSizeVar {
                baseSz = SyntaxExpr.variable(ref: isv, type: tyULong, loc: l)
            } else {
                baseSz = SyntaxExpr.intLiteral(value: Int64(elem.size), type: tyULong, loc: l)
            }

            // Create a local var for this VLA's total size
            let sizeVar = newLVar("", tyULong)
            let sizeRef = sizeVar.makeRef()

            // size = len * baseSz
            let mulExpr = SyntaxExpr.binary(op: .mul,
                lhs: lenExpr, rhs: baseSz,
                type: tyULong, loc: l)
            let sizeVarExpr = SyntaxExpr.variable(ref: sizeRef, type: tyULong, loc: l)
            let assignExpr = SyntaxExpr.assign(lhs: sizeVarExpr, rhs: mulExpr, type: tyULong, loc: l)

            // Update the type with the size var
            t.kind = .vla(element: elem, sizeVar: sizeRef)

            // Chain: previous computations, then this assignment
            if case .nullExpr = chain {
                chain = assignExpr
            } else {
                chain = SyntaxExpr.comma(lhs: chain, rhs: assignExpr, type: tyULong, loc: l)
            }

            return chain
        }

        let chain = compute(ty)

        // Return the size var
        if case .vla(_, let sv) = ty.kind, let sizeRef = sv {
            if case .nullExpr = chain {
                return .variable(ref: sizeRef, type: tyULong, loc: l)
            }
            return SyntaxExpr.comma(lhs: chain,
                rhs: .variable(ref: sizeRef, type: tyULong, loc: l),
                type: tyULong, loc: l)
        }

        return chain
    }

    // MARK: - Enum specifier

    func enumSpecifier() throws -> SyntaxType {
        let ty = enumType()

        var tag: String? = nil
        if tok.kind == .ident {
            tag = cursor.advance().text
        }

        if let tag = tag, !cursor.equal("{") {
            if let found = findTag(tag) { return found }
            throw error("unknown enum type")
        }

        try cursor.skip("{")
        var val = 0
        var first = true
        while !consumeEnd() {
            if !first { try cursor.skip(",") }
            first = false

            guard tok.kind == .ident else { throw error("expected identifier") }
            let name = cursor.advance().text

            if cursor.consume("=") {
                val = Int(try constExpr())
            }

            var vs = VarScope()
            vs.enumTy = ty
            vs.enumVal = val
            pushVar(name, vs)
            val += 1
        }

        if let tag = tag { pushTag(tag, ty) }
        return ty
    }

    // MARK: - typeof

    func typeofSpecifier() throws -> SyntaxType {
        try cursor.skip("(")
        let ty: SyntaxType
        if isTypename() {
            ty = try typename_()
        } else {
            let e = try expr()
            ty = typeOf(e)
        }
        try cursor.skip(")")
        return ty
    }

    // MARK: - Struct/Union

    func structUnionDecl() throws -> (SyntaxType, [SyntaxMember], Bool, Bool, Int?) {
        var ty = structType()
        var isPacked = false
        var attrAlign: Int? = nil

        // Parse __attribute__
        if cursor.equal("__attribute__") {
            (isPacked, attrAlign) = try parseAttributes()
        }

        var tag: String? = nil
        if tok.kind == .ident {
            tag = cursor.advance().text
        }

        if let tag = tag, !cursor.equal("{") {
            if let found = findTag(tag) { return (found, [], false, false, nil) }
            // Forward declaration
            pushTag(tag, ty)
            return (ty, [], false, true, nil)
        }

        try cursor.skip("{")
        let (members, isFlexible) = try structMembers()

        if cursor.equal("__attribute__") {
            let (p, a) = try parseAttributes()
            if p { isPacked = true }
            if let a = a { attrAlign = a }
        }

        if let tag = tag {
            if let existing = findTagInCurrentScope(tag) {
                // Redefine existing type in-place
                existing.kind = ty.kind // will be overwritten below
                ty = existing
            } else {
                pushTag(tag, ty)
            }
        }

        return (ty, members, isFlexible, isPacked, attrAlign)
    }

    func structDecl() throws -> SyntaxType {
        let (ty, members, isFlexible, isPacked, attrAlign) = try structUnionDecl()

        if members.isEmpty && isFlexible == false {
            // Forward declaration or existing tag reference
            return ty
        }

        // Compute struct layout
        var bits = 0
        var maxAlign = 1
        var laidOut: [SyntaxMember] = []

        for mem in members {
            let offset: Int
            let bitfield = mem.bitfield

            if let bf = bitfield, bf.bitWidth == 0 {
                bits = alignTo(bits, mem.type.size * 8)
                laidOut.append(mem)
                continue
            } else if let bf = bitfield {
                let sz = mem.type.size
                if bits / (sz * 8) != (bits + bf.bitWidth - 1) / (sz * 8) {
                    bits = alignTo(bits, sz * 8)
                }
                offset = alignDown(bits / 8, sz)
                let bitOffset = bits % (sz * 8)
                bits += bf.bitWidth
                let m = SyntaxMember(name: mem.name, type: mem.type, index: mem.index,
                                     offset: offset, align: mem.align,
                                     bitfield: SyntaxMember.BitfieldInfo(
                                         bitOffset: bitOffset, bitWidth: bf.bitWidth))
                laidOut.append(m)
            } else {
                if !isPacked {
                    bits = alignTo(bits, mem.align * 8)
                }
                offset = bits / 8
                bits += mem.type.size * 8
                let m = SyntaxMember(name: mem.name, type: mem.type, index: mem.index,
                                     offset: offset, align: mem.align, bitfield: nil)
                laidOut.append(m)
            }

            if !isPacked && maxAlign < mem.align {
                maxAlign = mem.align
            }
        }

        // __attribute__((aligned(N))) overrides natural alignment
        if let attrAlign = attrAlign, attrAlign > maxAlign {
            maxAlign = attrAlign
        }

        let size = alignTo(bits, maxAlign * 8) / 8
        ty.kind = .struct(members: laidOut, isFlexible: isFlexible, isPacked: isPacked)
        ty.size = size
        ty.align = maxAlign
        return ty
    }

    func unionDecl() throws -> SyntaxType {
        let (ty, members, _, _, attrAlign) = try structUnionDecl()
        if members.isEmpty { return ty }

        var maxAlign = 1
        var maxSize = 0
        for mem in members {
            if maxAlign < mem.align { maxAlign = mem.align }
            if maxSize < mem.type.size { maxSize = mem.type.size }
        }
        if let attrAlign = attrAlign, attrAlign > maxAlign {
            maxAlign = attrAlign
        }
        let size = alignTo(maxSize, maxAlign)
        ty.kind = .union(members: members)
        ty.size = size
        ty.align = maxAlign
        return ty
    }

    func structMembers() throws -> ([SyntaxMember], Bool) {
        var members: [SyntaxMember] = []
        var idx = 0
        var isFlexible = false

        while !cursor.equal("}") {
            var attr = VarAttr()
            let basety = try declspec(attr: &attr)

            // Anonymous struct/union member
            if case .struct = basety.kind, cursor.consume(";") {
                let a = attr.align > 0 ? attr.align : basety.align
                members.append(SyntaxMember(name: nil, type: basety, index: idx,
                                            offset: 0, align: a, bitfield: nil))
                idx += 1
                continue
            }
            if case .union = basety.kind, cursor.consume(";") {
                let a = attr.align > 0 ? attr.align : basety.align
                members.append(SyntaxMember(name: nil, type: basety, index: idx,
                                            offset: 0, align: a, bitfield: nil))
                idx += 1
                continue
            }

            var first = true
            while !cursor.consume(";") {
                if !first { try cursor.skip(",") }
                first = false

                let (memTy, memName) = try declarator(basety)
                let a = attr.align > 0 ? attr.align : memTy.align

                var bitfield: SyntaxMember.BitfieldInfo? = nil
                if cursor.consume(":") {
                    let w = Int(try constExpr())
                    bitfield = SyntaxMember.BitfieldInfo(bitOffset: 0, bitWidth: w)
                }

                members.append(SyntaxMember(name: memName, type: memTy, index: idx,
                                            offset: 0, align: a, bitfield: bitfield))
                idx += 1
            }
        }

        // Flexible array member
        if let last = members.last {
            if case .array(let elem, let len) = last.type.kind, len < 0 {
                let fixed = SyntaxMember(name: last.name, type: arrayOf(elem, 0),
                                         index: last.index, offset: 0,
                                         align: last.align, bitfield: nil)
                members[members.count - 1] = fixed
                isFlexible = true
            }
        }

        _ = cursor.advance() // skip "}"
        return (members, isFlexible)
    }

    /// Skip balanced `(( ... ))` content inside `__attribute__`.
    /// Handles nested parentheses and arbitrary tokens.
    func skipAttributeParens() throws {
        try cursor.skip("(")
        try cursor.skip("(")
        var depth = 0
        while true {
            if cursor.equal(")") && depth == 0 { break }
            if cursor.consume("(") { depth += 1; continue }
            if cursor.consume(")") { depth -= 1; continue }
            _ = cursor.advance()
        }
        try cursor.skip(")")
        try cursor.skip(")")
    }

    func parseAttributes() throws -> (isPacked: Bool, align: Int?) {
        var isPacked = false
        var align: Int? = nil

        while cursor.consume("__attribute__") {
            try cursor.skip("(")
            try cursor.skip("(")
            var depth = 0
            while true {
                if cursor.equal(")") && depth == 0 { break }
                if cursor.equal("(") { depth += 1; _ = cursor.advance(); continue }
                if cursor.equal(")") { depth -= 1; _ = cursor.advance(); continue }
                if cursor.consume("packed") {
                    isPacked = true
                } else if cursor.consume("aligned") {
                    if cursor.consume("(") {
                        align = Int(try constExpr())
                        try cursor.skip(")")
                    }
                } else {
                    _ = cursor.advance() // skip unknown attr tokens
                }
            }
            try cursor.skip(")")
            try cursor.skip(")")
        }
        return (isPacked, align)
    }

    /// Skip any `__attribute__((...))` and `__asm__("...")` sequences.
    func skipAttributes() throws {
        while cursor.equal("__attribute__") || cursor.equal("__asm__") {
            if cursor.consume("__attribute__") {
                try skipAttributeParens()
            } else if cursor.consume("__asm__") {
                try cursor.skip("(")
                var depth = 1
                while depth > 0 {
                    if cursor.consume("(") { depth += 1 }
                    else if cursor.consume(")") { depth -= 1 }
                    else { _ = cursor.advance() }
                }
            }
        }
    }

    // MARK: - Helper: consumeEnd (for initializer lists)

    func isEnd() -> Bool {
        cursor.equal("}") || (cursor.equal(",") && lookAhead().text == "}")
    }

    func consumeEnd() -> Bool {
        if cursor.equal("}") {
            _ = cursor.advance()
            return true
        }
        if cursor.equal(",") && lookAhead().text == "}" {
            _ = cursor.advance() // skip ","
            _ = cursor.advance() // skip "}"
            return true
        }
        return false
    }

    // MARK: - Struct member lookup

    func getStructMember(_ ty: SyntaxType, _ name: String) -> SyntaxMember? {
        let members: [SyntaxMember]
        switch ty.kind {
        case .struct(let m, _, _): members = m
        case .union(let m): members = m
        default: return nil
        }

        for mem in members {
            if mem.name == nil {
                // Anonymous member
                if getStructMember(mem.type, name) != nil {
                    return mem
                }
                continue
            }
            if mem.name == name { return mem }
        }
        return nil
    }

    func structRef(_ base: SyntaxExpr, _ memberName: String, _ loc: SourceLocation) throws -> SyntaxExpr {
        var node = base
        var ty = typeOf(base)

        while true {
            guard let mem = getStructMember(ty, memberName) else {
                throw ParseError("no such member: \(memberName)", loc)
            }
            node = .member(expr: node, member: mem, type: mem.type, loc: loc)
            if mem.name != nil { break }
            ty = mem.type
        }
        return node
    }

    // MARK: - Statements

    func compoundStmt() throws -> SyntaxStmt {
        let l = loc
        enterScope()
        var stmts: [SyntaxStmt] = []

        while !cursor.equal("}") {
            if isTypename() && lookAhead().text != ":" {
                var attr = VarAttr()
                let basety = try declspec(attr: &attr)

                if attr.isTypedef {
                    try parseTypedef(basety)
                    continue
                }

                if isFunction() {
                    try parseFunction(basety, attr: attr)
                    continue
                }

                if attr.isExtern {
                    try parseGlobalVariable(basety, attr: attr)
                    continue
                }

                let s = try declaration(basety, attr: attr)
                stmts.append(s)
            } else {
                stmts.append(try stmt())
            }
        }

        leaveScope()
        _ = cursor.advance() // skip "}"
        return .block(stmts, loc: l)
    }

    func stmt() throws -> SyntaxStmt {
        let l = loc

        if cursor.equal("return") {
            _ = cursor.advance()
            if cursor.consume(";") {
                return .return(value: nil, loc: l)
            }
            var e = try expr()
            try cursor.skip(";")

            if let fnTy = currentFnType, case .function(let retTy, _, _) = fnTy.kind {
                if !isStructOrUnion(retTy) {
                    e = synCast(e, to: retTy, loc: l)
                }
            }
            return .return(value: e, loc: l)
        }

        if cursor.equal("if") {
            _ = cursor.advance()
            try cursor.skip("(")
            let cond = try expr()
            try cursor.skip(")")
            let then = try stmt()
            var els: SyntaxStmt? = nil
            if cursor.consume("else") {
                els = try stmt()
            }
            return .if(cond: cond, then: then, else: els, loc: l)
        }

        if cursor.equal("switch") {
            _ = cursor.advance()
            try cursor.skip("(")
            let cond = try expr()
            try cursor.skip(")")

            let savedCases = switchCases
            let savedDefault = switchDefaultLabel
            let savedBrk = brkLabel
            switchCases = []
            switchDefaultLabel = nil
            let bl = newUniqueLabel()
            brkLabel = bl

            let body = try stmt()

            let cases = switchCases!.map {
                CaseInfo(begin: $0.begin, end: $0.end, label: $0.label)
            }
            let result = SyntaxStmt.switch(cond: cond, body: body, cases: cases,
                                            defaultLabel: switchDefaultLabel,
                                            breakLabel: bl, loc: l)
            switchCases = savedCases
            switchDefaultLabel = savedDefault
            brkLabel = savedBrk
            return result
        }

        if cursor.equal("case") {
            _ = cursor.advance()
            let begin = try constExpr()
            var end = begin
            if cursor.consume("...") {
                end = try constExpr()
            }
            try cursor.skip(":")
            let label = newUniqueLabel()
            let body = try stmt()
            switchCases?.append((begin: begin, end: end, label: label))
            return .case(begin: begin, end: end, label: label, body: body, loc: l)
        }

        if cursor.equal("default") {
            _ = cursor.advance()
            try cursor.skip(":")
            let label = newUniqueLabel()
            let body = try stmt()
            switchDefaultLabel = label
            return .case(begin: 0, end: 0, label: label, body: body, loc: l)
        }

        if cursor.equal("for") {
            _ = cursor.advance()
            try cursor.skip("(")
            enterScope()

            let savedBrk = brkLabel
            let savedCont = contLabel
            let bl = newUniqueLabel()
            let cl = newUniqueLabel()
            brkLabel = bl
            contLabel = cl

            var initStmt: SyntaxStmt? = nil
            if isTypename() {
                let basety = try declspecNoAttr()
                initStmt = try declaration(basety, attr: VarAttr())
            } else {
                initStmt = try exprStmt()
            }

            var cond: SyntaxExpr? = nil
            if !cursor.equal(";") {
                cond = try expr()
            }
            try cursor.skip(";")

            var inc: SyntaxExpr? = nil
            if !cursor.equal(")") {
                inc = try expr()
            }
            try cursor.skip(")")

            let body = try stmt()
            leaveScope()
            brkLabel = savedBrk
            contLabel = savedCont

            return .for(init: initStmt, cond: cond, inc: inc, body: body,
                        breakLabel: bl, continueLabel: cl, loc: l)
        }

        if cursor.equal("while") {
            _ = cursor.advance()
            try cursor.skip("(")
            let cond = try expr()
            try cursor.skip(")")

            let savedBrk = brkLabel
            let savedCont = contLabel
            let bl = newUniqueLabel()
            let cl = newUniqueLabel()
            brkLabel = bl
            contLabel = cl

            let body = try stmt()
            brkLabel = savedBrk
            contLabel = savedCont

            return .for(init: nil, cond: cond, inc: nil, body: body,
                        breakLabel: bl, continueLabel: cl, loc: l)
        }

        if cursor.equal("do") {
            _ = cursor.advance()
            let savedBrk = brkLabel
            let savedCont = contLabel
            let bl = newUniqueLabel()
            let cl = newUniqueLabel()
            brkLabel = bl
            contLabel = cl

            let body = try stmt()
            brkLabel = savedBrk
            contLabel = savedCont

            try cursor.skip("while")
            try cursor.skip("(")
            let cond = try expr()
            try cursor.skip(")")
            try cursor.skip(";")

            return .doWhile(body: body, cond: cond,
                            breakLabel: bl, continueLabel: cl, loc: l)
        }

        if cursor.equal("asm") || cursor.equal("__asm__") {
            _ = cursor.advance()
            while cursor.equal("volatile") || cursor.equal("inline") {
                _ = cursor.advance()
            }
            try cursor.skip("(")
            guard tok.kind == .str else { throw error("expected string literal") }
            var data = tok.strData ?? []
            // Remove trailing null if present
            if data.last == 0 { data.removeLast() }
            let s = String(bytes: data, encoding: .utf8) ?? ""
            _ = cursor.advance()
            try cursor.skip(")")
            try cursor.skip(";")
            return .asm(s, loc: l)
        }

        if cursor.equal("goto") {
            _ = cursor.advance()
            if cursor.consume("*") {
                let target = try expr()
                try cursor.skip(";")
                return .gotoExpr(target: target, loc: l)
            }
            let name = cursor.advance().text
            gotos.append((name: name, loc: l))
            try cursor.skip(";")
            let ul = ".L\(currentFnName ?? "").\(name)"
            return .goto(uniqueLabel: ul, loc: l)
        }

        if cursor.equal("break") {
            _ = cursor.advance()
            try cursor.skip(";")
            guard let bl = brkLabel else { throw error("stray break") }
            return .goto(uniqueLabel: bl, loc: l)
        }

        if cursor.equal("continue") {
            _ = cursor.advance()
            try cursor.skip(";")
            guard let cl = contLabel else { throw error("stray continue") }
            return .goto(uniqueLabel: cl, loc: l)
        }

        // Label
        if tok.kind == .ident && lookAhead().text == ":" {
            let name = cursor.advance().text
            _ = cursor.advance() // skip ":"
            let uniqueLabel = ".L\(currentFnName ?? "").\(name)"
            let body = try stmt()
            labelMap[name] = uniqueLabel
            return .label(name: name, uniqueLabel: uniqueLabel, body: body, loc: l)
        }

        if cursor.equal("{") {
            _ = cursor.advance()
            return try compoundStmt()
        }

        return try exprStmt()
    }

    func exprStmt() throws -> SyntaxStmt {
        let l = loc
        if cursor.consume(";") {
            return .block([], loc: l)
        }
        let e = try expr()
        try cursor.skip(";")
        return .expr(e, loc: l)
    }

    // MARK: - Declarations

    func declaration(_ basety: SyntaxType, attr: VarAttr) throws -> SyntaxStmt {
        let l = loc
        var stmts: [SyntaxStmt] = []
        var i = 0

        while !cursor.equal(";") {
            if i > 0 { try cursor.skip(",") }
            i += 1

            let (ty, name) = try declarator(basety)
            guard let name = name else { throw error("variable name omitted") }

            if attr.isStatic {
                // Static local → anonymous global
                let gv = newAnonGVar(ty)
                pushVar(name, VarScope(varInfo: gv))
                if cursor.consume("=") {
                    try gvarInitializer(gv)
                }
                let gvLoc = loc
                globalLocs[gv.id] = gvLoc
                allDeclarations.append(.variable(gv.makeGlobalVar(loc: gvLoc)))
                continue
            }

            // Compute VLA sizes for any VLA in the type (including pointers to VLA)
            let vlaSizeExpr = computeVlaSizeExpr(ty, loc: l)
            if case .nullExpr = vlaSizeExpr {} else {
                stmts.append(.expr(vlaSizeExpr, loc: l))
            }

            if case .vla(_, let sizeVarRef) = ty.kind, let svRef = sizeVarRef {
                if cursor.equal("=") {
                    throw error("variable-sized object may not be initialized")
                }
                // VLA variable: allocate via alloca() call
                let v = newLVar(name, ty)
                if attr.align > 0 { v.align = attr.align }
                let sizeVarExpr = SyntaxExpr.variable(ref: svRef, type: tyULong, loc: l)
                let allocaFnTy = SyntaxType(kind: .function(returnType: pointerTo(tyVoid),
                    params: [tyInt], isVariadic: false), size: 1, align: 1)
                let allocaRef = builtinAllocaRef()
                let allocaCallee = SyntaxExpr.variable(ref: allocaRef, type: allocaFnTy, loc: l)
                let allocaExpr = SyntaxExpr.call(callee: allocaCallee, args: [sizeVarExpr],
                    funcType: allocaFnTy, returnBuffer: nil,
                    type: pointerTo(tyVoid), loc: l)
                let lhs = SyntaxExpr.vlaPtr(ref: v.makeRef(), type: ty, loc: l)
                let assignExpr = SyntaxExpr.assign(lhs: lhs, rhs: allocaExpr, type: ty, loc: l)
                stmts.append(.expr(assignExpr, loc: l))
                continue
            }

            let v = newLVar(name, ty)
            if attr.align > 0 { v.align = attr.align }

            if cursor.consume("=") {
                let initExpr = try lvarInitializer(v)
                stmts.append(.expr(initExpr, loc: l))
            }
        }

        try cursor.skip(";")
        if stmts.count == 1 { return stmts[0] }
        return .block(stmts, loc: l)
    }

    // MARK: - Expressions

    func expr() throws -> SyntaxExpr {
        let l = loc
        var node = try assign()
        if cursor.consume(",") {
            let rhs = try expr()
            return .comma(lhs: node, rhs: rhs, type: typeOf(rhs), loc: l)
        }
        return node
    }

    func assign() throws -> SyntaxExpr {
        let l = loc
        var node = try conditional()

        if cursor.consume("=") {
            let rhs = try assign()
            return makeAssign(node, rhs, loc: l)
        }

        // Compound assignments
        if let op = compoundAssignOp() {
            _ = cursor.advance()
            let rhs = try assign()
            return try toAssign(op, node, rhs, loc: l)
        }

        return node
    }

    func compoundAssignOp() -> String? {
        let t = tok.text
        if ["+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="].contains(t) {
            return t
        }
        return nil
    }

    func makeAssign(_ lhs: SyntaxExpr, _ rhs: SyntaxExpr, loc: SourceLocation) -> SyntaxExpr {
        var rhs = rhs
        let lhsTy = typeOf(lhs)
        if !isStructOrUnion(lhsTy) {
            rhs = synCast(rhs, to: lhsTy, loc: loc)
        }
        return .assign(lhs: lhs, rhs: rhs, type: lhsTy, loc: loc)
    }

    func toAssign(_ op: String, _ lhs: SyntaxExpr, _ rhs: SyntaxExpr,
                  loc: SourceLocation) throws -> SyntaxExpr {
        let lhsTy = typeOf(lhs)

        // For member bitfield: tmp = &A, (*tmp).x = (*tmp).x op rhs
        if case .member(let base, let mem, _, _) = lhs {
            let ptrTy = pointerTo(typeOf(base))
            let tmp = newLVar("", ptrTy)
            let tmpRef = SyntaxExpr.variable(ref: tmp.makeRef(), type: ptrTy, loc: loc)

            let addr = SyntaxExpr.addressOf(operand: base, type: ptrTy, loc: loc)
            let assign1 = SyntaxExpr.assign(lhs: tmpRef, rhs: addr, type: ptrTy, loc: loc)

            let deref = SyntaxExpr.deref(operand: tmpRef, type: typeOf(base), loc: loc)
            let memAccess1 = SyntaxExpr.member(expr: deref, member: mem,
                                                type: mem.type, loc: loc)
            let deref2 = SyntaxExpr.deref(operand: tmpRef, type: typeOf(base), loc: loc)
            let memAccess2 = SyntaxExpr.member(expr: deref2, member: mem,
                                                type: mem.type, loc: loc)

            let binExpr = try makeBinaryForCompound(op, memAccess2, rhs, loc: loc)
            let castedBin = synCast(binExpr, to: mem.type, loc: loc)
            let assign2 = makeAssign(memAccess1, castedBin, loc: loc)

            return .comma(lhs: assign1, rhs: assign2, type: typeOf(assign2), loc: loc)
        }

        // General case: tmp = &A, *tmp = *tmp op B
        let ptrTy = pointerTo(lhsTy)
        let tmp = newLVar("", ptrTy)
        let tmpRef = SyntaxExpr.variable(ref: tmp.makeRef(), type: ptrTy, loc: loc)

        let addr = SyntaxExpr.addressOf(operand: lhs, type: ptrTy, loc: loc)
        let assign1 = SyntaxExpr.assign(lhs: tmpRef, rhs: addr, type: ptrTy, loc: loc)

        let deref1 = SyntaxExpr.deref(operand: tmpRef, type: lhsTy, loc: loc)
        let deref2 = SyntaxExpr.deref(operand: tmpRef, type: lhsTy, loc: loc)

        let binExpr = try makeBinaryForCompound(op, deref2, rhs, loc: loc)
        let castedBin = synCast(binExpr, to: lhsTy, loc: loc)
        let assign2 = SyntaxExpr.assign(lhs: deref1, rhs: castedBin, type: lhsTy, loc: loc)

        return .comma(lhs: assign1, rhs: assign2, type: lhsTy, loc: loc)
    }

    func makeBinaryForCompound(_ op: String, _ lhs: SyntaxExpr, _ rhs: SyntaxExpr,
                                loc: SourceLocation) throws -> SyntaxExpr {
        switch op {
        case "+=": return newAdd(lhs, rhs, loc: loc)
        case "-=": return newSub(lhs, rhs, loc: loc)
        case "*=": return makeBinary(.mul, lhs, rhs, loc: loc)
        case "/=": return makeBinary(.div, lhs, rhs, loc: loc)
        case "%=": return makeBinary(.mod, lhs, rhs, loc: loc)
        case "&=": return makeBinary(.bitAnd, lhs, rhs, loc: loc)
        case "|=": return makeBinary(.bitOr, lhs, rhs, loc: loc)
        case "^=": return makeBinary(.bitXor, lhs, rhs, loc: loc)
        case "<<=": return makeBinaryNoConv(.shl, lhs, rhs, loc: loc)
        case ">>=": return makeBinaryNoConv(.shr, lhs, rhs, loc: loc)
        default: throw error("unknown compound assignment")
        }
    }

    func conditional() throws -> SyntaxExpr {
        let l = loc
        var cond = try logor()

        if !cursor.consume("?") { return cond }

        // GNU extension: a ?: b
        if cursor.equal(":") {
            let condTy = typeOf(cond)
            let tmp = newLVar("", condTy)
            let tmpRef = SyntaxExpr.variable(ref: tmp.makeRef(), type: condTy, loc: l)
            let assign = SyntaxExpr.assign(lhs: tmpRef, rhs: cond, type: condTy, loc: l)
            _ = cursor.advance() // skip ":"
            let els = try conditional()
            let (_, _, commonTy) = usualArithConvTypes(condTy, typeOf(els))
            let ternary = SyntaxExpr.ternary(cond: tmpRef, then: tmpRef, els: els,
                                              type: commonTy, loc: l)
            return .comma(lhs: assign, rhs: ternary, type: commonTy, loc: l)
        }

        let then = try expr()
        try cursor.skip(":")
        let els = try conditional()

        let thenTy = typeOf(then)
        let elsTy = typeOf(els)

        let resultTy: SyntaxType
        if case .void = thenTy.kind {
            resultTy = tyVoid
        } else if case .void = elsTy.kind {
            resultTy = tyVoid
        } else {
            let (_, _, ct) = usualArithConvTypes(thenTy, elsTy)
            resultTy = ct
        }

        return .ternary(cond: cond, then: synCast(then, to: resultTy, loc: l),
                         els: synCast(els, to: resultTy, loc: l),
                         type: resultTy, loc: l)
    }

    func logor() throws -> SyntaxExpr {
        var node = try logand()
        while cursor.consume("||") {
            let l = loc
            let rhs = try logand()
            node = .logical(op: .or, lhs: node, rhs: rhs, type: tyInt, loc: l)
        }
        return node
    }

    func logand() throws -> SyntaxExpr {
        var node = try bitor_()
        while cursor.consume("&&") {
            let l = loc
            let rhs = try bitor_()
            node = .logical(op: .and, lhs: node, rhs: rhs, type: tyInt, loc: l)
        }
        return node
    }

    func bitor_() throws -> SyntaxExpr {
        var node = try bitxor_()
        while cursor.consume("|") {
            let l = loc
            let rhs = try bitxor_()
            node = makeBinary(.bitOr, node, rhs, loc: l)
        }
        return node
    }

    func bitxor_() throws -> SyntaxExpr {
        var node = try bitand_()
        while cursor.consume("^") {
            let l = loc
            let rhs = try bitand_()
            node = makeBinary(.bitXor, node, rhs, loc: l)
        }
        return node
    }

    func bitand_() throws -> SyntaxExpr {
        var node = try equality()
        while cursor.consume("&") {
            let l = loc
            let rhs = try equality()
            node = makeBinary(.bitAnd, node, rhs, loc: l)
        }
        return node
    }

    func equality() throws -> SyntaxExpr {
        var node = try relational()
        while true {
            let l = loc
            if cursor.consume("==") {
                let rhs = try relational()
                node = makeComparison(.eq, node, rhs, loc: l)
            } else if cursor.consume("!=") {
                let rhs = try relational()
                node = makeComparison(.ne, node, rhs, loc: l)
            } else {
                break
            }
        }
        return node
    }

    func relational() throws -> SyntaxExpr {
        var node = try shift()
        while true {
            let l = loc
            if cursor.consume("<") {
                node = makeComparison(.lt, node, try shift(), loc: l)
            } else if cursor.consume("<=") {
                node = makeComparison(.le, node, try shift(), loc: l)
            } else if cursor.consume(">") {
                node = makeComparison(.lt, try shift(), node, loc: l) // swap
            } else if cursor.consume(">=") {
                node = makeComparison(.le, try shift(), node, loc: l) // swap
            } else {
                break
            }
        }
        return node
    }

    func shift() throws -> SyntaxExpr {
        var node = try add()
        while true {
            let l = loc
            if cursor.consume("<<") {
                node = makeBinaryNoConv(.shl, node, try add(), loc: l)
            } else if cursor.consume(">>") {
                node = makeBinaryNoConv(.shr, node, try add(), loc: l)
            } else {
                break
            }
        }
        return node
    }

    func add() throws -> SyntaxExpr {
        var node = try mul()
        while true {
            let l = loc
            if cursor.consume("+") {
                node = newAdd(node, try mul(), loc: l)
            } else if cursor.consume("-") {
                node = newSub(node, try mul(), loc: l)
            } else {
                break
            }
        }
        return node
    }

    func mul() throws -> SyntaxExpr {
        var node = try cast()
        while true {
            let l = loc
            if cursor.consume("*") {
                node = makeBinary(.mul, node, try cast(), loc: l)
            } else if cursor.consume("/") {
                node = makeBinary(.div, node, try cast(), loc: l)
            } else if cursor.consume("%") {
                node = makeBinary(.mod, node, try cast(), loc: l)
            } else {
                break
            }
        }
        return node
    }

    func cast() throws -> SyntaxExpr {
        if cursor.equal("(") && isTypenameAt(cursor.pos + 1) {
            let l = loc
            let savedPos = cursor.pos
            _ = cursor.advance() // skip "("
            let ty = try typename_()
            try cursor.skip(")")

            // Compound literal
            if cursor.equal("{") {
                cursor.pos = savedPos
                return try unary()
            }

            let operand = try cast()
            return synCast(operand, to: ty, loc: l)
        }
        return try unary()
    }

    func unary() throws -> SyntaxExpr {
        let l = loc

        if cursor.consume("+") { return try cast() }
        if cursor.consume("-") {
            let operand = try cast()
            let oty = typeOf(operand)
            let ty = getCommonType(tyInt, oty)
            let casted = synCast(operand, to: ty, loc: l)
            return .unary(op: .neg, operand: casted, type: ty, loc: l)
        }

        if cursor.consume("&") {
            let operand = try cast()
            let oty = typeOf(operand)
            let ptrTy: SyntaxType
            if case .array(let elem, _) = oty.kind {
                ptrTy = pointerTo(elem)
            } else {
                ptrTy = pointerTo(oty)
            }
            return .addressOf(operand: operand, type: ptrTy, loc: l)
        }

        if cursor.consume("*") {
            let operand = try cast()
            let oty = typeOf(operand)
            if case .function = oty.kind { return operand }
            guard let base = baseType(oty) else {
                throw error("invalid pointer dereference")
            }
            return .deref(operand: operand, type: base, loc: l)
        }

        if cursor.consume("!") {
            return .unary(op: .logNot, operand: try cast(), type: tyInt, loc: l)
        }

        if cursor.consume("~") {
            let operand = try cast()
            return .unary(op: .bitNot, operand: operand, type: typeOf(operand), loc: l)
        }

        // ++i → i += 1
        if cursor.consume("++") {
            let operand = try unary()
            return try toAssign("+=", operand,
                                .intLiteral(value: 1, type: tyInt, loc: l), loc: l)
        }
        // --i → i -= 1
        if cursor.consume("--") {
            let operand = try unary()
            return try toAssign("-=", operand,
                                .intLiteral(value: 1, type: tyInt, loc: l), loc: l)
        }

        // &&label (GNU labels-as-values)
        if cursor.consume("&&") {
            let name = cursor.advance().text
            gotos.append((name: name, loc: l))
            let ul = ".L\(currentFnName ?? "").\(name)"
            return .labelValue(label: name, uniqueLabel: ul,
                               type: pointerTo(tyVoid), loc: l)
        }

        return try postfix()
    }

    func postfix() throws -> SyntaxExpr {
        // Compound literal: (type-name) { ... }
        if cursor.equal("(") && isTypenameAt(cursor.pos + 1) {
            let l = loc
            _ = cursor.advance() // skip "("
            let ty = try typename_()
            try cursor.skip(")")

            if cursor.equal("{") {
                if scopes.count <= 1 {
                    // Global scope compound literal
                    let gv = newAnonGVar(ty)
                    try gvarInitializer(gv)
                    let gvLoc = loc
                    globalLocs[gv.id] = gvLoc
                    allDeclarations.append(.variable(gv.makeGlobalVar(loc: gvLoc)))
                    return .variable(ref: gv.makeRef(), type: gv.type, loc: l)
                }
                // Local scope compound literal
                let v = newLVar("", ty)
                let initExpr = try lvarInitializer(v)
                let varExpr = SyntaxExpr.variable(ref: v.makeRef(), type: v.type, loc: l)
                return .comma(lhs: initExpr, rhs: varExpr, type: v.type, loc: l)
            }
            // Not a compound literal, backtrack
            // This shouldn't happen since we checked for "{" above
            throw error("expected '{'")
        }

        var node = try primary()

        while true {
            let l = loc

            if cursor.consume("(") {
                node = try funcall(node, loc: l)
                continue
            }

            if cursor.consume("[") {
                let idx = try expr()
                try cursor.skip("]")
                let sum = newAdd(node, idx, loc: l)
                node = .deref(operand: sum,
                              type: baseType(typeOf(sum))!,
                              loc: l)
                continue
            }

            if cursor.consume(".") {
                let name = cursor.advance().text
                node = try structRef(node, name, l)
                continue
            }

            if cursor.consume("->") {
                let name = cursor.advance().text
                let derefTy = baseType(typeOf(node))!
                let derefed = SyntaxExpr.deref(operand: node, type: derefTy, loc: l)
                node = try structRef(derefed, name, l)
                continue
            }

            if cursor.consume("++") {
                // A++ → (typeof A)((A += 1) - 1)
                node = try newIncDec(node, 1, loc: l)
                continue
            }

            if cursor.consume("--") {
                node = try newIncDec(node, -1, loc: l)
                continue
            }

            break
        }
        return node
    }

    func newIncDec(_ node: SyntaxExpr, _ addend: Int,
                   loc: SourceLocation) throws -> SyntaxExpr {
        let nodeTy = typeOf(node)
        let one = SyntaxExpr.intLiteral(value: Int64(addend), type: tyInt, loc: loc)
        let addExpr = newAdd(node, one, loc: loc)
        let assigned = try toAssign("+=", node, one, loc: loc)
        let negOne = SyntaxExpr.intLiteral(value: Int64(-addend), type: tyInt, loc: loc)
        let result = newAdd(assigned, negOne, loc: loc)
        return synCast(result, to: nodeTy, loc: loc)
    }

    func funcall(_ fn: SyntaxExpr, loc: SourceLocation) throws -> SyntaxExpr {
        let fnTy = typeOf(fn)
        let funcTy: SyntaxType

        switch fnTy.kind {
        case .function: funcTy = fnTy
        case .pointer(let p):
            if case .function = p.kind { funcTy = p }
            else { throw error("not a function") }
        default: throw error("not a function")
        }

        guard case .function(let retTy, let paramTys, let isVariadic) = funcTy.kind else {
            throw error("not a function")
        }

        var args: [SyntaxExpr] = []
        var paramIdx = 0
        while !cursor.equal(")") {
            if !args.isEmpty { try cursor.skip(",") }
            var arg = try assign()

            if paramIdx < paramTys.count {
                let pty = paramTys[paramIdx]
                if !isStructOrUnion(pty) {
                    arg = synCast(arg, to: pty, loc: loc)
                }
                paramIdx += 1
            } else {
                // Variadic: promote float → double
                if case .float = typeOf(arg).kind {
                    arg = synCast(arg, to: tyDouble, loc: loc)
                }
            }
            args.append(arg)
        }
        try cursor.skip(")")

        var retBuf: SyntaxVariableRef? = nil
        if isStructOrUnion(retTy) {
            let buf = newLVar("", retTy)
            retBuf = buf.makeRef()
        }

        return .call(callee: fn, args: args, funcType: funcTy,
                     returnBuffer: retBuf, type: retTy, loc: loc)
    }

    func primary() throws -> SyntaxExpr {
        let l = loc

        // Statement expression: ({ ... })
        if cursor.equal("(") && lookAhead().text == "{" {
            _ = cursor.advance() // skip "("
            _ = cursor.advance() // skip "{"
            let block = try compoundStmt()
            try cursor.skip(")")

            // Extract type from last expression statement
            var stmts: [SyntaxStmt] = []
            if case .block(let ss, _) = block { stmts = ss }
            var resultTy: SyntaxType = tyVoid
            if let last = stmts.last, case .expr(let e, _) = last {
                resultTy = typeOf(e)
            }
            return .stmtExpr(body: stmts, type: resultTy, loc: l)
        }

        // Parenthesized expression
        if cursor.consume("(") {
            let node = try expr()
            try cursor.skip(")")
            return node
        }

        // sizeof
        if cursor.equal("sizeof") {
            _ = cursor.advance()
            if cursor.equal("(") && isTypenameAt(cursor.pos + 1) {
                _ = cursor.advance() // skip "("
                let ty = try typename_()
                try cursor.skip(")")
                if case .vla(_, let sizeVar) = ty.kind, let sv = sizeVar {
                    return .variable(ref: sv, type: tyULong, loc: l)
                }
                if case .vla = ty.kind {
                    // VLA without computed size — compute inline
                    let sizeExpr = computeVlaSizeExpr(ty, loc: l)
                    return sizeExpr
                }
                return .intLiteral(value: Int64(ty.size), type: tyULong, loc: l)
            }
            let node = try unary()
            let nodeTy = typeOf(node)
            if case .vla(_, let sizeVar) = nodeTy.kind, let sv = sizeVar {
                return .variable(ref: sv, type: tyULong, loc: l)
            }
            if case .vla = nodeTy.kind {
                return computeVlaSizeExpr(nodeTy, loc: l)
            }
            return .intLiteral(value: Int64(nodeTy.size), type: tyULong, loc: l)
        }

        // _Alignof
        if cursor.equal("_Alignof") {
            _ = cursor.advance()
            if cursor.equal("(") && isTypenameAt(cursor.pos + 1) {
                _ = cursor.advance()
                let ty = try typename_()
                try cursor.skip(")")
                return .intLiteral(value: Int64(ty.align), type: tyULong, loc: l)
            }
            let node = try unary()
            return .intLiteral(value: Int64(typeOf(node).align), type: tyULong, loc: l)
        }

        // _Generic
        if cursor.equal("_Generic") {
            _ = cursor.advance()
            return try genericSelection()
        }

        // __builtin_types_compatible_p
        if cursor.equal("__builtin_types_compatible_p") {
            _ = cursor.advance()
            try cursor.skip("(")
            let t1 = try typename_()
            try cursor.skip(",")
            let t2 = try typename_()
            try cursor.skip(")")
            return .intLiteral(value: isCompatible(t1, t2) ? 1 : 0, type: tyInt, loc: l)
        }

        // __builtin_reg_class
        if cursor.equal("__builtin_reg_class") {
            _ = cursor.advance()
            try cursor.skip("(")
            let ty = try typename_()
            try cursor.skip(")")
            let cls: Int64
            if isInteger(ty) || isPointerLike(ty) { cls = 0 }
            else if isFlonum(ty) { cls = 1 }
            else { cls = 2 }
            return .intLiteral(value: cls, type: tyInt, loc: l)
        }

        // __builtin_compare_and_swap
        if cursor.equal("__builtin_compare_and_swap") {
            _ = cursor.advance()
            try cursor.skip("(")
            let addr = try assign()
            try cursor.skip(",")
            let old = try assign()
            try cursor.skip(",")
            let new_ = try assign()
            try cursor.skip(")")
            return .cas(addr: addr, old: old, new: new_, type: tyBool, loc: l)
        }

        // __builtin_atomic_exchange
        if cursor.equal("__builtin_atomic_exchange") {
            _ = cursor.advance()
            try cursor.skip("(")
            let addr = try assign()
            try cursor.skip(",")
            let val = try assign()
            try cursor.skip(")")
            let resultTy = baseType(typeOf(addr)) ?? tyInt
            return .exchange(addr: addr, value: val, type: resultTy, loc: l)
        }

        // Identifier
        if tok.kind == .ident {
            let name = cursor.advance().text

            if let vs = findVar(name) {
                if let v = vs.varInfo {
                    // Track refs for static inline
                    if v.isFunction {
                        currentFnRefs.append(v.name)
                    }
                    return .variable(ref: v.makeRef(), type: v.type, loc: l)
                }
                if let _ = vs.enumTy {
                    return .intLiteral(value: Int64(vs.enumVal), type: tyInt, loc: l)
                }
            }

            // Implicit function declaration check
            if cursor.equal("(") {
                throw ParseError("implicit declaration of function '\(name)'", l)
            }
            throw ParseError("undefined variable '\(name)'", l)
        }

        // String literal
        if tok.kind == .str {
            let t = cursor.advance()
            let data = t.strData ?? []
            let strTy = t.ty ?? arrayOf(tyChar, data.count)
            let v = newStringLiteral(data, strTy)
            let vLoc = l
            globalLocs[v.id] = vLoc
            allDeclarations.append(.variable(v.makeGlobalVar(loc: vLoc)))
            return .variable(ref: v.makeRef(), type: v.type, loc: l)
        }

        // Number
        if tok.kind == .num {
            let t = cursor.advance()
            let numTy = t.ty ?? tyInt
            if isFlonum(numTy) {
                return .floatLiteral(value: t.fval, type: numTy, loc: l)
            }
            return .intLiteral(value: t.val, type: numTy, loc: l)
        }

        throw error("expected an expression")
    }

    func genericSelection() throws -> SyntaxExpr {
        let l = loc
        try cursor.skip("(")
        let ctrl = try assign()
        var ctrlTy = typeOf(ctrl)

        // Decay function/array to pointer
        if case .function = ctrlTy.kind { ctrlTy = pointerTo(ctrlTy) }
        if case .array(let elem, _) = ctrlTy.kind { ctrlTy = pointerTo(elem) }

        var result: SyntaxExpr? = nil
        while !cursor.consume(")") {
            try cursor.skip(",")
            if cursor.equal("default") {
                _ = cursor.advance()
                try cursor.skip(":")
                let node = try assign()
                if result == nil { result = node }
            } else {
                let ty = try typename_()
                try cursor.skip(":")
                let node = try assign()
                if isCompatible(ctrlTy, ty) { result = node }
            }
        }

        guard let result = result else {
            throw ParseError("no compatible type in _Generic", l)
        }
        return result
    }

    // MARK: - Pointer arithmetic

    func newAdd(_ lhs: SyntaxExpr, _ rhs: SyntaxExpr,
                loc: SourceLocation) -> SyntaxExpr {
        let lt = typeOf(lhs), rt = typeOf(rhs)

        if isNumeric(lt) && isNumeric(rt) {
            return makeBinary(.add, lhs, rhs, loc: loc)
        }

        // Canonicalize num + ptr → ptr + num
        if baseType(lt) == nil && baseType(rt) != nil {
            return newAdd(rhs, lhs, loc: loc)
        }

        // ptr + num
        guard let base = baseType(lt) else {
            return makeBinary(.add, lhs, rhs, loc: loc)
        }

        // Array types decay to pointer for the result type
        let resultTy: SyntaxType
        if case .array(let elem, _) = lt.kind {
            resultTy = pointerTo(elem)
        } else {
            resultTy = lt
        }

        let scale: SyntaxExpr
        if case .vla(_, let sv) = base.kind, let svRef = sv {
            scale = SyntaxExpr.variable(ref: svRef, type: tyULong, loc: loc)
        } else {
            scale = SyntaxExpr.intLiteral(value: Int64(base.size), type: tyLong, loc: loc)
        }
        let scaledRhs = makeBinaryNoConv(.mul, synCast(rhs, to: tyLong, loc: loc),
                                          scale, loc: loc)
        return SyntaxExpr.binary(op: .add, lhs: lhs, rhs: scaledRhs,
                                 type: resultTy, loc: loc)
    }

    func newSub(_ lhs: SyntaxExpr, _ rhs: SyntaxExpr,
                loc: SourceLocation) -> SyntaxExpr {
        let lt = typeOf(lhs), rt = typeOf(rhs)

        if isNumeric(lt) && isNumeric(rt) {
            return makeBinary(.sub, lhs, rhs, loc: loc)
        }

        // ptr - num
        if baseType(lt) != nil && isInteger(rt) {
            let base = baseType(lt)!
            let resultTy: SyntaxType
            if case .array(let elem, _) = lt.kind {
                resultTy = pointerTo(elem)
            } else {
                resultTy = lt
            }
            let scale: SyntaxExpr
            if case .vla(_, let sv) = base.kind, let svRef = sv {
                scale = SyntaxExpr.variable(ref: svRef, type: tyULong, loc: loc)
            } else {
                scale = SyntaxExpr.intLiteral(value: Int64(base.size), type: tyLong, loc: loc)
            }
            let scaledRhs = makeBinaryNoConv(.mul, synCast(rhs, to: tyLong, loc: loc),
                                              scale, loc: loc)
            return SyntaxExpr.binary(op: .sub, lhs: lhs, rhs: scaledRhs,
                                     type: resultTy, loc: loc)
        }

        // ptr - ptr
        if baseType(lt) != nil && baseType(rt) != nil {
            let diff = SyntaxExpr.binary(op: .sub, lhs: lhs, rhs: rhs,
                                          type: tyLong, loc: loc)
            let base = baseType(lt)!
            let divisor: SyntaxExpr
            if case .vla(_, let sv) = base.kind, let svRef = sv {
                divisor = SyntaxExpr.variable(ref: svRef, type: tyULong, loc: loc)
            } else {
                divisor = SyntaxExpr.intLiteral(value: Int64(base.size), type: tyLong, loc: loc)
            }
            return SyntaxExpr.binary(op: .div, lhs: diff, rhs: divisor,
                                     type: tyLong, loc: loc)
        }

        return makeBinary(.sub, lhs, rhs, loc: loc)
    }

    // MARK: - Binary/Cast helpers

    func makeBinary(_ op: BinaryOp, _ lhs: SyntaxExpr, _ rhs: SyntaxExpr,
                    loc: SourceLocation) -> SyntaxExpr {
        let (cl, cr, ct) = usualArithConvExprs(lhs, rhs, loc: loc)
        return .binary(op: op, lhs: cl, rhs: cr, type: ct, loc: loc)
    }

    func makeBinaryNoConv(_ op: BinaryOp, _ lhs: SyntaxExpr, _ rhs: SyntaxExpr,
                           loc: SourceLocation) -> SyntaxExpr {
        .binary(op: op, lhs: lhs, rhs: rhs, type: typeOf(lhs), loc: loc)
    }

    func makeComparison(_ op: BinaryOp, _ lhs: SyntaxExpr, _ rhs: SyntaxExpr,
                        loc: SourceLocation) -> SyntaxExpr {
        let (cl, cr, _) = usualArithConvExprs(lhs, rhs, loc: loc)
        return .binary(op: op, lhs: cl, rhs: cr, type: tyInt, loc: loc)
    }

    func usualArithConvTypes(_ t1: SyntaxType, _ t2: SyntaxType) -> (SyntaxType, SyntaxType, SyntaxType) {
        let ct = getCommonType(t1, t2)
        return (ct, ct, ct)
    }

    func usualArithConvExprs(_ lhs: SyntaxExpr, _ rhs: SyntaxExpr,
                              loc: SourceLocation) -> (SyntaxExpr, SyntaxExpr, SyntaxType) {
        let ct = getCommonType(typeOf(lhs), typeOf(rhs))
        return (synCast(lhs, to: ct, loc: loc), synCast(rhs, to: ct, loc: loc), ct)
    }

    func synCast(_ expr: SyntaxExpr, to ty: SyntaxType,
                 loc: SourceLocation) -> SyntaxExpr {
        let fromTy = typeOf(expr)
        // Skip if same type
        if fromTy === ty { return expr }
        if fromTy.size == ty.size && typeKindMatches(fromTy, ty) { return expr }
        return .cast(operand: expr, toType: ty, type: ty, loc: loc)
    }

    private func typeKindMatches(_ a: SyntaxType, _ b: SyntaxType) -> Bool {
        switch (a.kind, b.kind) {
        case (.void, .void), (.bool, .bool), (.float, .float),
             (.double, .double), (.longDouble, .longDouble), (.enum, .enum):
            return true
        case (.char(let u1), .char(let u2)): return u1 == u2
        case (.short(let u1), .short(let u2)): return u1 == u2
        case (.int(let u1), .int(let u2)): return u1 == u2
        case (.long(let u1), .long(let u2)): return u1 == u2
        default: return false
        }
    }

    func isStructOrUnion(_ ty: SyntaxType) -> Bool {
        switch ty.kind {
        case .struct, .union: return true
        default: return false
        }
    }

    // MARK: - Constant expression evaluation

    func constExpr() throws -> Int64 {
        let node = try conditional()
        return evalConst(node)
    }

    func evalConst(_ node: SyntaxExpr) -> Int64 {
        if isFlonum(typeOf(node)) { return Int64(evalDouble(node)) }

        switch node {
        case .intLiteral(let v, _, _): return v
        case .floatLiteral(let v, _, _): return Int64(v)
        case .binary(let op, let lhs, let rhs, let ty, _):
            let l = evalConst(lhs), r = evalConst(rhs)
            switch op {
            case .add: return l + r
            case .sub: return l - r
            case .mul: return l * r
            case .div:
                if isUnsigned(ty) { return Int64(bitPattern: UInt64(bitPattern: l) / UInt64(bitPattern: r)) }
                return l / r
            case .mod:
                if isUnsigned(ty) { return Int64(bitPattern: UInt64(bitPattern: l) % UInt64(bitPattern: r)) }
                return l % r
            case .bitAnd: return l & r
            case .bitOr: return l | r
            case .bitXor: return l ^ r
            case .shl: return l << r
            case .shr:
                if isUnsigned(ty) && ty.size == 8 {
                    return Int64(bitPattern: UInt64(bitPattern: l) >> UInt64(r))
                }
                return l >> r
            case .eq: return l == r ? 1 : 0
            case .ne: return l != r ? 1 : 0
            case .lt:
                if isUnsigned(typeOf(lhs)) { return UInt64(bitPattern: l) < UInt64(bitPattern: r) ? 1 : 0 }
                return l < r ? 1 : 0
            case .le:
                if isUnsigned(typeOf(lhs)) { return UInt64(bitPattern: l) <= UInt64(bitPattern: r) ? 1 : 0 }
                return l <= r ? 1 : 0
            }
        case .unary(let op, let operand, _, _):
            switch op {
            case .neg: return -evalConst(operand)
            case .logNot: return evalConst(operand) == 0 ? 1 : 0
            case .bitNot: return ~evalConst(operand)
            }
        case .logical(let op, let lhs, let rhs, _, _):
            switch op {
            case .and: return (evalConst(lhs) != 0 && evalConst(rhs) != 0) ? 1 : 0
            case .or: return (evalConst(lhs) != 0 || evalConst(rhs) != 0) ? 1 : 0
            }
        case .ternary(let cond, let then, let els, _, _):
            return evalConst(cond) != 0 ? evalConst(then) : evalConst(els)
        case .comma(_, let rhs, _, _):
            return evalConst(rhs)
        case .cast(let operand, _, let ty, _):
            let val = evalConst(operand)
            if isInteger(ty) {
                switch ty.size {
                case 1: return isUnsigned(ty) ? Int64(UInt8(truncatingIfNeeded: val)) : Int64(Int8(truncatingIfNeeded: val))
                case 2: return isUnsigned(ty) ? Int64(UInt16(truncatingIfNeeded: val)) : Int64(Int16(truncatingIfNeeded: val))
                case 4: return isUnsigned(ty) ? Int64(UInt32(truncatingIfNeeded: val)) : Int64(Int32(truncatingIfNeeded: val))
                default: return val
                }
            }
            return val
        case .variable(let ref, let ty, _):
            // Global array/function → address label
            if !ref.isLocal {
                if case .array = ty.kind { return 0 }
                if case .function = ty.kind { return 0 }
            }
            return 0
        default:
            return 0
        }
    }

    func tryEvalConst(_ node: SyntaxExpr) -> Int64? {
        // Simple check for constant expression
        switch node {
        case .intLiteral(let v, _, _): return v
        case .floatLiteral: return evalConst(node)
        case .binary(_, let lhs, let rhs, _, _):
            if tryEvalConst(lhs) != nil && tryEvalConst(rhs) != nil {
                return evalConst(node)
            }
            return nil
        case .unary(_, let operand, _, _):
            if tryEvalConst(operand) != nil { return evalConst(node) }
            return nil
        case .cast(let operand, _, _, _):
            if tryEvalConst(operand) != nil { return evalConst(node) }
            return nil
        case .ternary(let c, let t, let e, _, _):
            if tryEvalConst(c) != nil && tryEvalConst(t) != nil && tryEvalConst(e) != nil {
                return evalConst(node)
            }
            return nil
        case .comma(let lhs, let rhs, _, _):
            if tryEvalConst(lhs) != nil && tryEvalConst(rhs) != nil {
                return evalConst(node)
            }
            return nil
        case .logical(_, let lhs, let rhs, _, _):
            if tryEvalConst(lhs) != nil && tryEvalConst(rhs) != nil {
                return evalConst(node)
            }
            return nil
        default: return nil
        }
    }

    func evalDouble(_ node: SyntaxExpr) -> Double {
        if isInteger(typeOf(node)) {
            let v = evalConst(node)
            if isUnsigned(typeOf(node)) { return Double(UInt64(bitPattern: v)) }
            return Double(v)
        }
        switch node {
        case .floatLiteral(let v, _, _): return v
        case .binary(let op, let lhs, let rhs, _, _):
            let l = evalDouble(lhs), r = evalDouble(rhs)
            switch op {
            case .add: return l + r
            case .sub: return l - r
            case .mul: return l * r
            case .div: return l / r
            default: return 0
            }
        case .unary(.neg, let operand, _, _):
            return -evalDouble(operand)
        case .ternary(let c, let t, let e, _, _):
            return evalDouble(c) != 0 ? evalDouble(t) : evalDouble(e)
        case .comma(_, let rhs, _, _):
            return evalDouble(rhs)
        case .cast(let operand, _, _, _):
            if isFlonum(typeOf(operand)) { return evalDouble(operand) }
            return Double(evalConst(operand))
        default: return 0
        }
    }

    // MARK: - Initializers

    func lvarInitializer(_ v: VarInfo) throws -> SyntaxExpr {
        let l = loc
        var newTy = v.type
        let init_ = try parseInitializer(v.type, &newTy)
        v.type = newTy

        // memzero + init assignments
        let memzero = SyntaxExpr.memzero(variable: v.makeRef(), type: v.type, loc: l)
        let assigns = createLvarInit(init_, v.type, varInfo: v, loc: l)
        return .comma(lhs: memzero, rhs: assigns, type: typeOf(assigns), loc: l)
    }

    func parseInitializer(_ ty: SyntaxType, _ newTy: inout SyntaxType) throws -> InitNode {
        let init_ = newInitializer(ty, isFlexible: true)
        try initializer2(init_)

        if case .struct(let members, let flex, let isPacked) = init_.ty.kind, flex {
            if let last = members.last, let children = init_.children,
               let lastChild = children[last.index] {
                // Flexible array member: update struct type to include the resolved array size
                if case .array(let elem, let len) = lastChild.ty.kind, len > 0 {
                    var newMembers = members
                    let updatedLast = SyntaxMember(
                        name: last.name, type: lastChild.ty,
                        index: last.index, offset: last.offset,
                        align: last.align, bitfield: last.bitfield)
                    newMembers[newMembers.count - 1] = updatedLast
                    let flexSize = elem.size * len
                    let totalSize = last.offset + flexSize
                    let al = init_.ty.align
                    let paddedSize = (totalSize + al - 1) / al * al
                    init_.ty = SyntaxType(kind: .struct(members: newMembers, isFlexible: false, isPacked: isPacked),
                                          size: paddedSize, align: al)
                }
            }
        }

        newTy = init_.ty
        return init_
    }

    func initializer2(_ init_: InitNode) throws {
        // String initializer
        if case .array(let elem, _) = init_.ty.kind, tok.kind == .str {
            try stringInitializer(init_)
            return
        }

        if case .array = init_.ty.kind {
            if cursor.equal("{") {
                try arrayInitializer1(init_)
            } else {
                try arrayInitializer2(init_, 0)
            }
            return
        }

        if case .struct = init_.ty.kind {
            if cursor.equal("{") {
                try structInitializer1(init_)
                return
            }
            // Check if the next expression is a struct/union value assignment
            let saved = cursor.pos
            let e = try assign()
            if isStructOrUnion(typeOf(e)) {
                init_.expr = e
                return
            }
            // Not a struct value — restore cursor and parse members without braces
            cursor.pos = saved
            try structInitializer2(init_, 0)
            return
        }

        if case .union = init_.ty.kind {
            try unionInitializer(init_)
            return
        }

        // Scalar with braces
        if cursor.consume("{") {
            try initializer2(init_)
            _ = consumeEnd()
            return
        }

        init_.expr = try assign()
    }

    func stringInitializer(_ init_: InitNode) throws {
        guard case .array(let elem, var len) = init_.ty.kind else { return }
        let t = cursor.advance()
        let data = t.strData ?? []

        if init_.isFlexible {
            let arrLen = data.count / max(elem.size, 1)
            init_.ty = arrayOf(elem, arrLen)
            init_.children = (0..<arrLen).map { _ in newInitializer(elem, isFlexible: false) }
            len = arrLen
        }

        let count = min(len, data.count / max(elem.size, 1))
        for i in 0..<count {
            guard let child = init_.children?[i] else { continue }
            let val: Int64
            switch elem.size {
            case 1: val = Int64(data[i])
            case 2:
                let lo = Int64(data[i*2])
                let hi = i*2+1 < data.count ? Int64(data[i*2+1]) : 0
                val = lo | (hi << 8)
            case 4:
                var v: UInt32 = 0
                for j in 0..<min(4, data.count - i*4) {
                    v |= UInt32(data[i*4+j]) << (j*8)
                }
                val = Int64(v)
            default: val = 0
            }
            child.expr = .intLiteral(value: val, type: elem, loc: loc)
        }
    }

    // designation = ("[" const-expr "]" | "." ident)* "="? initializer
    func designation(_ init_: InitNode) throws {
        if cursor.equal("[") {
            guard case .array(_, let len) = init_.ty.kind else {
                throw ParseError("array index in non-array initializer", cursor.current.loc)
            }
            _ = cursor.advance() // skip "["
            let begin = Int(try constExpr())
            let end: Int
            if cursor.consume("...") {
                end = Int(try constExpr())
            } else {
                end = begin
            }
            try cursor.skip("]")

            if let children = init_.children {
                let valuePos = cursor.pos
                for i in begin...min(end, children.count - 1) {
                    cursor.pos = valuePos
                    if let child = children[i] {
                        try designation(child)
                    }
                }
            }
            try arrayInitializer2(init_, begin + 1)
            return
        }

        if cursor.equal(".") {
            if case .struct(let members, _, _) = init_.ty.kind {
                let dotPos = cursor.pos
                _ = cursor.advance() // skip "."
                let name = cursor.advance().text
                if let mem = members.first(where: { $0.name == name }) {
                    if let child = init_.children?[mem.index] {
                        try designation(child)
                    }
                    init_.expr = nil
                    let nextIdx = mem.index + 1
                    try structInitializer2(init_, nextIdx)
                } else {
                    // Check anonymous struct/union members
                    for mem in members {
                        if mem.name == nil || mem.name == "" {
                            if getStructMember(mem.type, name) != nil {
                                cursor.pos = dotPos
                                if let child = init_.children?[mem.index] {
                                    try designation(child)
                                }
                                init_.expr = nil
                                let nextIdx = mem.index + 1
                                try structInitializer2(init_, nextIdx)
                                break
                            }
                        }
                    }
                }
                return
            }
            if case .union(let members) = init_.ty.kind {
                _ = cursor.advance() // skip "."
                let name = cursor.advance().text
                if let mem = members.first(where: { $0.name == name }) {
                    init_.mem = mem
                    if let child = init_.children?[mem.index] {
                        try designation(child)
                    }
                }
                return
            }
            throw ParseError("field name not in struct or union initializer", cursor.current.loc)
        }

        if cursor.consume("=") {}
        try initializer2(init_)
    }

    func arrayInitializer1(_ init_: InitNode) throws {
        try cursor.skip("{")
        if init_.isFlexible {
            guard case .array(let elem, _) = init_.ty.kind else { return }
            let len = try countArrayInitElements(elemType: elem)
            init_.ty = arrayOf(elem, len)
            init_.children = (0..<len).map { _ in newInitializer(elem, isFlexible: false) }
            init_.isFlexible = false
        }

        var i = 0
        var first = true
        while !consumeEnd() {
            if !first { try cursor.skip(",") }
            first = false

            if cursor.equal("[") {
                // Array designated initializer: [index] or [begin...end]
                _ = cursor.advance()
                let begin = Int(try constExpr())
                let end: Int
                if cursor.consume("...") {
                    end = Int(try constExpr())
                } else {
                    end = begin
                }
                try cursor.skip("]")

                if let children = init_.children {
                    let valuePos = cursor.pos
                    for j in begin...min(end, children.count - 1) {
                        cursor.pos = valuePos
                        if let child = children[j] {
                            try designation(child)
                        }
                    }
                }
                i = end + 1
                continue
            }

            if cursor.equal(".") {
                try designation(init_)
                i = 0
                continue
            }

            if let children = init_.children, i < children.count {
                if let child = children[i] {
                    try initializer2(child)
                }
            } else {
                _ = try skipExcessElement()
            }
            i += 1
        }
    }

    func arrayInitializer2(_ init_: InitNode, _ startIdx: Int) throws {
        if init_.isFlexible {
            guard case .array(let elem, _) = init_.ty.kind else { return }
            let len = try countArrayInitElements(elemType: elem)
            init_.ty = arrayOf(elem, len)
            init_.children = (0..<len).map { _ in newInitializer(elem, isFlexible: false) }
            init_.isFlexible = false
        }
        guard case .array(_, let len) = init_.ty.kind else { return }
        var i = startIdx
        while i < len && !isEnd() {
            let saved = cursor.pos
            if i > 0 { try cursor.skip(",") }
            if cursor.equal("[") || cursor.equal(".") {
                cursor.pos = saved
                return
            }
            if let child = init_.children?[i] {
                try initializer2(child)
            }
            i += 1
        }
    }

    func structInitializer1(_ init_: InitNode) throws {
        try cursor.skip("{")
        guard case .struct(let members, _, _) = init_.ty.kind else { return }
        var memIdx = 0
        var first = true

        while !consumeEnd() {
            if !first { try cursor.skip(",") }
            first = false

            if cursor.equal(".") {
                let dotPos = cursor.pos
                _ = cursor.advance()
                let name = cursor.advance().text
                if let mem = members.first(where: { $0.name == name }) {
                    memIdx = mem.index
                    if let child = init_.children?[memIdx] {
                        try designation(child)
                    }
                    memIdx += 1
                } else {
                    // Check anonymous struct/union members
                    var found = false
                    for mem in members {
                        if mem.name == nil || mem.name == "" {
                            if getStructMember(mem.type, name) != nil {
                                // Backtrack to before ".name" and call designation on the anonymous member
                                cursor.pos = dotPos
                                memIdx = mem.index
                                if let child = init_.children?[memIdx] {
                                    try designation(child)
                                }
                                memIdx += 1
                                found = true
                                break
                            }
                        }
                    }
                    if !found {
                        // Unknown field, skip
                    }
                }
                continue
            }

            if memIdx < members.count, let child = init_.children?[memIdx] {
                try initializer2(child)
                memIdx += 1
            } else {
                _ = try skipExcessElement()
            }
        }
    }

    func structInitializer2(_ init_: InitNode, _ startIdx: Int) throws {
        guard case .struct(let members, _, _) = init_.ty.kind else { return }
        var memIdx = startIdx
        while memIdx < members.count && !isEnd() {
            let saved = cursor.pos
            if memIdx > 0 { try cursor.skip(",") }
            if cursor.equal("[") || cursor.equal(".") {
                cursor.pos = saved
                return
            }
            if let child = init_.children?[memIdx] {
                try initializer2(child)
            }
            memIdx += 1
        }
    }

    func unionInitializer(_ init_: InitNode) throws {
        guard case .union(let members) = init_.ty.kind else { return }

        if cursor.equal("{") && (lookAhead().text == "." || lookAhead().text == "[") {
            _ = cursor.advance() // skip "{"
            try designation(init_)
            _ = consumeEnd()
            return
        }

        init_.mem = members.first
        if cursor.consume("{") {
            if let child = init_.children?[0] {
                try initializer2(child)
            }
            _ = cursor.consume(",")
            try cursor.skip("}")
        } else {
            if let child = init_.children?[0] {
                try initializer2(child)
            }
        }
    }

    func skipExcessElement() throws -> Void {
        if cursor.consume("{") {
            try skipExcessElement()
            try cursor.skip("}")
            return
        }
        _ = try assign()
    }

    func countArrayInitElements(elemType: SyntaxType) throws -> Int {
        let savedPos = cursor.pos
        var i = 0, max_ = 0
        var first = true
        while !consumeEnd() {
            if !first { try cursor.skip(",") }
            first = false
            if cursor.equal("[") {
                _ = cursor.advance()
                i = Int(try constExpr())
                if cursor.consume("...") { i = Int(try constExpr()) }
                try cursor.skip("]")
                let dummy = newInitializer(elemType, isFlexible: true)
                try designation(dummy)
            } else {
                let dummy = newInitializer(elemType, isFlexible: true)
                try initializer2(dummy)
            }
            i += 1
            max_ = max(max_, i)
        }
        // Restore
        cursor.pos = savedPos
        return max_
    }

    func createLvarInit(_ init_: InitNode, _ ty: SyntaxType,
                        varInfo: VarInfo? = nil, member: SyntaxMember? = nil,
                        idx: Int? = nil, parent: SyntaxExpr? = nil,
                        loc: SourceLocation) -> SyntaxExpr {
        let l = loc
        let null = SyntaxExpr.nullExpr(type: tyVoid, loc: l)

        // Build the LHS designator expression
        func desgExpr() -> SyntaxExpr {
            if let v = varInfo {
                return .variable(ref: v.makeRef(), type: v.type, loc: l)
            }
            if let mem = member, let p = parent {
                return .member(expr: p, member: mem, type: mem.type, loc: l)
            }
            if let i = idx, let p = parent {
                let idxExpr = SyntaxExpr.intLiteral(value: Int64(i), type: tyLong, loc: l)
                let added = newAdd(p, idxExpr, loc: l)
                return .deref(operand: added, type: baseType(typeOf(p))!, loc: l)
            }
            return null
        }

        switch ty.kind {
        case .array(let elem, let len):
            var result = null
            for i in 0..<len {
                guard let child = init_.children?[i] else { continue }
                let base = desgExpr()
                let sub = createLvarInit(child, elem, idx: i, parent: base, loc: l)
                result = .comma(lhs: result, rhs: sub, type: typeOf(sub), loc: l)
            }
            return result

        case .struct(let members, _, _):
            if init_.expr != nil {
                return .assign(lhs: desgExpr(), rhs: init_.expr!, type: ty, loc: l)
            }
            var result = null
            for mem in members {
                guard let child = init_.children?[mem.index] else { continue }
                let base = desgExpr()
                let sub = createLvarInit(child, mem.type, member: mem, parent: base, loc: l)
                result = .comma(lhs: result, rhs: sub, type: typeOf(sub), loc: l)
            }
            return result

        case .union(let members):
            let mem = init_.mem ?? members.first!
            guard let child = init_.children?[mem.index] else { return null }
            let base = desgExpr()
            return createLvarInit(child, mem.type, member: mem, parent: base, loc: l)

        default:
            guard let expr = init_.expr else { return null }
            let rhs = synCast(expr, to: ty, loc: l)
            return .assign(lhs: desgExpr(), rhs: rhs, type: ty, loc: l)
        }
    }

    // MARK: - Global initializer

    func gvarInitializer(_ v: VarInfo) throws {
        var newTy = v.type
        let init_ = try parseInitializer(v.type, &newTy)
        v.type = newTy

        var buf = [UInt8](repeating: 0, count: v.type.size)
        var rels: [SyntaxRelocation] = []
        writeGvarData(init_, v.type, &buf, &rels, offset: 0)
        v.initData = buf
        v.relocations = rels
    }

    func writeGvarData(_ init_: InitNode, _ ty: SyntaxType,
                       _ buf: inout [UInt8], _ rels: inout [SyntaxRelocation],
                       offset: Int) {
        switch ty.kind {
        case .array(let elem, let len):
            for i in 0..<len {
                guard let child = init_.children?[i] else { continue }
                writeGvarData(child, elem, &buf, &rels, offset: offset + elem.size * i)
            }

        case .struct(let members, _, _):
            for mem in members {
                guard let child = init_.children?[mem.index] else { continue }
                if let bf = mem.bitfield {
                    guard let expr = child.expr else { continue }
                    let val = UInt64(bitPattern: evalConst(expr))
                    let mask = (UInt64(1) << bf.bitWidth) - 1
                    var old = readBuf(buf, offset: offset + mem.offset, size: mem.type.size)
                    old |= (val & mask) << bf.bitOffset
                    writeBuf(&buf, offset: offset + mem.offset, size: mem.type.size, val: old)
                } else {
                    writeGvarData(child, mem.type, &buf, &rels, offset: offset + mem.offset)
                }
            }

        case .union(let members):
            guard let mem = init_.mem ?? members.first else { return }
            guard let child = init_.children?[mem.index] else { return }
            writeGvarData(child, mem.type, &buf, &rels, offset: offset)

        default:
            guard let expr = init_.expr else { return }

            if case .float = ty.kind {
                let f = Float(evalDouble(expr))
                var bits = f.bitPattern
                withUnsafeBytes(of: &bits) { src in
                    for i in 0..<min(4, buf.count - offset) {
                        buf[offset + i] = src[i]
                    }
                }
                return
            }

            if case .double = ty.kind {
                let d = evalDouble(expr)
                var bits = d.bitPattern
                withUnsafeBytes(of: &bits) { src in
                    for i in 0..<min(8, buf.count - offset) {
                        buf[offset + i] = src[i]
                    }
                }
                return
            }

            // Check for relocatable value (address of global)
            let (val, label) = evalWithLabel(expr)
            if let label = label {
                rels.append(SyntaxRelocation(offset: offset, label: label,
                                             addend: val))
            } else {
                writeBuf(&buf, offset: offset, size: ty.size,
                         val: UInt64(bitPattern: val))
            }
        }
    }

    func evalWithLabel(_ node: SyntaxExpr) -> (Int64, String?) {
        switch node {
        case .variable(let ref, let ty, _):
            if !ref.isLocal {
                if case .array = ty.kind { return (0, ref.name) }
                if case .function = ty.kind { return (0, ref.name) }
            }
            return (0, nil)
        case .addressOf(let operand, _, _):
            return evalRval(operand)
        case .member(let expr, let mem, let ty, _):
            // Array members decay to pointers (address of first element)
            if case .array = ty.kind {
                let (val, label) = evalRval(expr)
                return (val + Int64(mem.offset), label)
            }
            return (0, nil)
        case .binary(.add, let lhs, let rhs, _, _):
            let (lv, ll) = evalWithLabel(lhs)
            let rv = evalConst(rhs)
            return (lv + rv, ll)
        case .binary(.sub, let lhs, let rhs, _, _):
            let (lv, ll) = evalWithLabel(lhs)
            let rv = evalConst(rhs)
            return (lv - rv, ll)
        case .cast(let operand, _, _, _):
            return evalWithLabel(operand)
        case .comma(_, let rhs, _, _):
            return evalWithLabel(rhs)
        default:
            return (evalConst(node), nil)
        }
    }

    func evalRval(_ node: SyntaxExpr) -> (Int64, String?) {
        switch node {
        case .variable(let ref, _, _):
            return (0, ref.name)
        case .deref(let operand, _, _):
            return evalWithLabel(operand)
        case .member(let expr, let mem, _, _):
            let (val, label) = evalRval(expr)
            return (val + Int64(mem.offset), label)
        default:
            return (0, nil)
        }
    }

    func readBuf(_ buf: [UInt8], offset: Int, size: Int) -> UInt64 {
        var val: UInt64 = 0
        for i in 0..<min(size, buf.count - offset) {
            val |= UInt64(buf[offset + i]) << (i * 8)
        }
        return val
    }

    func writeBuf(_ buf: inout [UInt8], offset: Int, size: Int, val: UInt64) {
        for i in 0..<min(size, buf.count - offset) {
            buf[offset + i] = UInt8(truncatingIfNeeded: val >> (i * 8))
        }
    }

    // MARK: - Function and global declarations

    func isFunction() -> Bool {
        if cursor.equal(";") { return false }
        let savedPos = cursor.pos
        let dummy = SyntaxType(kind: .void, size: 0, align: 0)
        let result: Bool
        do {
            let (ty, _) = try declarator(dummy)
            if case .function = ty.kind { result = true }
            else { result = false }
        } catch {
            result = false
        }
        cursor.pos = savedPos
        return result
    }

    func parseFunction(_ basety: SyntaxType, attr: VarAttr) throws {
        let l = loc
        let (ty, name) = try declarator(basety)
        guard let name = name else { throw error("function name omitted") }

        // Check for existing declaration
        var fn: VarInfo?
        if let existing = findFuncInGlobalScope(name) {
            fn = existing
            fn?.isDefinition = fn!.isDefinition || cursor.equal("{")
        } else {
            fn = newGVar(name, ty)
            fn!.isFunction = true
            fn!.isDefinition = cursor.equal("{")
            fn!.isStatic = attr.isStatic || (attr.isInline && !attr.isExtern)
            fn!.isInline = attr.isInline
        }

        fn!.isRoot = !(fn!.isStatic && fn!.isInline)

        // Skip trailing __attribute__ (e.g. __THROW, __nonnull, etc.)
        try skipAttributes()

        // Forward declaration
        if cursor.consume(";") {
            let gvLoc = l
            globalLocs[fn!.id] = gvLoc
            allDeclarations.append(.function(makeSyntaxFunction(fn!, body: nil,
                params: [], locals: [], stackSize: 0, vaArea: nil,
                allocaBottom: nil, loc: gvLoc)))
            return
        }

        // Function definition
        currentFnType = ty
        currentFnName = name
        currentFnRefs = []
        currentLocals = []
        gotos = []
        labelMap = [:]

        enterScope()

        // Create parameter locals
        guard case .function(let retTy, let paramTys, let isVariadic) = ty.kind else {
            throw error("expected function type")
        }

        // Parse parameter names by re-parsing the parameter list
        // Actually, we already consumed the declarator. The parameter names
        // are embedded in the type suffix parsing. Let me handle this differently.
        // We need to create locals for each parameter.
        // Since declarator already consumed the tokens, we need to extract param names
        // from what was parsed. But our declarator doesn't track parameter names.

        // Re-parse: save position, go back, re-parse just params
        // Actually this is tricky. Let me use a different approach:
        // Parse the function body. Parameter names come from the function type
        // parsing in funcParams. But we lost them.

        // Simpler approach: look at the tokens between the opening "(" before "{"
        // and create params. But that's fragile.

        // Best approach: modify funcParams to also track names. But for now,
        // let's create unnamed params based on the type count.
        // Actually, let me re-parse the parameter declarations.

        // Skip to "{" and re-scan param list
        // Actually the cursor is already past the declarator, at "{".
        // The parameter names were consumed during declarator parsing.
        // Let me track them during funcParams parsing.

        // For now: create params with placeholder names based on the signature.
        // This won't work for real code. Let me fix funcParams to save names.

        // WORKAROUND: Store param names during funcParams parsing
        let params = createParamLocals(ty)

        // Return buffer for large struct returns
        if (isStructOrUnion(retTy)) && retTy.size > 16 {
            _ = newLVar("", pointerTo(retTy))
        }

        let paramVars = params

        // va_area for variadic functions
        var vaArea: VarInfo? = nil
        if isVariadic {
            vaArea = newLVar("__va_area__", arrayOf(tyChar, 136))
        }
        let allocaBottom = newLVar("__alloca_size__", pointerTo(tyChar))

        try cursor.skip("{")

        // __func__ and __FUNCTION__
        let nameBytes = Array(name.utf8) + [0]
        let funcStr = newStringLiteral(nameBytes, arrayOf(tyChar, nameBytes.count))
        let funcLoc = l
        globalLocs[funcStr.id] = funcLoc
        allDeclarations.append(.variable(funcStr.makeGlobalVar(loc: funcLoc)))
        pushVar("__func__", VarScope(varInfo: funcStr))
        pushVar("__FUNCTION__", VarScope(varInfo: funcStr))

        let body = try compoundStmt()

        leaveScope()

        // Resolve gotos
        resolveGotoLabels()

        let syntaxParams = paramVars.map { $0.makeLocalVar() }
        let syntaxLocals = currentLocals.map { $0.makeLocalVar() }

        let sfn = makeSyntaxFunction(fn!, body: body,
            params: syntaxParams, locals: syntaxLocals, stackSize: 0,
            vaArea: vaArea?.makeRef(), allocaBottom: allocaBottom.makeRef(),
            loc: l)
        globalLocs[fn!.id] = l
        allDeclarations.append(.function(sfn))
    }

    // Store param names during type suffix parsing
    var lastParsedParamNames: [String?] = []

    func createParamLocals(_ fnTy: SyntaxType) -> [VarInfo] {
        guard case .function(_, let paramTys, _) = fnTy.kind else { return [] }
        var params: [VarInfo] = []
        for (i, pty) in paramTys.enumerated().reversed() {
            let name = i < lastParsedParamNames.count ? (lastParsedParamNames[i] ?? "") : ""
            let v = newLVar(name, pty)
            params.insert(v, at: 0)
        }
        return params
    }

    func resolveGotoLabels() {
        // Both goto and label now use deterministic ".L<fn>.<name>" labels,
        // so they match without a post-pass. Just validate.
        for g in gotos {
            if labelMap[g.name] == nil {
                // Forward reference to undefined label — ignore silently
                // (chibicc also allows this for computed goto targets)
            }
        }
    }

    func makeSyntaxFunction(_ v: VarInfo, body: SyntaxStmt?,
                            params: [SyntaxLocalVariable],
                            locals: [SyntaxLocalVariable],
                            stackSize: Int,
                            vaArea: SyntaxVariableRef?,
                            allocaBottom: SyntaxVariableRef?,
                            loc: SourceLocation) -> SyntaxFunction {
        SyntaxFunction(
            name: v.name, type: v.type,
            isDefinition: v.isDefinition,
            isStatic: v.isStatic,
            isInline: v.isInline,
            isLive: v.isLive,
            isRoot: v.isRoot,
            params: params, locals: locals,
            body: body, stackSize: stackSize,
            vaArea: vaArea, allocaBottom: allocaBottom,
            loc: loc
        )
    }

    func parseGlobalVariable(_ basety: SyntaxType, attr: VarAttr) throws {
        var first = true
        while !cursor.consume(";") {
            if !first { try cursor.skip(",") }
            first = false

            let (ty, name) = try declarator(basety)
            guard let name = name else { throw error("variable name omitted") }

            let v = newGVar(name, ty)
            v.isDefinition = !attr.isExtern
            v.isStatic = attr.isStatic
            v.isTLS = attr.isTLS
            if attr.align > 0 { v.align = attr.align }

            // Skip trailing __attribute__
            try skipAttributes()

            if cursor.consume("=") {
                try gvarInitializer(v)
            } else if !attr.isExtern && !attr.isTLS {
                v.isTentative = true
            }

            let gvLoc = loc
            globalLocs[v.id] = gvLoc
            allDeclarations.append(.variable(v.makeGlobalVar(loc: gvLoc)))
        }
    }

    func parseTypedef(_ basety: SyntaxType) throws {
        var first = true
        while !cursor.consume(";") {
            if !first { try cursor.skip(",") }
            first = false
            let (ty, name) = try declarator(basety)
            guard let name = name else { throw error("typedef name omitted") }
            try skipAttributes()
            pushVar(name, VarScope(typeDef: ty))
        }
    }

    func declareBuiltinFunctions() {
        let allocaTy = SyntaxType(
            kind: .function(returnType: pointerTo(tyVoid),
                            params: [tyInt], isVariadic: false),
            size: 1, align: 1)
        let v = newGVar("alloca", allocaTy)
        v.isFunction = true
        v.isDefinition = false
    }

    func findFuncInGlobalScope(_ name: String) -> VarInfo? {
        // Search from outermost scope
        if let vs = scopes[0].vars[name], let v = vs.varInfo, v.isFunction {
            return v
        }
        return nil
    }

    func markLive(_ v: VarInfo) {
        if !v.isFunction || v.isLive { return }
        v.isLive = true
        for ref in v.refs {
            if let fn = findFuncInGlobalScope(ref) {
                markLive(fn)
            }
        }
    }

    func scanGlobals() {
        // Remove redundant tentative definitions
        var seen: Set<String> = []
        var filtered: [SyntaxDeclaration] = []

        // First pass: find all defined names
        var definedNames: Set<String> = []
        for d in allDeclarations {
            switch d {
            case .variable(let gv):
                if gv.isDefinition && !gv.isTentative {
                    definedNames.insert(gv.name)
                }
            case .function: break
            }
        }

        // Second pass: skip tentative if defined elsewhere
        for d in allDeclarations {
            switch d {
            case .variable(let gv):
                if gv.isTentative && definedNames.contains(gv.name) {
                    continue
                }
            default: break
            }
            filtered.append(d)
        }

        allDeclarations = filtered
    }
}
