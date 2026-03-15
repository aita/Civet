// Type system helpers for the C parser.
// Ported from chibicc's type.c.

import Syntax

// MARK: - Shared type constants

let tyVoid = SyntaxType(kind: .void, size: 1, align: 1)
let tyBool = SyntaxType(kind: .bool, size: 1, align: 1)
let tyChar = SyntaxType(kind: .char(isUnsigned: false), size: 1, align: 1)
let tyShort = SyntaxType(kind: .short(isUnsigned: false), size: 2, align: 2)
let tyInt = SyntaxType(kind: .int(isUnsigned: false), size: 4, align: 4)
let tyLong = SyntaxType(kind: .long(isUnsigned: false), size: 8, align: 8)
let tyUChar = SyntaxType(kind: .char(isUnsigned: true), size: 1, align: 1)
let tyUShort = SyntaxType(kind: .short(isUnsigned: true), size: 2, align: 2)
let tyUInt = SyntaxType(kind: .int(isUnsigned: true), size: 4, align: 4)
let tyULong = SyntaxType(kind: .long(isUnsigned: true), size: 8, align: 8)
let tyFloat = SyntaxType(kind: .float, size: 4, align: 4)
let tyDouble = SyntaxType(kind: .double, size: 8, align: 8)
let tyLDouble = SyntaxType(kind: .longDouble, size: 16, align: 16)

// MARK: - Type predicates

func isInteger(_ ty: SyntaxType) -> Bool {
    switch ty.kind {
    case .bool, .char, .short, .int, .long, .enum: return true
    default: return false
    }
}

func isFlonum(_ ty: SyntaxType) -> Bool {
    switch ty.kind {
    case .float, .double, .longDouble: return true
    default: return false
    }
}

func isNumeric(_ ty: SyntaxType) -> Bool {
    isInteger(ty) || isFlonum(ty)
}

func isUnsigned(_ ty: SyntaxType) -> Bool {
    switch ty.kind {
    case .bool: return true
    case .char(let u), .short(let u), .int(let u), .long(let u): return u
    case .pointer: return true
    default: return false
    }
}

func isPointerLike(_ ty: SyntaxType) -> Bool {
    switch ty.kind {
    case .pointer: return true
    default: return false
    }
}

func baseType(_ ty: SyntaxType) -> SyntaxType? {
    switch ty.kind {
    case .pointer(let p): return p
    case .array(let e, _): return e
    case .vla(let e, _): return e
    default: return nil
    }
}

// MARK: - Type construction

func pointerTo(_ base: SyntaxType) -> SyntaxType {
    SyntaxType(kind: .pointer(pointee: base), size: 8, align: 8)
}

func arrayOf(_ base: SyntaxType, _ len: Int) -> SyntaxType {
    SyntaxType(kind: .array(element: base, length: len), size: base.size * len, align: base.align)
}

func funcType(_ ret: SyntaxType) -> SyntaxType {
    SyntaxType(kind: .function(returnType: ret, params: [], isVariadic: false), size: 1, align: 1)
}

func enumType() -> SyntaxType {
    SyntaxType(kind: .enum, size: 4, align: 4)
}

func structType() -> SyntaxType {
    SyntaxType(kind: .void, size: 0, align: 1) // placeholder, mutated later
}

func copyType(_ ty: SyntaxType) -> SyntaxType {
    SyntaxType(kind: ty.kind, size: ty.size, align: ty.align,
               isAtomic: ty.isAtomic, name: ty.name)
}

// MARK: - Usual arithmetic conversion

func getCommonType(_ ty1: SyntaxType, _ ty2: SyntaxType) -> SyntaxType {
    if baseType(ty1) != nil { return pointerTo(baseType(ty1)!) }

    if case .function = ty1.kind { return pointerTo(ty1) }
    if case .function = ty2.kind { return pointerTo(ty2) }

    if case .longDouble = ty1.kind { return tyLDouble }
    if case .longDouble = ty2.kind { return tyLDouble }
    if case .double = ty1.kind { return tyDouble }
    if case .double = ty2.kind { return tyDouble }
    if case .float = ty1.kind { return tyFloat }
    if case .float = ty2.kind { return tyFloat }

    let t1 = ty1.size < 4 ? tyInt : ty1
    let t2 = ty2.size < 4 ? tyInt : ty2

    if t1.size != t2.size {
        return t1.size < t2.size ? t2 : t1
    }
    if isUnsigned(t2) { return t2 }
    return t1
}

// MARK: - Type compatibility

func isCompatible(_ t1: SyntaxType, _ t2: SyntaxType) -> Bool {
    if t1 === t2 { return true }
    if typeKindTag(t1) != typeKindTag(t2) { return false }

    switch t1.kind {
    case .char(let u1):
        if case .char(let u2) = t2.kind { return u1 == u2 }
        return false
    case .short(let u1):
        if case .short(let u2) = t2.kind { return u1 == u2 }
        return false
    case .int(let u1):
        if case .int(let u2) = t2.kind { return u1 == u2 }
        return false
    case .long(let u1):
        if case .long(let u2) = t2.kind { return u1 == u2 }
        return false
    case .float, .double, .longDouble:
        return true
    case .pointer(let p1):
        if case .pointer(let p2) = t2.kind { return isCompatible(p1, p2) }
        return false
    case .function(let r1, let ps1, let v1):
        if case .function(let r2, let ps2, let v2) = t2.kind {
            if !isCompatible(r1, r2) { return false }
            if v1 != v2 { return false }
            if ps1.count != ps2.count { return false }
            for (a, b) in zip(ps1, ps2) { if !isCompatible(a, b) { return false } }
            return true
        }
        return false
    case .array(let e1, let l1):
        if case .array(let e2, let l2) = t2.kind {
            return isCompatible(e1, e2) && l1 == l2
        }
        return false
    default:
        return false
    }
}

private func typeKindTag(_ ty: SyntaxType) -> Int {
    switch ty.kind {
    case .void: return 0
    case .bool: return 1
    case .char: return 2
    case .short: return 3
    case .int: return 4
    case .long: return 5
    case .float: return 6
    case .double: return 7
    case .longDouble: return 8
    case .enum: return 9
    case .pointer: return 10
    case .array: return 11
    case .vla: return 12
    case .struct: return 13
    case .union: return 14
    case .function: return 15
    }
}

// MARK: - Extract type from SyntaxExpr

func typeOf(_ e: SyntaxExpr) -> SyntaxType {
    switch e {
    case .nullExpr(let t, _): return t
    case .intLiteral(_, let t, _): return t
    case .floatLiteral(_, let t, _): return t
    case .variable(_, let t, _): return t
    case .vlaPtr(_, let t, _): return t
    case .binary(_, _, _, let t, _): return t
    case .unary(_, _, let t, _): return t
    case .logical(_, _, _, let t, _): return t
    case .addressOf(_, let t, _): return t
    case .deref(_, let t, _): return t
    case .member(_, _, let t, _): return t
    case .assign(_, _, let t, _): return t
    case .ternary(_, _, _, let t, _): return t
    case .comma(_, _, let t, _): return t
    case .cast(_, _, let t, _): return t
    case .call(_, _, _, _, let t, _): return t
    case .stmtExpr(_, let t, _): return t
    case .labelValue(_, _, let t, _): return t
    case .cas(_, _, _, let t, _): return t
    case .exchange(_, _, let t, _): return t
    case .memzero(_, let t, _): return t
    }
}

// MARK: - Alignment helpers

func alignTo(_ n: Int, _ align: Int) -> Int {
    guard align > 0 else { return n }
    return (n + align - 1) / align * align
}

func alignDown(_ n: Int, _ align: Int) -> Int {
    alignTo(n - align + 1, align)
}
