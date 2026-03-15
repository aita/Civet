// Variable/typedef/tag scoping for the C parser.

import Syntax

// MARK: - Variable info

/// Tracks a declared variable (local or global) with a unique ID.
class VarInfo {
    let name: String
    var type: SyntaxType
    let isLocal: Bool
    let id: Int
    var align: Int

    // Global-specific
    var isFunction: Bool = false
    var isDefinition: Bool = false
    var isStatic: Bool = false
    var isInline: Bool = false
    var isLive: Bool = false
    var isRoot: Bool = false
    var isTentative: Bool = false
    var isTLS: Bool = false
    var initData: [UInt8]? = nil
    var relocations: [SyntaxRelocation] = []
    var refs: [String] = [] // for static inline liveness

    init(name: String, type: SyntaxType, isLocal: Bool, id: Int) {
        self.name = name
        self.type = type
        self.isLocal = isLocal
        self.id = id
        self.align = type.align
    }

    func makeRef() -> SyntaxVariableRef {
        SyntaxVariableRef(name: name, isLocal: isLocal, id: id)
    }

    func makeLocalVar() -> SyntaxLocalVariable {
        SyntaxLocalVariable(name: name, type: type, offset: 0, align: align, id: id)
    }

    func makeGlobalVar(loc: SourceLocation) -> SyntaxGlobalVariable {
        SyntaxGlobalVariable(
            name: name, type: type,
            isDefinition: isDefinition,
            isStatic: isStatic,
            isTentative: isTentative,
            isTLS: isTLS,
            align: align,
            initData: initData, relocations: relocations,
            loc: loc
        )
    }
}

// MARK: - Scope types

struct VarScope {
    var varInfo: VarInfo? = nil
    var typeDef: SyntaxType? = nil
    var enumTy: SyntaxType? = nil
    var enumVal: Int = 0
}

struct Scope {
    var vars: [String: VarScope] = [:]
    var tags: [String: SyntaxType] = [:]
}

struct VarAttr {
    var isTypedef: Bool = false
    var isStatic: Bool = false
    var isExtern: Bool = false
    var isInline: Bool = false
    var isTLS: Bool = false
    var align: Int = 0
}

// MARK: - Initializer tree

class InitNode {
    var ty: SyntaxType
    var expr: SyntaxExpr? = nil
    var children: [InitNode?]? = nil
    var isFlexible: Bool = false
    var mem: SyntaxMember? = nil // for unions: which member is initialized

    init(ty: SyntaxType) {
        self.ty = ty
    }
}

func newInitializer(_ ty: SyntaxType, isFlexible: Bool) -> InitNode {
    let init_ = InitNode(ty: ty)

    switch ty.kind {
    case .array(let elem, let len):
        if isFlexible && ty.size < 0 {
            init_.isFlexible = true
            return init_
        }
        init_.children = (0..<len).map { _ in newInitializer(elem, isFlexible: false) }

    case .struct(let members, let flex, _):
        init_.children = Array(repeating: nil as InitNode?, count: members.count)
        for mem in members {
            let isLastFlexible = isFlexible && flex && mem.index == members.count - 1
            if isLastFlexible {
                let child = InitNode(ty: mem.type)
                child.isFlexible = true
                init_.children![mem.index] = child
            } else {
                init_.children![mem.index] = newInitializer(mem.type, isFlexible: false)
            }
        }

    case .union(let members):
        init_.children = Array(repeating: nil as InitNode?, count: members.count)
        for mem in members {
            init_.children![mem.index] = newInitializer(mem.type, isFlexible: false)
        }

    default:
        break
    }

    return init_
}

// InitDesg not needed — designator logic is inlined in createLvarInit.
