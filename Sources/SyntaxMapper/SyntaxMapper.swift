import ChibiCC
import Syntax

// MARK: - Errors

public enum MappingError: Error, CustomStringConvertible {
    case nullPointer(context: String)
    case unsupportedNodeKind(UInt32, SourceLocation?)
    case unsupportedTypeKind(UInt32)
    case invalidState(String)

    public var description: String {
        switch self {
        case .nullPointer(let ctx):
            "Null pointer: \(ctx)"
        case .unsupportedNodeKind(let kind, let loc):
            "Unsupported node kind \(kind) at \(loc.map { "\($0)" } ?? "unknown")"
        case .unsupportedTypeKind(let kind):
            "Unsupported type kind \(kind)"
        case .invalidState(let msg):
            "Invalid state: \(msg)"
        }
    }
}

// MARK: - SyntaxMapper

public final class SyntaxMapper {

    private var typeCache: [UnsafeRawPointer: SyntaxType] = [:]
    private var variableIDs: [UnsafeRawPointer: Int] = [:]
    private var nextVariableID: Int = 1

    public init() {}

    // MARK: - Public API

    public func parseFile(
        _ path: String,
        includePaths: [String] = []
    ) throws -> SyntaxTranslationUnit {
        civet_clear_include_paths()
        for p in includePaths {
            p.withCString { civet_add_include_path(strdup($0)) }
        }
        path.withCString { civet_set_base_file($0) }
        init_macros()

        guard let tokens = path.withCString({ tokenize_file(UnsafeMutablePointer(mutating: $0)) }) else {
            throw MappingError.invalidState("Tokenization failed")
        }
        let preprocessed = preprocess(tokens)
        guard let prog = parse(preprocessed) else {
            throw MappingError.invalidState("Parse returned nil")
        }
        let result = try mapTranslationUnit(prog)

        // Free C-side memory and reset global state for reuse
        chibicc_reset()

        // Clear Swift-side caches (C pointers are now invalid)
        typeCache.removeAll()
        variableIDs.removeAll()
        nextVariableID = 0

        return result
    }

    public func mapTranslationUnit(
        _ prog: UnsafeMutablePointer<Obj>
    ) throws -> SyntaxTranslationUnit {
        let objects = collectLinkedList(prog, next: { $0.pointee.next })
        var declarations: [SyntaxDeclaration] = []
        for obj in objects {
            if obj.pointee.is_function {
                declarations.append(.function(try mapFunction(obj)))
            } else {
                declarations.append(.variable(try mapGlobalVariable(obj)))
            }
        }
        return SyntaxTranslationUnit(declarations: declarations)
    }

    // MARK: - Type Mapping

    public func mapType(
        _ ty: UnsafeMutablePointer<ChibiCC.`Type`>
    ) throws -> SyntaxType {
        let key = UnsafeRawPointer(ty)
        if let cached = typeCache[key] { return cached }

        let name = extractTypeName(ty)
        let size = Int(ty.pointee.size)
        let align = Int(ty.pointee.align)
        let isAtomic = ty.pointee.is_atomic

        switch ty.pointee.kind {
        case TY_VOID:
            return cache(key, .void, size: size, align: align,
                         isAtomic: isAtomic, name: name)
        case TY_BOOL:
            return cache(key, .bool, size: size, align: align,
                         isAtomic: isAtomic, name: name)
        case TY_CHAR:
            return cache(key, .char(isUnsigned: ty.pointee.is_unsigned),
                         size: size, align: align, isAtomic: isAtomic, name: name)
        case TY_SHORT:
            return cache(key, .short(isUnsigned: ty.pointee.is_unsigned),
                         size: size, align: align, isAtomic: isAtomic, name: name)
        case TY_INT:
            return cache(key, .int(isUnsigned: ty.pointee.is_unsigned),
                         size: size, align: align, isAtomic: isAtomic, name: name)
        case TY_LONG:
            return cache(key, .long(isUnsigned: ty.pointee.is_unsigned),
                         size: size, align: align, isAtomic: isAtomic, name: name)
        case TY_FLOAT:
            return cache(key, .float, size: size, align: align,
                         isAtomic: isAtomic, name: name)
        case TY_DOUBLE:
            return cache(key, .double, size: size, align: align,
                         isAtomic: isAtomic, name: name)
        case TY_LDOUBLE:
            return cache(key, .longDouble, size: size, align: align,
                         isAtomic: isAtomic, name: name)
        case TY_ENUM:
            return cache(key, .enum, size: size, align: align,
                         isAtomic: isAtomic, name: name)

        case TY_PTR:
            // Insert placeholder to break cycles (updated in-place below)
            let placeholder = SyntaxType(kind: .void, size: size, align: align,
                                         isAtomic: isAtomic, name: name)
            typeCache[key] = placeholder

            let pointeeType: SyntaxType
            if let base = ty.pointee.base {
                pointeeType = try mapType(base)
            } else {
                pointeeType = SyntaxType(kind: .void, size: 1, align: 1)
            }
            placeholder.kind = .pointer(pointee: pointeeType)
            return placeholder

        case TY_ARRAY:
            guard let base = ty.pointee.base else {
                throw MappingError.invalidState("Array type without base type")
            }
            let element = try mapType(base)
            return cache(key, .array(element: element, length: Int(ty.pointee.array_len)),
                         size: size, align: align, isAtomic: isAtomic, name: name)

        case TY_VLA:
            guard let base = ty.pointee.base else {
                throw MappingError.invalidState("VLA type without base type")
            }
            let element = try mapType(base)
            return cache(key, .vla(element: element, sizeVar: nil),
                         size: size, align: align, isAtomic: isAtomic, name: name)

        case TY_STRUCT:
            let placeholder = SyntaxType(kind: .void, size: size, align: align,
                                         isAtomic: isAtomic, name: name)
            typeCache[key] = placeholder
            let members = try mapMembers(ty.pointee.members)
            placeholder.kind = .struct(members: members,
                                       isFlexible: ty.pointee.is_flexible,
                                       isPacked: ty.pointee.is_packed)
            return placeholder

        case TY_UNION:
            let placeholder = SyntaxType(kind: .void, size: size, align: align,
                                         isAtomic: isAtomic, name: name)
            typeCache[key] = placeholder
            let members = try mapMembers(ty.pointee.members)
            placeholder.kind = .union(members: members)
            return placeholder

        case TY_FUNC:
            guard let retTy = ty.pointee.return_ty else {
                throw MappingError.invalidState("Function type without return type")
            }
            let returnType = try mapType(retTy)
            let paramTypes = try collectLinkedList(ty.pointee.params,
                                                   next: { $0.pointee.next })
                .map { try mapType($0) }
            return cache(key,
                         .function(returnType: returnType, params: paramTypes,
                                   isVariadic: ty.pointee.is_variadic),
                         size: size, align: align, isAtomic: isAtomic, name: name)

        default:
            throw MappingError.unsupportedTypeKind(ty.pointee.kind.rawValue)
        }
    }

    // MARK: - Expression Mapping

    public func mapExpr(_ node: UnsafeMutablePointer<Node>) throws -> SyntaxExpr {
        let loc = extractLocation(node.pointee.tok)
        let type = try mapNodeType(node)

        switch node.pointee.kind {
        case ND_NULL_EXPR:
            return .nullExpr(type: type, loc: loc)

        case ND_NUM:
            if isFloatingType(type) {
                return .floatLiteral(value: Double(node.pointee.fval),
                                     type: type, loc: loc)
            } else {
                return .intLiteral(value: node.pointee.val, type: type, loc: loc)
            }

        case ND_VAR:
            return .variable(ref: try mapVariableRef(node.pointee.`var`),
                             type: type, loc: loc)

        case ND_VLA_PTR:
            return .vlaPtr(ref: try mapVariableRef(node.pointee.`var`),
                           type: type, loc: loc)

        case ND_ADD, ND_SUB, ND_MUL, ND_DIV, ND_MOD,
             ND_BITAND, ND_BITOR, ND_BITXOR, ND_SHL, ND_SHR,
             ND_EQ, ND_NE, ND_LT, ND_LE:
            let op = mapBinaryOp(node.pointee.kind)
            return .binary(op: op,
                           lhs: try mapExpr(node.pointee.lhs),
                           rhs: try mapExpr(node.pointee.rhs),
                           type: type, loc: loc)

        case ND_NEG:
            return .unary(op: .neg, operand: try mapExpr(node.pointee.lhs),
                          type: type, loc: loc)
        case ND_NOT:
            return .unary(op: .logNot, operand: try mapExpr(node.pointee.lhs),
                          type: type, loc: loc)
        case ND_BITNOT:
            return .unary(op: .bitNot, operand: try mapExpr(node.pointee.lhs),
                          type: type, loc: loc)

        case ND_LOGAND:
            return .logical(op: .and,
                            lhs: try mapExpr(node.pointee.lhs),
                            rhs: try mapExpr(node.pointee.rhs),
                            type: type, loc: loc)
        case ND_LOGOR:
            return .logical(op: .or,
                            lhs: try mapExpr(node.pointee.lhs),
                            rhs: try mapExpr(node.pointee.rhs),
                            type: type, loc: loc)

        case ND_ADDR:
            return .addressOf(operand: try mapExpr(node.pointee.lhs),
                              type: type, loc: loc)
        case ND_DEREF:
            return .deref(operand: try mapExpr(node.pointee.lhs),
                          type: type, loc: loc)

        case ND_MEMBER:
            return .member(expr: try mapExpr(node.pointee.lhs),
                           member: try mapSingleMember(node.pointee.member),
                           type: type, loc: loc)

        case ND_ASSIGN:
            return .assign(lhs: try mapExpr(node.pointee.lhs),
                           rhs: try mapExpr(node.pointee.rhs),
                           type: type, loc: loc)

        case ND_COND:
            return .ternary(cond: try mapExpr(node.pointee.cond),
                            then: try mapExpr(node.pointee.then),
                            els: try mapExpr(node.pointee.els),
                            type: type, loc: loc)

        case ND_COMMA:
            return .comma(lhs: try mapExpr(node.pointee.lhs),
                          rhs: try mapExpr(node.pointee.rhs),
                          type: type, loc: loc)

        case ND_CAST:
            return .cast(operand: try mapExpr(node.pointee.lhs),
                         toType: type, type: type, loc: loc)

        case ND_FUNCALL:
            let callee = try mapExpr(node.pointee.lhs)
            let args = try collectLinkedList(node.pointee.args,
                                             next: { $0.pointee.next })
                .map { try mapExpr($0) }
            let funcType = try mapType(node.pointee.func_ty)
            let retBuf: SyntaxVariableRef? = try node.pointee.ret_buffer
                .map { try mapVariableRef($0) }
            return .call(callee: callee, args: args, funcType: funcType,
                         returnBuffer: retBuf, type: type, loc: loc)

        case ND_STMT_EXPR:
            let stmts = try collectLinkedList(node.pointee.body,
                                              next: { $0.pointee.next })
                .map { try mapStmt($0) }
            return .stmtExpr(body: stmts, type: type, loc: loc)

        case ND_LABEL_VAL:
            return .labelValue(label: String(cString: node.pointee.label),
                               uniqueLabel: String(cString: node.pointee.unique_label),
                               type: type, loc: loc)

        case ND_CAS:
            return .cas(addr: try mapExpr(node.pointee.cas_addr),
                        old: try mapExpr(node.pointee.cas_old),
                        new: try mapExpr(node.pointee.cas_new),
                        type: type, loc: loc)

        case ND_EXCH:
            return .exchange(addr: try mapExpr(node.pointee.lhs),
                             value: try mapExpr(node.pointee.rhs),
                             type: type, loc: loc)

        case ND_MEMZERO:
            // Use the variable's actual type (not the node type, which is void).
            let varType = try mapType(node.pointee.`var`.pointee.ty)
            return .memzero(variable: try mapVariableRef(node.pointee.`var`),
                            type: varType, loc: loc)

        default:
            throw MappingError.unsupportedNodeKind(node.pointee.kind.rawValue, loc)
        }
    }

    // MARK: - Statement Mapping

    public func mapStmt(_ node: UnsafeMutablePointer<Node>) throws -> SyntaxStmt {
        let loc = extractLocation(node.pointee.tok)

        switch node.pointee.kind {
        case ND_EXPR_STMT:
            return .expr(try mapExpr(node.pointee.lhs), loc: loc)

        case ND_RETURN:
            let value: SyntaxExpr? = try node.pointee.lhs.map { try mapExpr($0) }
            return .return(value: value, loc: loc)

        case ND_BLOCK:
            let stmts = try collectLinkedList(node.pointee.body,
                                              next: { $0.pointee.next })
                .map { try mapStmt($0) }
            return .block(stmts, loc: loc)

        case ND_IF:
            let cond = try mapExpr(node.pointee.cond)
            let then = try mapStmt(node.pointee.then)
            let els: SyntaxStmt? = try node.pointee.els.map { try mapStmt($0) }
            return .if(cond: cond, then: then, else: els, loc: loc)

        case ND_FOR:
            let initStmt: SyntaxStmt? = try node.pointee.`init`
                .map { try mapStmt($0) }
            let cond: SyntaxExpr? = try node.pointee.cond.map { try mapExpr($0) }
            let inc: SyntaxExpr? = try node.pointee.inc.map { try mapExpr($0) }
            let body = try mapStmt(node.pointee.then)
            return .for(init: initStmt, cond: cond, inc: inc, body: body,
                        breakLabel: optCStr(node.pointee.brk_label),
                        continueLabel: optCStr(node.pointee.cont_label),
                        loc: loc)

        case ND_DO:
            let body = try mapStmt(node.pointee.then)
            let cond = try mapExpr(node.pointee.cond)
            return .doWhile(body: body, cond: cond,
                            breakLabel: optCStr(node.pointee.brk_label),
                            continueLabel: optCStr(node.pointee.cont_label),
                            loc: loc)

        case ND_SWITCH:
            let cond = try mapExpr(node.pointee.cond)
            let body = try mapStmt(node.pointee.then)

            var cases: [CaseInfo] = []
            var caseNode = node.pointee.case_next
            while let cn = caseNode {
                cases.append(CaseInfo(
                    begin: Int64(cn.pointee.begin),
                    end: Int64(cn.pointee.end),
                    label: String(cString: cn.pointee.label)
                ))
                caseNode = cn.pointee.case_next
            }

            let defaultLabel: String? = node.pointee.default_case
                .map { String(cString: $0.pointee.label) }

            return .switch(cond: cond, body: body, cases: cases,
                           defaultLabel: defaultLabel,
                           breakLabel: optCStr(node.pointee.brk_label),
                           loc: loc)

        case ND_CASE:
            return .case(begin: Int64(node.pointee.begin),
                         end: Int64(node.pointee.end),
                         label: String(cString: node.pointee.label),
                         body: try mapStmt(node.pointee.lhs),
                         loc: loc)

        case ND_GOTO:
            return .goto(uniqueLabel: String(cString: node.pointee.unique_label),
                         loc: loc)

        case ND_GOTO_EXPR:
            return .gotoExpr(target: try mapExpr(node.pointee.lhs), loc: loc)

        case ND_LABEL:
            return .label(name: String(cString: node.pointee.label),
                          uniqueLabel: String(cString: node.pointee.unique_label),
                          body: try mapStmt(node.pointee.lhs),
                          loc: loc)

        case ND_MEMZERO:
            let varType = try mapType(node.pointee.`var`.pointee.ty)
            return .memzero(variable: try mapVariableRef(node.pointee.`var`),
                            type: varType, loc: loc)

        case ND_ASM:
            return .asm(String(cString: node.pointee.asm_str), loc: loc)

        default:
            throw MappingError.unsupportedNodeKind(node.pointee.kind.rawValue, loc)
        }
    }

    // MARK: - Obj Mapping

    public func mapFunction(
        _ obj: UnsafeMutablePointer<Obj>
    ) throws -> SyntaxFunction {
        let name = String(cString: obj.pointee.name)
        let type = try mapType(obj.pointee.ty)
        let loc = extractLocation(obj.pointee.tok)

        var params: [SyntaxLocalVariable] = []
        var locals: [SyntaxLocalVariable] = []
        var body: SyntaxStmt? = nil
        var stackSize = 0
        var vaArea: SyntaxVariableRef? = nil
        var allocaBottom: SyntaxVariableRef? = nil

        if obj.pointee.is_definition {
            params = try collectLinkedList(obj.pointee.params, next: { $0.pointee.next })
                .map { try mapLocalVariable($0) }
            locals = try collectLinkedList(obj.pointee.locals, next: { $0.pointee.next })
                .map { try mapLocalVariable($0) }
            if let bodyNode = obj.pointee.body {
                body = try mapStmt(bodyNode)
            }
            stackSize = Int(obj.pointee.stack_size)
            if let va = obj.pointee.va_area {
                vaArea = try mapVariableRef(va)
            }
            if let ab = obj.pointee.alloca_bottom {
                allocaBottom = try mapVariableRef(ab)
            }
        }

        return SyntaxFunction(
            name: name, type: type,
            isDefinition: obj.pointee.is_definition,
            isStatic: obj.pointee.is_static,
            isInline: obj.pointee.is_inline,
            isLive: obj.pointee.is_live,
            isRoot: obj.pointee.is_root,
            params: params, locals: locals,
            body: body, stackSize: stackSize,
            vaArea: vaArea, allocaBottom: allocaBottom,
            loc: loc
        )
    }

    public func mapGlobalVariable(
        _ obj: UnsafeMutablePointer<Obj>
    ) throws -> SyntaxGlobalVariable {
        let name = String(cString: obj.pointee.name)
        let type = try mapType(obj.pointee.ty)
        let loc = extractLocation(obj.pointee.tok)

        var initData: [UInt8]? = nil
        if let data = obj.pointee.init_data {
            let size = Int(obj.pointee.ty.pointee.size)
            initData = Array(UnsafeBufferPointer(
                start: UnsafeRawPointer(data).assumingMemoryBound(to: UInt8.self),
                count: size
            ))
        }

        let relocations: [SyntaxRelocation] = collectLinkedList(
            obj.pointee.rel, next: { $0.pointee.next }
        ).map { rel in
            SyntaxRelocation(
                offset: Int(rel.pointee.offset),
                label: String(cString: rel.pointee.label.pointee!),
                addend: Int64(rel.pointee.addend)
            )
        }

        return SyntaxGlobalVariable(
            name: name, type: type,
            isDefinition: obj.pointee.is_definition,
            isStatic: obj.pointee.is_static,
            isTentative: obj.pointee.is_tentative,
            isTLS: obj.pointee.is_tls,
            align: Int(obj.pointee.align),
            initData: initData, relocations: relocations,
            loc: loc
        )
    }

    // MARK: - Helpers

    private func collectLinkedList<T>(
        _ head: UnsafeMutablePointer<T>?,
        next: (UnsafeMutablePointer<T>) -> UnsafeMutablePointer<T>?
    ) -> [UnsafeMutablePointer<T>] {
        var result: [UnsafeMutablePointer<T>] = []
        var current = head
        while let node = current {
            result.append(node)
            current = next(node)
        }
        return result
    }

    private func mapVariableRef(
        _ obj: UnsafeMutablePointer<Obj>
    ) throws -> SyntaxVariableRef {
        let key = UnsafeRawPointer(obj)
        let id: Int
        if let existing = variableIDs[key] {
            id = existing
        } else {
            id = nextVariableID
            nextVariableID += 1
            variableIDs[key] = id
        }
        return SyntaxVariableRef(
            name: String(cString: obj.pointee.name),
            isLocal: obj.pointee.is_local,
            id: id
        )
    }

    private func mapLocalVariable(
        _ obj: UnsafeMutablePointer<Obj>
    ) throws -> SyntaxLocalVariable {
        let key = UnsafeRawPointer(obj)
        let id: Int
        if let existing = variableIDs[key] {
            id = existing
        } else {
            id = nextVariableID
            nextVariableID += 1
            variableIDs[key] = id
        }
        return SyntaxLocalVariable(
            name: String(cString: obj.pointee.name),
            type: try mapType(obj.pointee.ty),
            offset: Int(obj.pointee.offset),
            align: Int(obj.pointee.align),
            id: id
        )
    }

    private func mapMembers(
        _ first: UnsafeMutablePointer<Member>?
    ) throws -> [SyntaxMember] {
        try collectLinkedList(first, next: { $0.pointee.next }).map { mem in
            let memberType = try mapType(mem.pointee.ty)
            let memberName: String? = mem.pointee.name.map { nameToken in
                nameToken.pointee.loc.map { cStrSlice($0, len: Int(nameToken.pointee.len)) } ?? "<anon>"
            }
            let bitfield: SyntaxMember.BitfieldInfo? = mem.pointee.is_bitfield
                ? SyntaxMember.BitfieldInfo(
                    bitOffset: Int(mem.pointee.bit_offset),
                    bitWidth: Int(mem.pointee.bit_width))
                : nil
            return SyntaxMember(
                name: memberName, type: memberType,
                index: Int(mem.pointee.idx),
                offset: Int(mem.pointee.offset),
                align: Int(mem.pointee.align),
                bitfield: bitfield
            )
        }
    }

    private func mapSingleMember(
        _ mem: UnsafeMutablePointer<Member>?
    ) throws -> SyntaxMember {
        guard let mem else {
            throw MappingError.nullPointer(context: "Member pointer is nil")
        }
        let memberType = try mapType(mem.pointee.ty)
        let memberName: String? = mem.pointee.name.map { nameToken in
            nameToken.pointee.loc.map { cStrSlice($0, len: Int(nameToken.pointee.len)) } ?? "<anon>"
        }
        let bitfield: SyntaxMember.BitfieldInfo? = mem.pointee.is_bitfield
            ? SyntaxMember.BitfieldInfo(
                bitOffset: Int(mem.pointee.bit_offset),
                bitWidth: Int(mem.pointee.bit_width))
            : nil
        return SyntaxMember(
            name: memberName, type: memberType,
            index: Int(mem.pointee.idx),
            offset: Int(mem.pointee.offset),
            align: Int(mem.pointee.align),
            bitfield: bitfield
        )
    }

    private func extractLocation(
        _ tok: UnsafeMutablePointer<Token>?
    ) -> SourceLocation {
        guard let tok else {
            return SourceLocation(fileName: "<unknown>", line: 0, column: 0)
        }
        let fileName: String
        if let file = tok.pointee.file {
            fileName = String(cString: file.pointee.name)
        } else if let fn = tok.pointee.filename {
            fileName = String(cString: fn)
        } else {
            fileName = "<unknown>"
        }
        return SourceLocation(fileName: fileName,
                              line: Int(tok.pointee.line_no),
                              column: 0)
    }

    private func extractTypeName(
        _ ty: UnsafeMutablePointer<ChibiCC.`Type`>
    ) -> String? {
        guard let nameTok = ty.pointee.name else { return nil }
        // Validate the token pointer itself before dereferencing
        let tokAddr = UInt(bitPattern: nameTok)
        guard tokAddr > 0x10000 && tokAddr < 0x7FFF_FFFF_FFFF else { return nil }
        guard let loc = nameTok.pointee.loc else { return nil }
        let len = Int(nameTok.pointee.len)
        guard len > 0 && len < 4096 else { return nil }
        let locAddr = UInt(bitPattern: loc)
        guard locAddr > 0x10000 && locAddr < 0x7FFF_FFFF_FFFF else { return nil }
        return cStrSlice(loc, len: len)
    }

    private func mapNodeType(
        _ node: UnsafeMutablePointer<Node>
    ) throws -> SyntaxType {
        guard let ty = node.pointee.ty else {
            return SyntaxType(kind: .void, size: 0, align: 0)
        }
        return try mapType(ty)
    }

    private func mapBinaryOp(_ kind: NodeKind) -> BinaryOp {
        switch kind {
        case ND_ADD:    .add
        case ND_SUB:    .sub
        case ND_MUL:    .mul
        case ND_DIV:    .div
        case ND_MOD:    .mod
        case ND_BITAND: .bitAnd
        case ND_BITOR:  .bitOr
        case ND_BITXOR: .bitXor
        case ND_SHL:    .shl
        case ND_SHR:    .shr
        case ND_EQ:     .eq
        case ND_NE:     .ne
        case ND_LT:     .lt
        case ND_LE:     .le
        default:        fatalError("Not a binary op: \(kind.rawValue)")
        }
    }

    private func isFloatingType(_ type: SyntaxType) -> Bool {
        switch type.kind {
        case .float, .double, .longDouble: true
        default: false
        }
    }

    // Convert a potentially-null C string pointer (imported as IUO) to String?
    private func optCStr(_ p: UnsafeMutablePointer<CChar>!) -> String? {
        guard let p else { return nil }
        return String(cString: p)
    }

    // Convert a char* + length pair to String without Foundation
    private func cStrSlice(_ loc: UnsafeMutablePointer<CChar>, len: Int) -> String {
        let buf = UnsafeBufferPointer(
            start: UnsafeRawPointer(loc).assumingMemoryBound(to: UInt8.self),
            count: len
        )
        return String(decoding: buf, as: UTF8.self)
    }

    private func cache(
        _ key: UnsafeRawPointer,
        _ kind: SyntaxType.Kind,
        size: Int, align: Int,
        isAtomic: Bool, name: String?
    ) -> SyntaxType {
        let t = SyntaxType(kind: kind, size: size, align: align,
                            isAtomic: isAtomic, name: name)
        typeCache[key] = t
        return t
    }
}
