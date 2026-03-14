import Tree

// MARK: - Operand / type utilities

func sameOperand(_ a: Operand, _ b: Operand) -> Bool {
    switch (a, b) {
    case (.variable(_, let id1, _), .variable(_, let id2, _)): return id1 == id2
    case (.intConst(let v1, _), .intConst(let v2, _)): return v1 == v2
    case (.floatConst(let v1, _), .floatConst(let v2, _)): return v1 == v2
    case (.labelAddr(let s1, _), .labelAddr(let s2, _)): return s1 == s2
    default: return false
    }
}

/// Structural type equality used for trivial-cast elision.
func sameType(_ a: CType, _ b: CType) -> Bool {
    switch (a, b) {
    case (.void, .void): return true
    case (.bool, .bool): return true
    case (.char(let s1), .char(let s2)): return s1 == s2
    case (.short(let s1), .short(let s2)): return s1 == s2
    case (.int(let s1), .int(let s2)): return s1 == s2
    case (.long(let s1), .long(let s2)): return s1 == s2
    case (.float, .float): return true
    case (.double, .double): return true
    case (.longDouble, .longDouble): return true
    case (.enumType, .enumType): return true
    case (.pointer(let t1), .pointer(let t2)): return sameType(t1, t2)
    case (.structType(let r1), .structType(let r2)): return r1 === r2
    case (.unionType(let r1), .unionType(let r2)): return r1 === r2
    default: return false
    }
}

/// Byte size of a COIL type.
func coilTypeSize(_ type: CType) -> Int {
    switch type {
    case .void:                    return 0
    case .bool, .char:             return 1
    case .short:                   return 2
    case .int, .enumType, .float:  return 4
    case .long, .double, .longDouble, .pointer, .function: return 8
    case .array(let elem, let n):  return coilTypeSize(elem) * n
    case .vla:                     return 8
    case .structType(let r):       return r.members.reduce(0) { $0 + coilTypeSize($1.type) }
    case .unionType(let r):        return r.members.map { coilTypeSize($0.type) }.max() ?? 0
    }
}

// MARK: - Hash keys for value numbering

/// Hashable wrapper for an `Operand`, used as a dictionary key.
/// Includes type size to distinguish float vs double constants.
struct OpKey: Hashable {
    private enum Inner: Hashable {
        case variable(Int)
        case intConst(Int64, Int)
        case floatConst(UInt64, Int)
        case labelAddr(String)
    }
    private let inner: Inner

    init(_ op: Operand) {
        switch op {
        case .variable(_, let id, _):       inner = .variable(id)
        case .intConst(let v, let t):       inner = .intConst(v, coilTypeSize(t))
        case .floatConst(let v, let t):     inner = .floatConst(v.bitPattern, coilTypeSize(t))
        case .labelAddr(let s, _):          inner = .labelAddr(s)
        }
    }
}

/// Hashable key for a pure instruction expression, used for CSE.
/// Returns `nil` for instructions that are not eligible for CSE.
struct ExprKey: Hashable {
    private enum Inner: Hashable {
        case binary(Int, OpKey, OpKey)
        case unary(Int, OpKey)
        case cast(OpKey, Int)
        case member(OpKey, String)
        case addressOf(OpKey)
    }
    private let inner: Inner
    private let resultTypeSize: Int

    init?(_ instr: Instr) {
        switch instr {
        case .binary(let dest, let op, let lhs, let rhs):
            inner = .binary(bopTag(op), OpKey(lhs), OpKey(rhs))
            resultTypeSize = coilTypeSize(dest.type)
        case .unary(let dest, let op, let src):
            inner = .unary(uopTag(op), OpKey(src))
            resultTypeSize = coilTypeSize(dest.type)
        case .cast(let dest, let src, _):
            inner = .cast(OpKey(src), coilTypeSize(dest.type))
            resultTypeSize = coilTypeSize(dest.type)
        case .member(let dest, let base, let name, _):
            inner = .member(OpKey(base), name)
            resultTypeSize = coilTypeSize(dest.type)
        case .addressOf(let dest, let src):
            inner = .addressOf(OpKey(src))
            resultTypeSize = coilTypeSize(dest.type)
        default:
            return nil
        }
    }
}

private func bopTag(_ op: BinaryOp) -> Int {
    switch op {
    case .add: return 0; case .sub: return 1; case .mul: return 2
    case .div: return 3; case .mod: return 4
    case .bitAnd: return 5; case .bitOr: return 6; case .bitXor: return 7
    case .shl: return 8; case .shr: return 9
    case .eq: return 10; case .ne: return 11; case .lt: return 12; case .le: return 13
    }
}

private func uopTag(_ op: UnaryOp) -> Int {
    switch op {
    case .neg: return 0
    case .bitNot: return 1
    }
}

// MARK: - Address-taken variable collection

/// Collect variables whose address is taken in the given blocks.
///
/// Detects three patterns:
/// - `addressOf(_, variable(id))` — explicit address-of
/// - `member(_, variable(id), _, _)` — struct base accessed via memory offset
/// - `cast(_, variable(id, arrayOrStructType), _)` — aggregate decay to pointer
func collectAddressTaken(in blocks: some Sequence<Block>) -> Set<Int> {
    var ids: Set<Int> = []
    for block in blocks {
        for instr in block.instructions {
            if case .addressOf(_, let src) = instr,
               case .variable(_, let id, _) = src {
                ids.insert(id)
            }
            if case .member(_, let base, _, _) = instr,
               case .variable(_, let id, let baseType) = base {
                // Only mark aggregate-typed bases as address-taken.
                // Pointer bases (e.g. struct_ptr->field) are just read, not stored through.
                switch baseType {
                case .structType, .unionType, .array:
                    ids.insert(id)
                default:
                    break
                }
            }
            if case .cast(_, let src, _) = instr,
               case .variable(_, let id, let srcType) = src {
                switch srcType {
                case .array, .structType, .unionType:
                    ids.insert(id)
                default:
                    break
                }
            }
        }
    }
    return ids
}

// MARK: - Computed goto / label address utilities

/// Collect all label-address targets referenced in the given blocks.
///
/// Scans instructions, terminators, and phi args for `.labelAddr` operands.
/// Returns the set of target label strings.
func collectLabelAddrTargets(in blocks: [Block]) -> Set<String> {
    var targets: Set<String> = []
    for block in blocks {
        func scan(_ op: Operand) {
            if case .labelAddr(let target, _) = op { targets.insert(target) }
        }
        for instr in block.instructions { instr.operands.forEach(scan) }
        for phi in block.phis { phi.operands.forEach(scan) }
        block.terminator.operands.forEach(scan)
    }
    return targets
}

// MARK: - Block label index

/// Build a map from block label → block index.
func buildLabelIndex(_ blocks: [Block]) -> [String: Int] {
    Dictionary(uniqueKeysWithValues: blocks.enumerated().map { ($1.label, $0) })
}

// MARK: - Branch evaluation helpers

func evaluateCompare(_ a: Int64, _ b: Int64, _ cond: Condition, unsigned: Bool = false) -> Bool {
    switch cond {
    case .eq:      return a == b
    case .ne:      return a != b
    case .lt:
        if unsigned { return UInt64(bitPattern: a) < UInt64(bitPattern: b) }
        return a < b
    case .le:
        if unsigned { return UInt64(bitPattern: a) <= UInt64(bitPattern: b) }
        return a <= b
    case .zero:    return false
    case .nonZero: return false
    }
}

func evaluateTest(_ a: Int64, _ cond: Condition) -> Bool {
    switch cond {
    case .zero:    return a == 0
    case .nonZero: return a != 0
    case .eq:      return a == 0
    case .ne:      return a != 0
    case .lt:      return a < 0
    case .le:      return a <= 0
    }
}

// MARK: - Function utilities

/// Create a new Function with replaced blocks, keeping all other fields.
func withBlocks(_ function: Function, _ blocks: [Block]) -> Function {
    Function(name: function.name, returnType: function.returnType,
             params: function.params, locals: function.locals,
             blocks: blocks, isStatic: function.isStatic, isInline: function.isInline,
             domTree: function.domTree)
}

/// Build a map from block label → set of predecessor labels.
func buildPredMap(_ blocks: [Block]) -> [String: Set<String>] {
    var map: [String: Set<String>] = [:]
    for block in blocks {
        for succ in block.terminator.successorLabels {
            map[succ, default: []].insert(block.label)
        }
    }
    return map
}

func instrCount(_ blocks: [Block]) -> Int {
    blocks.reduce(0) { $0 + $1.instructions.count }
}

// MARK: - Reachability

/// Compute which blocks are reachable from the entry block (index 0).
/// Handles computed gotos by seeding with `labelAddr` targets.
func computeReachable(_ blocks: [Block]) -> [Bool] {
    let n = blocks.count
    guard n > 0 else { return [] }
    let labelIndex = buildLabelIndex(blocks)
    var reachable = [Bool](repeating: false, count: n)
    var queue: [Int] = [0]
    reachable[0] = true
    let blockLabels = Set(blocks.map(\.label))
    for target in collectLabelAddrTargets(in: blocks) {
        if blockLabels.contains(target), let si = labelIndex[target], !reachable[si] {
            reachable[si] = true
            queue.append(si)
        }
    }
    while let bi = queue.popLast() {
        for succ in blocks[bi].terminator.successorLabels {
            if let si = labelIndex[succ], !reachable[si] {
                reachable[si] = true
                queue.append(si)
            }
        }
    }
    return reachable
}
