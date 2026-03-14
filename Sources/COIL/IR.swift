import Tree

// MARK: - Operand

/// A named, writable storage slot — always a variable or synthetic temporary.
/// Negative `id` values denote temporaries introduced by `TreeConverter`.
/// Only a `Place` may appear as the destination of an instruction.
public struct Place: Sendable, Equatable {
  public static func == (lhs: Place, rhs: Place) -> Bool {
    lhs.id == rhs.id && lhs.name == rhs.name
  }

  public let name: String
  public let id: Int
  public let type: CType

  public init(name: String, id: Int, type: CType) {
    self.name = name
    self.id = id
    self.type = type
  }

  /// Lift to a readable `Operand` for use on the source side of instructions.
  public var asOperand: Operand { .variable(name: name, id: id, type: type) }
}

/// A readable COIL value: a named slot or a compile-time constant.
public enum Operand: Sendable {
  /// A source variable or synthesised temporary.
  /// A source variable or synthesised temporary.
  case variable(name: String, id: Int, type: CType)
  case intConst(Int64, type: CType)
  case floatConst(Double, type: CType)
  /// GNU extension: address of a local label (`&&label`).
  case labelAddr(String, type: CType)

  public var type: CType {
    switch self {
    case .variable(_, _, let t): return t
    case .intConst(_, let t): return t
    case .floatConst(_, let t): return t
    case .labelAddr(_, let t): return t
    }
  }
}

// MARK: - Instr

/// A non-terminating instruction within a basic block.
/// Every instruction that produces a value writes to a `Place` (never a constant).
public enum Instr: Sendable {
  case assign(dest: Place, src: Operand)
  case binary(dest: Place, op: BinaryOp, lhs: Operand, rhs: Operand)
  case unary(dest: Place, op: UnaryOp, src: Operand)
  /// `dest` is `nil` for void-returning calls.
  case call(dest: Place?, callee: Operand, args: [Operand])
  case addressOf(dest: Place, src: Operand)
  case load(dest: Place, addr: Operand)  // dest = *addr
  case store(addr: Operand, value: Operand)  // *addr = value (no dest)
  case cast(dest: Place, src: Operand, to: CType)
  case cas(dest: Place, addr: Operand, old: Operand, new: Operand)
  case exchange(dest: Place, addr: Operand, value: Operand)
  case member(dest: Place, base: Operand, name: String, offset: Int32 = 0)
  case asm(String)

  // ── Flag-setting instructions (no dest) ───────────────────────────
  /// Compare two values; sets condition flags for the following branch.
  case compare(lhs: Operand, rhs: Operand)
  /// Test an operand for zero/nonzero; sets condition flags.
  case test(Operand)

  /// The place written by this instruction, if any.
  public var dest: Place? {
    switch self {
    case .assign(let d, _), .binary(let d, _, _, _), .unary(let d, _, _),
      .addressOf(let d, _), .load(let d, _), .cast(let d, _, _),
      .cas(let d, _, _, _), .exchange(let d, _, _), .member(let d, _, _, _):
      return d
    case .call(let d, _, _):
      return d
    case .store, .asm, .compare, .test:
      return nil
    }
  }

  /// All operands read by this instruction.
  public var operands: [Operand] {
    switch self {
    case .assign(_, let s): return [s]
    case .binary(_, _, let l, let r): return [l, r]
    case .unary(_, _, let s): return [s]
    case .call(_, let c, let args): return [c] + args
    case .addressOf(_, let s): return [s]
    case .load(_, let a): return [a]
    case .store(let a, let v): return [a, v]
    case .cast(_, let s, _): return [s]
    case .cas(_, let a, let o, let n): return [a, o, n]
    case .exchange(_, let a, let v): return [a, v]
    case .member(_, let b, _, _): return [b]
    case .asm: return []
    case .compare(let l, let r): return [l, r]
    case .test(let v): return [v]
    }
  }

  /// Whether this instruction may have side effects beyond writing to `dest`.
  public var hasSideEffects: Bool {
    switch self {
    case .call, .store, .cas, .exchange, .asm, .compare, .test:
      return true
    default:
      return false
    }
  }

  /// Return a new instruction with all source operands transformed by `f`.
  public func remapOperands(_ f: (Operand) -> Operand) -> Instr {
    switch self {
    case .assign(let d, let s):
      return .assign(dest: d, src: f(s))
    case .binary(let d, let op, let l, let r):
      return .binary(dest: d, op: op, lhs: f(l), rhs: f(r))
    case .unary(let d, let op, let s):
      return .unary(dest: d, op: op, src: f(s))
    case .call(let d, let c, let args):
      return .call(dest: d, callee: f(c), args: args.map { f($0) })
    case .addressOf(let d, let s):
      return .addressOf(dest: d, src: f(s))
    case .load(let d, let a):
      return .load(dest: d, addr: f(a))
    case .store(let a, let v):
      return .store(addr: f(a), value: f(v))
    case .cast(let d, let s, let t):
      return .cast(dest: d, src: f(s), to: t)
    case .cas(let d, let a, let o, let n):
      return .cas(dest: d, addr: f(a), old: f(o), new: f(n))
    case .exchange(let d, let a, let v):
      return .exchange(dest: d, addr: f(a), value: f(v))
    case .member(let d, let b, let name, let off):
      return .member(dest: d, base: f(b), name: name, offset: off)
    case .asm:
      return self
    case .compare(let l, let r):
      return .compare(lhs: f(l), rhs: f(r))
    case .test(let v):
      return .test(f(v))
    }
  }
}

/// Branch predicate — references the flags set by a preceding `compare` or `test`.
public enum Condition: Sendable {
  // After `compare`:
  case eq, ne, lt, le
  // After `test`:
  case zero, nonZero
}

/// The control-transfer at the end of a basic block.
public enum Terminator: Sendable {
  case goto(String)
  case branch(cond: Condition, then: String, else: String)
  case `return`(Operand?)
  case computedGoto(Operand)  // GNU extension: goto *expr

  /// The statically known successor block labels, in order.
  /// `.computedGoto` has no statically known successors.
  public var successorLabels: [String] {
    switch self {
    case .goto(let l): return [l]
    case .branch(_, let t, let e): return [t, e]
    case .return: return []
    case .computedGoto: return []
    }
  }

  /// All operands referenced by this terminator.
  public var operands: [Operand] {
    switch self {
    case .goto: return []
    case .branch: return []
    case .return(let v): return v.map { [$0] } ?? []
    case .computedGoto(let v): return [v]
    }
  }

  /// Return a new terminator with labels rewritten by `f`.
  public func remapLabels(_ f: (String) -> String) -> Terminator {
    switch self {
    case .goto(let l):
      return .goto(f(l))
    case .branch(let c, let t, let e):
      return .branch(cond: c, then: f(t), else: f(e))
    case .return:
      return self
    case .computedGoto:
      return self
    }
  }

  /// Return a new terminator with all operands transformed by `f`.
  public func remapOperands(_ f: (Operand) -> Operand) -> Terminator {
    switch self {
    case .goto:
      return self
    case .branch:
      return self
    case .return(let v):
      return .return(v.map { f($0) })
    case .computedGoto(let v):
      return .computedGoto(f(v))
    }
  }
}

/// A phi function: merges values from predecessor blocks at a join point.
/// `args` maps predecessor block label → the Operand arriving from that edge.
public struct Phi: Sendable {
  public let dest: Place
  public var args: [(label: String, value: Operand)]

  public init(dest: Place, args: [(label: String, value: Operand)]) {
    self.dest = dest
    self.args = args
  }

  /// All operands read by this phi.
  public var operands: [Operand] { args.map(\.value) }

  /// Return a new phi with all value operands transformed by `f`.
  public func remapOperands(_ f: (Operand) -> Operand) -> Phi {
    Phi(dest: dest, args: args.map { (label: $0.label, value: f($0.value)) })
  }

  /// Return a new phi with predecessor labels rewritten by `f`.
  public func remapLabels(_ f: (String) -> String) -> Phi {
    Phi(dest: dest, args: args.map { (label: f($0.label), value: $0.value) })
  }
}

/// A straight-line sequence of instructions with a single entry point
/// and exactly one terminator. Phi functions appear before all instructions.
public struct Block: Sendable {
  public let label: String
  public var phis: [Phi]
  public var instructions: [Instr]
  public var terminator: Terminator

  public init(
    label: String, phis: [Phi] = [], instructions: [Instr] = [],
    terminator: Terminator
  ) {
    self.label = label
    self.phis = phis
    self.instructions = instructions
    self.terminator = terminator
  }
}

// MARK: - Decl

/// A function in CFG form. `blocks[0]` is the entry block.
public struct Function: Sendable {
  public let name: String
  public let returnType: CType
  public let params: [CVar]
  public let locals: [CVar]  // source locals + synthesised temporaries
  public let blocks: [Block]
  public let isStatic: Bool
  public let isInline: Bool

  /// Cached dominator tree. Set automatically by `dominatorTree()`;
  /// cleared by `invalidateCFG()` when the CFG changes.
  public var domTree: DominatorTree?

  public init(
    name: String, returnType: CType, params: [CVar], locals: [CVar],
    blocks: [Block], isStatic: Bool, isInline: Bool,
    domTree: DominatorTree? = nil
  ) {
    self.name = name
    self.returnType = returnType
    self.params = params
    self.locals = locals
    self.blocks = blocks
    self.isStatic = isStatic
    self.isInline = isInline
    self.domTree = domTree
  }

  /// Return the cached dominator tree, or build and cache it.
  public mutating func dominatorTree() -> DominatorTree {
    if let dt = domTree { return dt }
    let dt = DominatorTree(self)
    domTree = dt
    return dt
  }

  /// Invalidate cached analyses after CFG modifications.
  public mutating func invalidateCFG() {
    domTree = nil
  }
}

extension Function {

  /// Returns the statically known successor labels of `label`.
  /// O(n) block lookup; O(1) terminator dispatch.
  public func successors(of label: String) -> [String] {
    guard let block = blocks.first(where: { $0.label == label }) else { return [] }
    return block.terminator.successorLabels
  }

  /// Returns all block labels that have a direct edge to `label`.
  /// O(n) scan over all blocks.
  public func predecessors(of label: String) -> [String] {
    blocks
      .filter { $0.terminator.successorLabels.contains(label) }
      .map(\.label)
  }
}

/// The top-level COIL program (all functions + global variables).
public struct Program: Sendable {
  public let functions: [Function]
  public let globals: [CVar]

  public init(functions: [Function], globals: [CVar]) {
    self.functions = functions
    self.globals = globals
  }
}
