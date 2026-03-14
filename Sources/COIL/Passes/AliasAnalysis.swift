import Tree

/// Flow-insensitive, intra-procedural points-to analysis (subset of Andersen's).
///
/// For each pointer-typed SSA variable, computes the set of stack-local variable
/// IDs it may point to. Only tracks pointers derived (directly or via copies)
/// from `addressOf` instructions. All other pointer sources (call results, loads
/// of pointer values, function parameters, global addresses) are treated as
/// pointing to an "unknown" object set — represented by the presence of
/// `AliasAnalysis.unknown` in the pts set.
///
/// Usage (LICM): a `load(dest, addr)` can be treated as loop-invariant if:
/// 1. `addr` is loop-invariant,
/// 2. `addr`'s points-to set is fully known (no `unknown`), and
/// 3. No loop store's address has a non-empty intersection with `addr`'s pts set.
public struct AliasAnalysis {
    /// Sentinel object ID meaning "unknown / may alias anything".
    public static let unknown = Int.min

    /// pts[varId] = set of object IDs the pointer variable may point to.
    /// Absence from the map is equivalent to `{unknown}` (not analysed).
    public let pts: [Int: Set<Int>]

    public init(_ function: Function) {
        pts = AliasAnalysis.compute(function)
    }

    /// Returns `true` if pointer operands `p` and `q` may alias.
    /// Conservative: `true` if either's points-to set is unknown.
    public func mayAlias(_ p: Operand, _ q: Operand) -> Bool {
        guard case .variable(_, let pid, _) = p,
              case .variable(_, let qid, _) = q else { return true }
        guard let pSet = pts[pid], !pSet.contains(AliasAnalysis.unknown),
              let qSet = pts[qid], !qSet.contains(AliasAnalysis.unknown) else { return true }
        return !pSet.isDisjoint(with: qSet)
    }

    /// Returns the known points-to set for `op`, or `nil` if unknown.
    public func knownPointsTo(_ op: Operand) -> Set<Int>? {
        guard case .variable(_, let id, _) = op else { return nil }
        guard let s = pts[id], !s.contains(AliasAnalysis.unknown) else { return nil }
        return s
    }

    // MARK: - Analysis

    private static func compute(_ function: Function) -> [Int: Set<Int>] {
        var pts: [Int: Set<Int>] = [:]

        // Pass 1: seed base constraints from `addressOf`.
        // Other pointer definitions start as {unknown}.
        for block in function.blocks {
            for instr in block.instructions {
                guard let dest = instr.dest, isPointerLike(dest.type) else { continue }
                switch instr {
                case .addressOf(let d, let src):
                    if case .variable(_, let xid, _) = src {
                        // p = &x  →  pts(p) = {x}
                        pts[d.id, default: []].insert(xid)
                    } else {
                        // &(expr) — e.g. &global or &member → unknown
                        pts[dest.id] = [unknown]
                    }
                case .assign, .cast:
                    // Initialise as empty; copy constraints fill this in pass 2.
                    if pts[dest.id] == nil { pts[dest.id] = [] }
                case .call, .load, .cas, .exchange:
                    pts[dest.id] = [unknown]
                default:
                    pts[dest.id] = [unknown]
                }
            }
            // Phi nodes: initialise as empty; filled by copy propagation.
            for phi in block.phis {
                guard isPointerLike(phi.dest.type) else { continue }
                if pts[phi.dest.id] == nil { pts[phi.dest.id] = [] }
            }
        }

        // Parameters are unknown.
        for param in function.params where isPointerLike(param.type) {
            if case .local(let id) = param.storage { pts[id] = [unknown] }
        }

        // Pass 2: propagate copy constraints on a worklist until fixed point.
        var changed = true
        while changed {
            changed = false
            for block in function.blocks {
                // Phis: dest gets union of all arg pts sets (or unknown if any arg is unknown).
                for phi in block.phis {
                    guard isPointerLike(phi.dest.type) else { continue }
                    let did = phi.dest.id
                    guard var dSet = pts[did],
                          !dSet.contains(AliasAnalysis.unknown) else { continue }
                    for (_, val) in phi.args {
                        propagate(src: val, into: &dSet, from: pts)
                        if dSet.contains(AliasAnalysis.unknown) { break }
                    }
                    if dSet != pts[did]! { pts[did] = dSet; changed = true }
                }

                for instr in block.instructions {
                    switch instr {
                    case .assign(let dest, let src):
                        guard isPointerLike(dest.type) else { continue }
                        guard var dSet = pts[dest.id],
                              !dSet.contains(AliasAnalysis.unknown) else { continue }
                        propagate(src: src, into: &dSet, from: pts)
                        if dSet != pts[dest.id]! { pts[dest.id] = dSet; changed = true }

                    case .cast(let dest, let src, _):
                        guard isPointerLike(dest.type) else { continue }
                        guard var dSet = pts[dest.id],
                              !dSet.contains(AliasAnalysis.unknown) else { continue }
                        propagate(src: src, into: &dSet, from: pts)
                        if dSet != pts[dest.id]! { pts[dest.id] = dSet; changed = true }

                    default: break
                    }
                }
            }
        }

        return pts
    }

    /// Merge `src` operand's pts into `dest` set; if `src` is unknown, inserts `unknown`.
    private static func propagate(src: Operand, into dest: inout Set<Int>,
                                   from pts: [Int: Set<Int>]) {
        switch src {
        case .variable(_, let sid, _):
            let sSet = pts[sid] ?? [unknown]
            dest.formUnion(sSet)
        case .intConst(0, _):
            break  // null pointer — no alias
        default:
            dest.insert(unknown)
        }
    }
}

private func isPointerLike(_ t: CType) -> Bool {
    switch t {
    case .pointer: return true
    default:       return false
    }
}
