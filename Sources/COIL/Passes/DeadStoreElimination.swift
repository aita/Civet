/// Dead store elimination and intra-block load forwarding.
///
/// **Intra-block DSE**: within each block, if a store to address A is followed
/// by another store to A before any load/call, the first store is dead.
///
/// **Inter-block DSE**: forward must-available-stores dataflow (RPO order).
/// A store available at ALL predecessors is killed when an overwriting store
/// is seen in the current block. Back-edge predecessors produce empty sets
/// (conservative: no cross-loop DSE).
///
/// **Load Forwarding (intra-block)**: if a store `store(A, v)` is followed by
/// `load(r, A)` with no intervening store/call/asm to A, replace the load with
/// `assign(r, v)`. This handles struct field write-then-read patterns after
/// GVN has CSE'd the member address computations.
public func deadStoreElimination(in function: Function) -> Function {
    let blocks = function.blocks
    let n = blocks.count

    var f = function
    let dom = f.dominatorTree()
    let preds = dom.preds
    let rpoOrder = dom.rpoOrder

    // dead[blockIdx] = set of instrIdx within that block that are dead stores.
    var dead: [Int: Set<Int>] = [:]
    // fwd[blockIdx][instrIdx] = Operand to forward (replaces load with assign).
    var fwd: [Int: [Int: Operand]] = [:]

    // availOut[b]: address key → list of encoded store refs (b*1_000_000 + ii).
    var availOut: [[OpKey: [Int]]] = Array(repeating: [:], count: n)
    // availValOut[b]: address key → the single stored value (if all paths agree).
    // Used for intra-block load forwarding only (cleared at block boundaries).
    var availValOut: [[OpKey: Operand]] = Array(repeating: [:], count: n)

    for b in rpoOrder {
        // ── Compute availIn[b] ────────────────────────────────────────────
        var cur: [OpKey: [Int]]
        if preds[b].isEmpty {
            cur = [:]
        } else {
            var commonKeys = Set(availOut[preds[b][0]].keys)
            for p in preds[b].dropFirst() {
                commonKeys.formIntersection(availOut[p].keys)
            }
            cur = [:]
            for key in commonKeys {
                var refs: [Int] = []
                for p in preds[b] { refs += availOut[p][key, default: []] }
                cur[key] = refs
            }
        }

        // Intra-block load forwarding: track last-stored value within this block only.
        // (Separate from inter-block cur to avoid cross-block value propagation issues.)
        var localVal: [OpKey: Operand] = [:]

        // ── Scan instructions ─────────────────────────────────────────────
        for (ii, instr) in blocks[b].instructions.enumerated() {
            switch instr {
            case .store(let addr, let value):
                let key = OpKey(addr)
                // Kill all pending stores to this address — they're dead.
                if let prevRefs = cur[key] {
                    for ref in prevRefs {
                        dead[ref / 1_000_000, default: []].insert(ref % 1_000_000)
                    }
                }
                cur[key] = [b * 1_000_000 + ii]
                // Conservative: any store may alias any tracked address (no alias
                // analysis), so clear ALL forwarded values first. Then optionally
                // re-add the current store's constant value for its specific key.
                localVal.removeAll()
                switch value {
                case .intConst, .floatConst:
                    localVal[key] = value
                default:
                    break
                }

            case .load(_, let addr):
                let key = OpKey(addr)
                // Intra-block load forwarding: replace load with forwarded constant.
                if let storedVal = localVal[key] {
                    fwd[b, default: [:]][ii] = storedVal
                }
                // The previous store to this address is observed — not dead.
                cur.removeValue(forKey: key)
                localVal.removeValue(forKey: key)

            case .call, .cas, .exchange, .asm:
                // Conservative: may observe/modify any address.
                cur.removeAll()
                localVal.removeAll()

            case .assign(let dest, _):
                // Struct/union/array assign is a struct copy (writes to dest's memory).
                // Clear forwarding cache conservatively — we can't tell which member
                // addresses correspond to dest's fields without full alias analysis.
                switch dest.type {
                case .structType, .unionType, .array:
                    localVal.removeAll()
                default:
                    break
                }

            default:
                break
            }
        }

        availOut[b] = cur
        availValOut[b] = localVal
    }

    let hasChanges = !dead.isEmpty || !fwd.isEmpty
    guard hasChanges else { return function }

    var newBlocks = blocks
    for (bi, block) in blocks.enumerated() {
        let deadSet = dead[bi] ?? []
        let fwdMap  = fwd[bi]  ?? [:]
        guard !deadSet.isEmpty || !fwdMap.isEmpty else { continue }

        var newInstrs: [Instr] = []
        for (ii, instr) in block.instructions.enumerated() {
            if deadSet.contains(ii) { continue }
            if let forwardedVal = fwdMap[ii],
               case .load(let dest, _) = instr {
                // Replace load with forwarded assign.
                newInstrs.append(.assign(dest: dest, src: forwardedVal))
            } else {
                newInstrs.append(instr)
            }
        }
        newBlocks[bi] = block.with(instructions: newInstrs)
    }
    return withBlocks(function, newBlocks)
}
