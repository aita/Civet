/// Dead store elimination and load forwarding.
///
/// **Phase 1 — Forward DSE + Load Forwarding** (RPO):
/// - Intra-block DSE: if a store to address A is followed by another store to A
///   before any load/call, the first store is dead.
/// - Forward inter-block: stores available at ALL predecessors are killed when
///   an overwriting store is seen in the current block.
/// - Load forwarding: if a store `store(A, v)` dominates a `load(r, A)` with
///   no intervening may-alias store/call/asm, replace the load with `assign(r, v)`.
///   Works both intra-block and inter-block (all predecessors must agree).
///
/// **Phase 2 — Backward must-kill DSE** (post-order):
/// A store is dead if on ALL forward paths from that store, the same address is
/// overwritten before being read. Uses backward dataflow with intersection as
/// meet: `mustKillOut[b] = ∩ mustKillIn[succ(b)]`. Alias analysis ensures loads
/// through may-aliasing pointers conservatively invalidate the kill set.
public func deadStoreElimination(in function: Function) -> Function {
    let blocks = function.blocks
    let n = blocks.count

    var f = function
    let dom = f.dominatorTree()
    let preds = dom.preds
    let rpoOrder = dom.rpoOrder
    let aa = AliasAnalysis(f)

    // dead[blockIdx] = set of instrIdx within that block that are dead stores.
    var dead: [Int: Set<Int>] = [:]
    // fwd[blockIdx][instrIdx] = Operand to forward (replaces load with assign).
    var fwd: [Int: [Int: Operand]] = [:]

    // availOut[b]: address key → list of encoded store refs (b*1_000_000 + ii).
    var availOut: [[OpKey: [Int]]] = Array(repeating: [:], count: n)
    // availValOut[b]: address key → (address operand, stored value).
    // Tracks constant values available at block exit for inter-block load forwarding.
    var availValOut: [[OpKey: (addr: Operand, value: Operand)]] = Array(repeating: [:], count: n)

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

        // Load forwarding: track address → (addr operand, stored value).
        // Initialized from inter-block available values (intersection of preds).
        var localVal: [OpKey: (addr: Operand, value: Operand)] = [:]
        if !preds[b].isEmpty {
            // Start with first pred's available values.
            var commonValKeys = Set(availValOut[preds[b][0]].keys)
            for p in preds[b].dropFirst() {
                commonValKeys.formIntersection(availValOut[p].keys)
            }
            for key in commonValKeys {
                guard let first = availValOut[preds[b][0]][key] else { continue }
                // All predecessors must agree on the same stored value.
                let allAgree = preds[b].dropFirst().allSatisfy { p in
                    guard let entry = availValOut[p][key] else { return false }
                    return OpKey(entry.value) == OpKey(first.value)
                }
                if allAgree {
                    localVal[key] = first
                }
            }
        }

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
                // Alias-aware invalidation: only clear entries that may alias.
                invalidateMayAlias(addr, in: &localVal, aa: aa)
                // Re-add the current store's value for forwarding.
                switch value {
                case .intConst, .floatConst:
                    localVal[key] = (addr: addr, value: value)
                default:
                    break
                }

            case .load(_, let addr):
                let key = OpKey(addr)
                // Load forwarding: replace load with forwarded value.
                if let entry = localVal[key] {
                    fwd[b, default: [:]][ii] = entry.value
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

    // ── Phase 2: Backward must-kill dataflow for inter-block DSE ────────
    // A store is dead if on ALL forward paths, the same address is overwritten
    // before being read (or before function exit with no observable effect).

    // Build successor map.
    var succs: [[Int]] = Array(repeating: [], count: n)
    let labelToIdx: [String: Int] = Dictionary(
        uniqueKeysWithValues: blocks.enumerated().map { ($1.label, $0) })
    for (bi, block) in blocks.enumerated() {
        for label in block.terminator.successorLabels {
            if let si = labelToIdx[label] { succs[bi].append(si) }
        }
    }

    // OpKey → representative address Operand (for alias queries on loads).
    var keyToAddr: [OpKey: Operand] = [:]
    for block in blocks {
        for instr in block.instructions {
            if case .store(let addr, _) = instr {
                keyToAddr[OpKey(addr)] = addr
            }
        }
    }

    if !keyToAddr.isEmpty {
        let allStoreKeys = Set(keyToAddr.keys)

        // mustKillIn[b]: address keys definitely stored (without intervening
        // load/call) on all paths from block b's entry to function exit.
        // Initialise to top (= allStoreKeys); narrows via intersection.
        var mustKillIn: [Set<OpKey>] = Array(repeating: allStoreKeys, count: n)

        // Backward dataflow in post-order (= reverse of rpoOrder).
        let postOrder = Array(rpoOrder.reversed())
        var bwChanged = true
        while bwChanged {
            bwChanged = false
            for b in postOrder {
                let killOut = mustKillOut(b, succs: succs, mustKillIn: mustKillIn)
                let newIn = transferBackward(
                    blocks[b], killOut: killOut, keyToAddr: keyToAddr, aa: aa)
                if newIn != mustKillIn[b] {
                    mustKillIn[b] = newIn
                    bwChanged = true
                }
            }
        }

        // Identify inter-block dead stores using converged mustKillIn.
        for b in 0..<n {
            let killOut = mustKillOut(b, succs: succs, mustKillIn: mustKillIn)
            var killed = killOut
            for (ii, instr) in blocks[b].instructions.enumerated().reversed() {
                switch instr {
                case .store(let addr, _):
                    let key = OpKey(addr)
                    if killed.contains(key) {
                        dead[b, default: []].insert(ii)
                    }
                    killed.insert(key)
                case .load(_, let addr):
                    removeObserved(addr, from: &killed, keyToAddr: keyToAddr, aa: aa)
                case .call, .cas, .exchange, .asm:
                    killed.removeAll()
                case .assign(let dest, _):
                    switch dest.type {
                    case .structType, .unionType, .array:
                        killed.removeAll()
                    default: break
                    }
                default: break
                }
            }
        }
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

// MARK: - Backward DSE helpers

/// Compute mustKillOut for block `b`: intersection of mustKillIn across all successors.
/// Exit blocks (no successors) return empty — stores before `ret` may be externally visible.
private func mustKillOut(
    _ b: Int,
    succs: [[Int]],
    mustKillIn: [Set<OpKey>]
) -> Set<OpKey> {
    guard !succs[b].isEmpty else { return [] }
    var result = mustKillIn[succs[b][0]]
    for s in succs[b].dropFirst() {
        result.formIntersection(mustKillIn[s])
    }
    return result
}

/// Backward transfer function: scan block bottom-to-top, return mustKillIn.
private func transferBackward(
    _ block: Block,
    killOut: Set<OpKey>,
    keyToAddr: [OpKey: Operand],
    aa: AliasAnalysis
) -> Set<OpKey> {
    var killed = killOut
    for instr in block.instructions.reversed() {
        switch instr {
        case .store(let addr, _):
            killed.insert(OpKey(addr))
        case .load(_, let addr):
            removeObserved(addr, from: &killed, keyToAddr: keyToAddr, aa: aa)
        case .call, .cas, .exchange, .asm:
            killed.removeAll()
        case .assign(let dest, _):
            switch dest.type {
            case .structType, .unionType, .array:
                killed.removeAll()
            default: break
            }
        default: break
        }
    }
    return killed
}

/// Remove all keys from `killed` whose address may-alias the loaded address.
private func removeObserved(
    _ loadAddr: Operand,
    from killed: inout Set<OpKey>,
    keyToAddr: [OpKey: Operand],
    aa: AliasAnalysis
) {
    guard aa.knownPointsTo(loadAddr) != nil else {
        // Unknown pointer — may alias anything.
        killed.removeAll()
        return
    }
    killed = killed.filter { key in
        guard let storedAddr = keyToAddr[key] else { return true }
        return !aa.mayAlias(loadAddr, storedAddr)
    }
}

/// Remove entries from `localVal` whose address may-alias `storeAddr`.
private func invalidateMayAlias(
    _ storeAddr: Operand,
    in localVal: inout [OpKey: (addr: Operand, value: Operand)],
    aa: AliasAnalysis
) {
    // If the store address has unknown points-to, conservatively clear all.
    guard aa.knownPointsTo(storeAddr) != nil else {
        localVal.removeAll()
        return
    }
    // Remove only entries whose address may alias the store address.
    localVal = localVal.filter { (_, entry) in
        !aa.mayAlias(storeAddr, entry.addr)
    }
}
