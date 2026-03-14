// MARK: - Dead Block Elimination

/// Remove blocks unreachable from the entry block.
public func eliminateDeadBlocks(in function: Function) -> Function {
    guard let entry = function.blocks.first else { return function }
    var reachable: Set<String> = [entry.label]
    var worklist = [entry.label]

    // Computed gotos (&&label / goto *p) can jump to any labeled block.
    let blockLabels = Set(function.blocks.map(\.label))
    for target in collectLabelAddrTargets(in: function.blocks) {
        if blockLabels.contains(target), reachable.insert(target).inserted {
            worklist.append(target)
        }
    }

    let blockMap = Dictionary(uniqueKeysWithValues: function.blocks.map { ($0.label, $0) })
    while let label = worklist.popLast() {
        for succ in blockMap[label]!.terminator.successorLabels {
            if reachable.insert(succ).inserted {
                worklist.append(succ)
            }
        }
    }
    var filtered = function.blocks.filter { reachable.contains($0.label) }
    guard filtered.count != function.blocks.count else { return function }

    // Clean up phi args that reference removed blocks.
    let removed = Set(function.blocks.map(\.label)).subtracting(reachable)
    if !removed.isEmpty {
        filtered = filtered.map { block in
            guard !block.phis.isEmpty else { return block }
            let newPhis = block.phis.map { phi in
                Phi(dest: phi.dest, args: phi.args.filter { !removed.contains($0.label) })
            }
            return Block(label: block.label, phis: newPhis,
                         instructions: block.instructions, terminator: block.terminator)
        }
    }
    var result = withBlocks(function, filtered)
    result.invalidateCFG()
    return result
}

// MARK: - Jump Threading

/// Thread through blocks that contain no instructions and just `goto(target)`.
public func threadJumps(in function: Function) -> Function {
    // Build forwarding map: blocks with no instructions, no phis, and a goto terminator.
    var forwarding: [String: String] = [:]
    for block in function.blocks {
        if block.instructions.isEmpty && block.phis.isEmpty,
           case .goto(let target) = block.terminator {
            forwarding[block.label] = target
        }
    }
    guard !forwarding.isEmpty else { return function }

    // Resolve chains: A→B→C becomes A→C.
    func resolve(_ label: String) -> String {
        var current = label
        var visited: Set<String> = []
        while let next = forwarding[current], visited.insert(current).inserted {
            current = next
        }
        return current
    }

    // Don't thread away the entry block.
    if let entry = function.blocks.first {
        forwarding.removeValue(forKey: entry.label)
    }

    // Build predecessor map BEFORE remapping so we can fix up phis.
    var predsBeforeRemap: [String: [String]] = [:]
    for block in function.blocks {
        for succ in block.terminator.successorLabels {
            predsBeforeRemap[succ, default: []].append(block.label)
        }
    }

    // For a forwarded block, find its "real" (non-forwarded) predecessors
    // by walking backwards through forwarding chains.
    func realPredecessors(_ label: String) -> [String] {
        guard forwarding[label] != nil else { return [label] }
        return (predsBeforeRemap[label] ?? []).flatMap { realPredecessors($0) }
    }

    var newBlocks = function.blocks.map { block in
        Block(label: block.label, phis: block.phis, instructions: block.instructions,
              terminator: block.terminator.remapLabels { resolve($0) })
    }

    // Check for conflicts: if forwarding would create duplicate phi args from
    // the same real predecessor with different values, don't forward those blocks.
    // Build a set of block labels that must NOT be forwarded.
    var unsafeToForward: Set<String> = []
    for block in function.blocks {
        guard !block.phis.isEmpty else { continue }
        for phi in block.phis {
            // Collect what real predecessors each forwarded arg would resolve to.
            var realPredValues: [String: [Operand]] = [:]
            for arg in phi.args {
                if forwarding[arg.label] != nil {
                    for rp in realPredecessors(arg.label) {
                        realPredValues[rp, default: []].append(arg.value)
                    }
                } else {
                    realPredValues[arg.label, default: []].append(arg.value)
                }
            }
            // If any real predecessor has conflicting values, mark the forwarded
            // blocks that contribute to that predecessor as unsafe.
            for (pred, values) in realPredValues {
                guard values.count > 1 else { continue }
                let first = values[0]
                if values.dropFirst().contains(where: { !sameOperand($0, first) }) {
                    // Conflict: find which forwarded blocks resolve to this pred.
                    for arg in phi.args {
                        if forwarding[arg.label] != nil {
                            let rps = realPredecessors(arg.label)
                            if rps.contains(pred) {
                                unsafeToForward.insert(arg.label)
                            }
                        }
                    }
                }
            }
        }
    }

    // Remove unsafe entries from forwarding.
    for label in unsafeToForward {
        forwarding.removeValue(forKey: label)
    }
    guard !forwarding.isEmpty || !unsafeToForward.isEmpty else { return function }

    // Re-resolve chains after removing unsafe entries.
    // Rebuild newBlocks with cleaned forwarding.
    newBlocks = function.blocks.map { block in
        Block(label: block.label, phis: block.phis, instructions: block.instructions,
              terminator: block.terminator.remapLabels { resolve($0) })
    }

    // Fix up phis: replace forwarded block labels with their real predecessors.
    // When A→B→C is threaded to A→C, the phi at C that references B must
    // be updated to reference A (with the same value, since B was empty).
    newBlocks = newBlocks.map { block in
        guard !block.phis.isEmpty else { return block }
        let newPhis = block.phis.map { phi in
            var newArgs: [(label: String, value: Operand)] = []
            for arg in phi.args {
                if forwarding[arg.label] != nil {
                    for realPred in realPredecessors(arg.label) {
                        newArgs.append((label: realPred, value: arg.value))
                    }
                } else {
                    newArgs.append(arg)
                }
            }
            return Phi(dest: phi.dest, args: newArgs)
        }
        return Block(label: block.label, phis: newPhis,
                     instructions: block.instructions, terminator: block.terminator)
    }

    return eliminateDeadBlocks(in: withBlocks(function, newBlocks))
}

// MARK: - Block Merging

/// Merge block A into B when A's sole successor is B and B's sole predecessor is A.
public func mergeBlocks(in function: Function) -> Function {
    var blocks = function.blocks
    var changed = true
    while changed {
        changed = false
        var predCount: [String: Int] = [:]
        for b in blocks {
            for succ in b.terminator.successorLabels {
                predCount[succ, default: 0] += 1
            }
        }
        // Track label renames: when B is merged into A, rename B → A in phi args.
        var labelRename: [String: String] = [:]
        var removed: Set<String> = []
        var merged: [Block] = []
        for var block in blocks {
            if removed.contains(block.label) { continue }
            while case .goto(let target) = block.terminator,
                  predCount[target] == 1,
                  target != block.label,
                  let succIdx = blocks.firstIndex(where: { $0.label == target && !removed.contains($0.label) }) {
                let succ = blocks[succIdx]
                let phiAssigns = succ.phis.map { phi -> Instr in
                    let val = phi.args.first?.value ?? .intConst(0, type: phi.dest.type)
                    return .assign(dest: phi.dest, src: val)
                }
                block = Block(label: block.label, phis: block.phis,
                              instructions: block.instructions + phiAssigns + succ.instructions,
                              terminator: succ.terminator)
                labelRename[target] = block.label
                removed.insert(target)
                changed = true
            }
            merged.append(block)
        }
        blocks = merged

        // Update phi args to reflect merged block labels.
        if !labelRename.isEmpty {
            blocks = blocks.map { block in
                guard !block.phis.isEmpty else { return block }
                let newPhis = block.phis.map { phi in
                    Phi(dest: phi.dest, args: phi.args.map { arg in
                        (label: labelRename[arg.label] ?? arg.label, value: arg.value)
                    })
                }
                return Block(label: block.label, phis: newPhis,
                             instructions: block.instructions, terminator: block.terminator)
            }
        }
    }
    var result = withBlocks(function, blocks)
    result.invalidateCFG()
    return result
}
