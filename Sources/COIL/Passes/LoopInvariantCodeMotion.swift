/// Insert preheader blocks for loops that lack a single outside predecessor.
///
/// A preheader is a dedicated block that is the sole predecessor of the loop
/// header from outside the loop. When the header has multiple outside
/// predecessors, this function creates a new block, redirects all outside
/// predecessors to it, and splits header phi nodes accordingly.
///
/// Returns `true` if any preheaders were inserted.
private func insertPreheaders(_ blocks: inout [Block], loopInfo: LoopInfo,
                              domTree: DominatorTree) -> Bool {
    // Find the minimum variable ID across all blocks for fresh ID generation.
    var minId = 0
    for block in blocks {
        for phi in block.phis {
            minId = min(minId, phi.dest.id)
            for arg in phi.args {
                if case .variable(_, let id, _) = arg.value { minId = min(minId, id) }
            }
        }
        for instr in block.instructions {
            if let d = instr.dest { minId = min(minId, d.id) }
            for op in instr.operands {
                if case .variable(_, let id, _) = op { minId = min(minId, id) }
            }
        }
    }
    var nextFreshId = minId - 1

    // Collect (headerIndex, outsidePreds) for loops needing preheaders.
    // Process in decreasing header index order so insertions don't invalidate
    // earlier indices.
    var insertions: [(headerIdx: Int, outsidePreds: [Int])] = []
    for loop in loopInfo.loops {
        guard loop.preheader == nil else { continue }
        let outsidePreds = domTree.preds[loop.header].filter { !loop.blocks.contains($0) }
        guard outsidePreds.count >= 2 else { continue }
        insertions.append((headerIdx: loop.header, outsidePreds: outsidePreds))
    }
    guard !insertions.isEmpty else { return false }

    // Sort by decreasing header index so we insert from the back.
    insertions.sort { $0.headerIdx > $1.headerIdx }

    for (headerIdx, outsidePreds) in insertions {
        let headerLabel = blocks[headerIdx].label
        let preheaderLabel = headerLabel + ".ph"
        let outsidePredLabels = Set(outsidePreds.map { blocks[$0].label })

        // Split header phi nodes.
        var preheaderPhis: [Phi] = []
        var newHeaderPhis: [Phi] = []
        for phi in blocks[headerIdx].phis {
            let outsideArgs = phi.args.filter { outsidePredLabels.contains($0.label) }
            let insideArgs = phi.args.filter { !outsidePredLabels.contains($0.label) }

            if outsideArgs.count >= 2 {
                // Create a new phi in the preheader merging outside args.
                let freshId = nextFreshId
                nextFreshId -= 1
                let phDest = Place(name: phi.dest.name, id: freshId, type: phi.dest.type)
                preheaderPhis.append(Phi(dest: phDest, args: outsideArgs))
                // Replace all outside args in header phi with single preheader arg.
                let merged = insideArgs + [(label: preheaderLabel, value: phDest.asOperand)]
                newHeaderPhis.append(Phi(dest: phi.dest, args: merged))
            } else if outsideArgs.count == 1 {
                // Just relabel the single outside arg to preheaderLabel.
                let relabeled = [(label: preheaderLabel, value: outsideArgs[0].value)]
                newHeaderPhis.append(Phi(dest: phi.dest, args: insideArgs + relabeled))
            } else {
                // No outside args — keep as-is (shouldn't happen in well-formed SSA).
                newHeaderPhis.append(phi)
            }
        }

        // Update header phis.
        blocks[headerIdx] = blocks[headerIdx].with(phis: newHeaderPhis)

        // Redirect outside predecessors to the preheader.
        for predIdx in outsidePreds {
            blocks[predIdx] = blocks[predIdx].with(
                terminator: blocks[predIdx].terminator.remapLabels {
                    $0 == headerLabel ? preheaderLabel : $0
                }
            )
        }

        // Create and insert preheader block immediately before the header.
        let preheaderBlock = Block(
            label: preheaderLabel,
            phis: preheaderPhis,
            instructions: [],
            terminator: .goto(headerLabel)
        )
        blocks.insert(preheaderBlock, at: headerIdx)
    }

    return true
}

/// Loop Invariant Code Motion.
///
/// Hoists instructions whose operands are all loop-invariant to the loop's
/// preheader block. Creates preheader blocks when necessary.
public func licm(in function: Function) -> Function {
    var blocks = function.blocks
    guard blocks.count > 1 else { return function }

    var f = function
    var domTree = f.dominatorTree()
    var loopInfo = LoopInfo(f, domTree: domTree)
    guard !loopInfo.loops.isEmpty else { return function }

    // Insert preheaders for loops that lack them.
    var changed = false
    if insertPreheaders(&blocks, loopInfo: loopInfo, domTree: domTree) {
        f = withBlocks(function, blocks)
        domTree = f.dominatorTree()
        loopInfo = LoopInfo(f, domTree: domTree)
        changed = true
    }

    // Build definition map: varId → block index where it's defined.
    func buildDefBlock() -> [Int: Int] {
        var defBlock: [Int: Int] = [:]
        for (bi, block) in blocks.enumerated() {
            for phi in block.phis {
                defBlock[phi.dest.id] = bi
            }
            for instr in block.instructions {
                if let dest = instr.dest {
                    defBlock[dest.id] = bi
                }
            }
        }
        return defBlock
    }

    // Process loops from outermost to innermost (reverse order since sorted innermost first).
    for loop in loopInfo.loops.reversed() {
        guard let preheaderIdx = loop.preheader else {
            continue
        }

        let defBlock = buildDefBlock()

        let addressTakenInLoop = collectAddressTaken(in: loop.blocks.map { blocks[$0] })

        // Collect store addresses in the loop for alias-based load hoisting.
        var loopStoreAddrs: [Operand] = []
        for bi in loop.blocks {
            for instr in blocks[bi].instructions {
                if case .store(let addr, _) = instr { loopStoreAddrs.append(addr) }
            }
        }
        let aa = AliasAnalysis(withBlocks(function, blocks))

        // Check if an operand is loop-invariant.
        var hoisted: Set<Int> = []  // var IDs already hoisted
        func isLoopInvariant(_ op: Operand) -> Bool {
            switch op {
            case .intConst, .floatConst, .labelAddr:
                return true
            case .variable(_, let id, _):
                if hoisted.contains(id) { return true }
                // Address-taken variables may be modified through memory.
                if addressTakenInLoop.contains(id) { return false }
                guard let db = defBlock[id] else { return true }  // params/undefined
                return !loop.blocks.contains(db)
            }
        }

        // Scan loop body in RPO order for hoist candidates.
        for bi in domTree.rpoOrder where loop.blocks.contains(bi) {
            guard bi != preheaderIdx else { continue }
            let block = blocks[bi]

            var remainingInstrs: [Instr] = []
            for instr in block.instructions {
                // Skip side-effecting instructions.
                if instr.hasSideEffects {
                    remainingInstrs.append(instr)
                    continue
                }
                // Loads can be hoisted if their address is loop-invariant AND
                // the address does not alias any store in the loop.
                if case .load(_, let addr) = instr {
                    let addrInvariant = isLoopInvariant(addr)
                    let noAlias = addrInvariant && loopStoreAddrs.allSatisfy {
                        !aa.mayAlias(addr, $0)
                    }
                    if !noAlias {
                        remainingInstrs.append(instr)
                        continue
                    }
                    // Fall through to hoisting logic below.
                }

                guard let dest = instr.dest else {
                    remainingInstrs.append(instr)
                    continue
                }

                // Check all operands are loop-invariant.
                let allInvariant = instr.operands.allSatisfy(isLoopInvariant)
                guard allInvariant else {
                    remainingInstrs.append(instr)
                    continue
                }

                // Check dest dominates all exit blocks.
                let dominatesExits = loop.exitBlocks.allSatisfy { exit in
                    domTree.dominates(bi, exit)
                }
                guard dominatesExits else {
                    remainingInstrs.append(instr)
                    continue
                }

                // Hoist: move to preheader (before terminator).
                var phBlock = blocks[preheaderIdx]
                phBlock.instructions.append(instr)
                blocks[preheaderIdx] = phBlock
                hoisted.insert(dest.id)
                changed = true
            }

            if remainingInstrs.count != block.instructions.count {
                blocks[bi] = block.with(instructions: remainingInstrs)
            }
        }
    }

    guard changed else { return function }
    return withBlocks(function, blocks)
}
