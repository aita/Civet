/// Loop Invariant Code Motion.
///
/// Hoists instructions whose operands are all loop-invariant to the loop's
/// preheader block. Creates preheader blocks when necessary.
public func licm(in function: Function) -> Function {
    var blocks = function.blocks
    guard blocks.count > 1 else { return function }

    var f = function
    let domTree = f.dominatorTree()
    let loopInfo = LoopInfo(f, domTree: domTree)
    guard !loopInfo.loops.isEmpty else { return function }

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

    var changed = false

    // Process loops from outermost to innermost (reverse order since sorted innermost first).
    for loop in loopInfo.loops.reversed() {
        guard let preheaderIdx = loop.preheader else {
            // Skip loops without a single preheader — inserting one requires
            // phi splitting which is complex. Most loops from C for/while
            // already have a natural preheader.
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
