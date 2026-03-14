/// Aggressive Dead Code Elimination using SSA def-use chains.
///
/// Starts from essential instructions (side effects, returns) and marks
/// all transitively needed definitions as live. Removes everything else.
public func aggressiveDCE(in function: Function) -> Function {
    let blocks = function.blocks
    let n = blocks.count
    guard n > 0 else { return function }

    // ── Build definition map: varId → (blockIdx, isPhi, index) ──────
    struct DefLocation: Hashable {
        let blockIdx: Int
        let isPhi: Bool
        let index: Int
    }

    // SCCP simplifies dead branches to goto but leaves unreachable blocks
    // in place. Including unreachable blocks in defMap would cause ADCE to
    // use dead definitions, hiding the live ones in reachable blocks.
    let reachable = computeReachable(blocks)

    var defMap: [Int: DefLocation] = [:]
    for (bi, block) in blocks.enumerated() {
        guard reachable[bi] else { continue }
        for (pi, phi) in block.phis.enumerated() {
            defMap[phi.dest.id] = DefLocation(blockIdx: bi, isPhi: true, index: pi)
        }
        for (ii, instr) in block.instructions.enumerated() {
            if let dest = instr.dest {
                defMap[dest.id] = DefLocation(blockIdx: bi, isPhi: false, index: ii)
            }
        }
    }

    // ── Mark essential instructions ─────────────────────────────────────
    let addressTakenIds = collectAddressTaken(in: blocks)

    var liveInstrs: Set<DefLocation> = []
    var worklist: [Int] = []  // variable IDs to process

    func markOperand(_ op: Operand) {
        if case .variable(_, let id, _) = op {
            if let def = defMap[id], liveInstrs.insert(def).inserted {
                worklist.append(id)
            }
        }
    }

    func markOperands(_ ops: [Operand]) {
        for op in ops { markOperand(op) }
    }

    for (bi, block) in blocks.enumerated() {
        guard reachable[bi] else { continue }
        for (ii, instr) in block.instructions.enumerated() {
            let essential: Bool
            switch instr {
            case .store, .cas, .exchange, .asm:
                essential = true
            case .call:
                essential = true
            case .compare, .test:
                // Essential only if followed by a branch terminator.
                if case .branch = block.terminator {
                    essential = true
                } else {
                    essential = false
                }
            case .assign, .cast, .addressOf, .binary, .unary, .load:
                // Writes to address-taken variables are essential: the value may
                // be read through a pointer, so we can't treat it as dead.
                if let dest = instr.dest, addressTakenIds.contains(dest.id) {
                    essential = true
                } else {
                    essential = false
                }
            default:
                essential = false
            }

            if essential {
                if let dest = instr.dest {
                    let def = DefLocation(blockIdx: bi, isPhi: false, index: ii)
                    if liveInstrs.insert(def).inserted {
                        worklist.append(dest.id)
                    }
                }
                markOperands(instr.operands)
            }
        }

        // Return operands are essential.
        markOperands(block.terminator.operands)
    }

    // ── Backward walk: mark all transitively needed definitions ────────
    while let id = worklist.popLast() {
        guard let def = defMap[id] else { continue }
        let block = blocks[def.blockIdx]
        if def.isPhi {
            let phi = block.phis[def.index]
            markOperands(phi.operands)
        } else {
            let instr = block.instructions[def.index]
            markOperands(instr.operands)
        }
    }

    // ── Remove dead instructions and phis ───────────────────────────────
    let newBlocks = blocks.enumerated().map { (bi, block) -> Block in
        // Unreachable blocks: clear all instructions (they'll be removed by
        // threadJumps/mergeBlocks later).
        guard reachable[bi] else {
            return block.with(phis: [], instructions: [])
        }
        let newPhis = block.phis.enumerated().compactMap { (pi, phi) -> Phi? in
            let def = DefLocation(blockIdx: bi, isPhi: true, index: pi)
            return liveInstrs.contains(def) ? phi : nil
        }

        let newInstrs = block.instructions.enumerated().compactMap { (ii, instr) -> Instr? in
            // Side-effect instructions without dest are kept if they were marked essential.
            if instr.dest == nil {
                // compare/test: keep if marked via operands scan.
                switch instr {
                case .store, .asm:
                    return instr  // Always keep stores and asm.
                case .compare, .test:
                    // Keep if the block has a branch terminator (already checked above).
                    if case .branch = block.terminator { return instr }
                    return nil
                default:
                    return instr
                }
            }
            let def = DefLocation(blockIdx: bi, isPhi: false, index: ii)
            return liveInstrs.contains(def) ? instr : nil
        }

        return block.with(phis: newPhis, instructions: newInstrs)
    }

    return withBlocks(function, newBlocks)
}
