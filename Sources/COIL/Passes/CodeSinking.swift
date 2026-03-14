import Tree

/// Code Sinking: move definitions closer to their unique use site.
///
/// If a definition `x = op` is used exclusively in a single successor block B,
/// and the operation has no side effects, we sink the instruction to the
/// beginning of B. This reduces live-range pressure and avoids executing the
/// computation on paths that never reach the use.
///
/// This is the complement of LICM (which hoists code outward).
///
/// Conditions for sinking a definition in block A to block B:
/// 1. The instruction has no side effects (per `Instr.hasSideEffects`).
/// 2. The destination variable is used in exactly one block (block B).
/// 3. That block B is a direct successor of A.
/// 4. The destination is not referenced in A itself (instructions or terminator).
///
/// Loads are excluded from sinking (no alias analysis; a later store in A could
/// alias the load address).
///
/// The pipeline runs this pass inside the 4-iteration loop so multi-level
/// chains are resolved incrementally.
public func codeSinking(in function: Function) -> Function {
    let blocks = function.blocks
    guard blocks.count > 1 else { return function }

    // Build use-site map: varId → set of block labels where the variable appears.
    var usedIn: [Int: Set<String>] = [:]
    // Variables that appear as phi arguments must NOT be sunk: phi args are
    // semantically evaluated in the predecessor block, so the defining
    // instruction must remain in the predecessor.
    var phiArgIds: Set<Int> = []
    for block in blocks {
        func note(_ op: Operand) {
            if case .variable(_, let id, _) = op { usedIn[id, default: []].insert(block.label) }
        }
        for instr in block.instructions { instr.operands.forEach(note) }
        for phi in block.phis {
            phi.operands.forEach(note)
            // Mark all phi argument variables as phi-arg (unsinkable).
            for (_, op) in phi.args {
                if case .variable(_, let id, _) = op { phiArgIds.insert(id) }
            }
        }
        block.terminator.operands.forEach(note)
    }

    // Index blocks by label for fast access.
    var blockIndex: [String: Int] = [:]
    for (i, b) in blocks.enumerated() { blockIndex[b.label] = i }

    // Candidates to sink: (srcBlockIdx, instrIdx, dstLabel)
    struct Candidate { let srcIdx: Int; let instrIdx: Int; let dstLabel: String }
    var candidates: [Candidate] = []

    for (srcIdx, block) in blocks.enumerated() {
        let succs = block.terminator.successorLabels
        guard !succs.isEmpty else { continue }

        for (instrIdx, instr) in block.instructions.enumerated() {
            guard !instr.hasSideEffects, let dest = instr.dest else { continue }
            // Exclude loads — may alias stores earlier in the block.
            if case .load = instr { continue }
            let id = dest.id
            // Phi arguments must be defined in their predecessor block; skip.
            guard !phiArgIds.contains(id) else { continue }

            // Must not be used in the defining block.
            guard usedIn[id]?.contains(block.label) != true else { continue }

            // All uses must be in exactly one block.
            guard let useBlocks = usedIn[id], useBlocks.count == 1,
                  let dstLabel = useBlocks.first else { continue }

            // That block must be a direct successor.
            guard succs.contains(dstLabel) else { continue }

            candidates.append(Candidate(srcIdx: srcIdx, instrIdx: instrIdx, dstLabel: dstLabel))
        }
    }

    guard !candidates.isEmpty else { return function }

    var newBlocks = blocks

    // Group by source block; remove instructions in descending index order
    // so earlier indices stay valid after each removal.
    let grouped = Dictionary(grouping: candidates, by: \.srcIdx)
    for (srcIdx, group) in grouped {
        let sorted = group.sorted { $0.instrIdx > $1.instrIdx }
        var srcInstrs = newBlocks[srcIdx].instructions

        var toInsert: [String: [Instr]] = [:]
        for c in sorted {
            let sunk = srcInstrs.remove(at: c.instrIdx)
            toInsert[c.dstLabel, default: []].insert(sunk, at: 0)
        }

        newBlocks[srcIdx] = newBlocks[srcIdx].with(instructions: srcInstrs)

        for (dstLabel, sunkInstrs) in toInsert {
            guard let dstIdx = blockIndex[dstLabel] else { continue }
            newBlocks[dstIdx] = newBlocks[dstIdx].with(
                instructions: sunkInstrs + newBlocks[dstIdx].instructions)
        }
    }

    return withBlocks(function, newBlocks)
}
