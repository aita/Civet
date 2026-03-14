import Tree

/// Loop Unrolling (factor 2) for small innermost loops.
///
/// Duplicates the loop body once, halving branch overhead. Only targets
/// simple loops with a single back-edge (latch), a preheader,
/// small body (≤30 instructions), and no function calls.
///
/// Handles both test-at-top (while) and test-at-bottom (do-while) loops.
/// Inserts trampoline blocks for clone exit edges to correctly propagate
/// header phi values through the unrolled iteration.
public func loopUnroll(in function: Function) -> Function {
    var blocks = function.blocks
    guard blocks.count > 1 else { return function }

    let domTree = DominatorTree(function)
    let loopInfo = LoopInfo(function, domTree: domTree)
    guard !loopInfo.loops.isEmpty else { return function }

    // Find minimum variable ID for generating fresh IDs.
    var nextId: Int = {
        var minId = 0
        for block in blocks {
            for phi in block.phis { minId = min(minId, phi.dest.id) }
            for instr in block.instructions {
                if let d = instr.dest { minId = min(minId, d.id) }
            }
        }
        return minId - 1
    }()

    var changed = false

    for loop in loopInfo.loops {
        guard let _ = loop.preheader else { continue }

        let headerIdx = loop.header
        let headerLabel = blocks[headerIdx].label
        if headerLabel.contains(".u1") { continue }

        let headerBlock = blocks[headerIdx]
        guard !headerBlock.phis.isEmpty else { continue }

        let bodyInstrCount = loop.blocks.reduce(0) { $0 + blocks[$1].instructions.count }
        guard bodyInstrCount <= 30 else { continue }

        let hasCall = loop.blocks.contains { bi in
            blocks[bi].instructions.contains {
                if case .call = $0 { return true }; return false
            }
        }
        guard !hasCall else { continue }

        let hasComputedGoto = loop.blocks.contains { bi in
            if case .computedGoto = blocks[bi].terminator { return true }
            return false
        }
        guard !hasComputedGoto else { continue }

        // Find single latch.
        let latchIdx: Int
        if loop.blocks.count == 1 {
            guard headerBlock.terminator.successorLabels.contains(headerLabel)
            else { continue }
            latchIdx = headerIdx
        } else {
            let latches = loop.blocks.filter { bi in
                blocks[bi].terminator.successorLabels.contains(headerLabel)
            }
            guard latches.count == 1 else { continue }
            latchIdx = latches.first!
        }
        let latchLabel = blocks[latchIdx].label

        // === Build clone mappings ===

        var phiBackEdgeValues: [Int: Operand] = [:]
        for phi in headerBlock.phis {
            guard let backArg = phi.args.first(where: { $0.label == latchLabel }) else {
                continue
            }
            phiBackEdgeValues[phi.dest.id] = backArg.value
        }
        guard phiBackEdgeValues.count == headerBlock.phis.count else { continue }

        var varRemap: [Int: Int] = [:]
        let phiDestIds = Set(headerBlock.phis.map(\.dest.id))

        for bi in loop.blocks {
            if bi != headerIdx {
                for phi in blocks[bi].phis {
                    varRemap[phi.dest.id] = nextId; nextId -= 1
                }
            }
            for instr in blocks[bi].instructions {
                if let d = instr.dest {
                    varRemap[d.id] = nextId; nextId -= 1
                }
            }
        }

        var labelRemap: [String: String] = [:]
        for bi in loop.blocks {
            labelRemap[blocks[bi].label] = blocks[bi].label + ".u1"
        }

        // === Remap helpers ===

        func remapOperand(_ op: Operand) -> Operand {
            switch op {
            case .variable(let name, let id, let type):
                if phiDestIds.contains(id), let backVal = phiBackEdgeValues[id] {
                    return backVal
                }
                if let newId = varRemap[id] {
                    return .variable(name: name + ".u1", id: newId, type: type)
                }
                return op
            default:
                return op
            }
        }

        func remapPlace(_ p: Place) -> Place {
            if let newId = varRemap[p.id] {
                return Place(name: p.name + ".u1", id: newId, type: p.type)
            }
            return p
        }

        func remapLabel(_ l: String) -> String {
            labelRemap[l] ?? l
        }

        func remapInstr(_ instr: Instr) -> Instr {
            let r = instr.remapOperands(remapOperand)
            switch r {
            case .assign(let d, let s):
                return .assign(dest: remapPlace(d), src: s)
            case .binary(let d, let op, let l, let rhs):
                return .binary(dest: remapPlace(d), op: op, lhs: l, rhs: rhs)
            case .unary(let d, let op, let s):
                return .unary(dest: remapPlace(d), op: op, src: s)
            case .call(let d, let c, let args):
                return .call(dest: d.map(remapPlace), callee: c, args: args)
            case .addressOf(let d, let s):
                return .addressOf(dest: remapPlace(d), src: s)
            case .load(let d, let a):
                return .load(dest: remapPlace(d), addr: a)
            case .store(let a, let v):
                return .store(addr: a, value: v)
            case .cast(let d, let s, let t):
                return .cast(dest: remapPlace(d), src: s, to: t)
            case .cas(let d, let a, let o, let n):
                return .cas(dest: remapPlace(d), addr: a, old: o, new: n)
            case .exchange(let d, let a, let v):
                return .exchange(dest: remapPlace(d), addr: a, value: v)
            case .member(let d, let b, let name, let off):
                return .member(dest: remapPlace(d), base: b, name: name, offset: off)
            case .asm(let s):
                return .asm(s)
            case .compare(let l, let rhs):
                return .compare(lhs: l, rhs: rhs)
            case .test(let v):
                return .test(v)
            }
        }

        // === Identify exit blocks and needed value fixes ===

        // For each exit block, we need to ensure that header phi dest variables
        // get the correct "post-first-iteration" values when exiting from the clone.
        // We do this by inserting a trampoline block that carries the updated values.
        //
        // Example: original exit does `return s` where s is header phi dest.
        // After unrolling: clone exit should use s_next (the first iteration's result).
        // Trampoline assigns s_tramp = s_next, then jumps to a modified exit block
        // with phi(s_merged, [(header, s), (trampoline, s_tramp)]).

        // Find which loop blocks exit to which exit blocks.
        var exitEdges: [(loopBlockIdx: Int, exitLabel: String)] = []
        for bi in loop.blocks {
            for succLabel in blocks[bi].terminator.successorLabels {
                if let si = domTree.labelIndex[succLabel], !loop.blocks.contains(si) {
                    exitEdges.append((bi, succLabel))
                }
            }
        }
        // For simplicity, skip loops with too many exit edges.
        guard exitEdges.count <= 2 else { continue }

        let cloneHeaderLabel = remapLabel(headerLabel)
        let cloneLatchLabel = remapLabel(latchLabel)

        // Build trampoline info for each unique exit label.
        struct TrampolineInfo {
            let exitLabel: String
            let trampolineLabel: String
            // assigns: for each header phi dest, create fresh var = back-edge value
            var assigns: [Instr] = []
            // Map: original phi dest id → trampoline fresh place
            var valueMap: [Int: Place] = [:]
        }

        var trampolineInfos: [String: TrampolineInfo] = [:]
        for edge in exitEdges {
            let exitLabel = edge.exitLabel
            if trampolineInfos[exitLabel] != nil { continue }

            var info = TrampolineInfo(
                exitLabel: exitLabel,
                trampolineLabel: exitLabel + ".tramp.u1"
            )

            // For each header phi, create a trampoline assignment.
            for phi in headerBlock.phis {
                guard let backVal = phiBackEdgeValues[phi.dest.id] else { continue }
                let freshPlace = Place(
                    name: phi.dest.name + ".tramp",
                    id: nextId,
                    type: phi.dest.type
                )
                nextId -= 1
                info.assigns.append(.assign(dest: freshPlace, src: backVal))
                info.valueMap[phi.dest.id] = freshPlace
            }

            trampolineInfos[exitLabel] = info
        }

        // === Clone loop blocks ===

        let sortedLoopBlocks = loop.blocks.sorted()

        var clonedBlocks: [Block] = []
        for bi in sortedLoopBlocks {
            let block = blocks[bi]
            let newLabel = remapLabel(block.label)

            var newPhis: [Phi] = []
            if bi != headerIdx {
                newPhis = block.phis.map { phi in
                    Phi(
                        dest: remapPlace(phi.dest),
                        args: phi.args.map { arg in
                            (label: remapLabel(arg.label), value: remapOperand(arg.value))
                        }
                    )
                }
            }

            let newInstrs = block.instructions.map(remapInstr)

            var newTerm = block.terminator
                .remapLabels(remapLabel)
                .remapOperands(remapOperand)

            // Redirect clone exit edges to trampolines.
            for (exitLabel, info) in trampolineInfos {
                if newTerm.successorLabels.contains(exitLabel) {
                    newTerm = newTerm.remapLabels {
                        $0 == exitLabel ? info.trampolineLabel : $0
                    }
                }
            }

            clonedBlocks.append(Block(
                label: newLabel, phis: newPhis,
                instructions: newInstrs, terminator: newTerm
            ))
        }

        // Create trampoline blocks.
        var trampolineBlocks: [Block] = []
        for (_, info) in trampolineInfos {
            trampolineBlocks.append(Block(
                label: info.trampolineLabel,
                instructions: info.assigns,
                terminator: .goto(info.exitLabel)
            ))
        }

        // === Wire the original and clone together ===

        // 1. Original latch's back-edge → clone header.
        blocks[latchIdx] = Block(
            label: latchLabel, phis: blocks[latchIdx].phis,
            instructions: blocks[latchIdx].instructions,
            terminator: blocks[latchIdx].terminator.remapLabels {
                $0 == headerLabel ? cloneHeaderLabel : $0
            }
        )

        // 2. Clone's latch back-edge → original header.
        for (ci, cloneBlock) in clonedBlocks.enumerated() {
            if cloneBlock.label == cloneLatchLabel {
                clonedBlocks[ci] = Block(
                    label: cloneBlock.label, phis: cloneBlock.phis,
                    instructions: cloneBlock.instructions,
                    terminator: cloneBlock.terminator.remapLabels {
                        $0 == cloneHeaderLabel ? headerLabel : $0
                    }
                )
            }
        }

        // 3. Update header phis: back-edge now comes from clone's latch.
        let newHeaderPhis = headerBlock.phis.map { phi -> Phi in
            let newArgs = phi.args.map { arg -> (label: String, value: Operand) in
                if arg.label == latchLabel {
                    return (label: cloneLatchLabel, value: remapOperand(arg.value))
                }
                return arg
            }
            return Phi(dest: phi.dest, args: newArgs)
        }
        blocks[headerIdx] = Block(
            label: headerLabel, phis: newHeaderPhis,
            instructions: blocks[headerIdx].instructions,
            terminator: blocks[headerIdx].terminator
        )

        // 4. Update exit blocks: add phis to merge original and trampoline values.
        for (exitLabel, info) in trampolineInfos {
            guard let exitIdx = blocks.firstIndex(where: { $0.label == exitLabel }) else {
                continue
            }
            let exitBlock = blocks[exitIdx]

            // For existing phis: add trampoline args.
            var newPhis = exitBlock.phis.map { phi -> Phi in
                var newArgs = phi.args
                for arg in phi.args {
                    if let srcIdx = domTree.labelIndex[arg.label],
                       loop.blocks.contains(srcIdx) {
                        // Add trampoline version.
                        let cloneValue: Operand
                        // If the phi arg value is a header phi dest, use the trampoline var.
                        if case .variable(_, let id, _) = arg.value,
                           let trampPlace = info.valueMap[id] {
                            cloneValue = trampPlace.asOperand
                        } else {
                            cloneValue = remapOperand(arg.value)
                        }
                        newArgs.append((label: info.trampolineLabel, value: cloneValue))
                    }
                }
                return Phi(dest: phi.dest, args: newArgs)
            }

            // For header phi dests used in exit block (but not in existing phis):
            // scan instructions, terminator, AND successor block phis for uses.
            var usedPhiDests: Set<Int> = []
            let existingPhiDests = Set(exitBlock.phis.map(\.dest.id))
            for instr in exitBlock.instructions {
                for op in instr.operands {
                    if case .variable(_, let id, _) = op, phiDestIds.contains(id) {
                        usedPhiDests.insert(id)
                    }
                }
            }
            for op in exitBlock.terminator.operands {
                if case .variable(_, let id, _) = op, phiDestIds.contains(id) {
                    usedPhiDests.insert(id)
                }
            }
            // Also scan successor blocks' phis for header phi dests flowing
            // through the exit block (e.g., nested loop exit → outer loop phi).
            for succLabel in exitBlock.terminator.successorLabels {
                if let succIdx = blocks.firstIndex(where: { $0.label == succLabel }) {
                    for phi in blocks[succIdx].phis {
                        for arg in phi.args where arg.label == exitLabel {
                            if case .variable(_, let id, _) = arg.value,
                               phiDestIds.contains(id) {
                                usedPhiDests.insert(id)
                            }
                        }
                    }
                }
            }

            // For each used header phi dest not already covered by a phi:
            // Create a new phi and rewrite uses.
            var instrReplacements: [Int: Operand] = [:]  // phi dest id → new merged phi dest
            for phi in headerBlock.phis {
                let id = phi.dest.id
                guard usedPhiDests.contains(id) else { continue }
                // Check if already handled by existing exit phi.
                let alreadyHandled = exitBlock.phis.contains { p in
                    p.args.contains { arg in
                        if case .variable(_, let aid, _) = arg.value { return aid == id }
                        return false
                    }
                }
                if alreadyHandled { continue }

                // Create a new phi: merge original value (from header) and trampoline value.
                let mergedPlace = Place(
                    name: phi.dest.name + ".merged",
                    id: nextId,
                    type: phi.dest.type
                )
                nextId -= 1

                // Find which loop blocks reach this exit.
                var phiArgs: [(label: String, value: Operand)] = []
                for edge in exitEdges where edge.exitLabel == exitLabel {
                    let srcLabel = blocks[edge.loopBlockIdx].label
                    phiArgs.append((label: srcLabel, value: phi.dest.asOperand))
                }
                // Add trampoline arg with updated value.
                if let trampPlace = info.valueMap[id] {
                    phiArgs.append((label: info.trampolineLabel, value: trampPlace.asOperand))
                }

                newPhis.append(Phi(dest: mergedPlace, args: phiArgs))
                instrReplacements[id] = mergedPlace.asOperand
            }

            // Rewrite exit block instructions and terminator to use merged phis.
            var newInstrs = exitBlock.instructions
            var newTerm = exitBlock.terminator
            if !instrReplacements.isEmpty {
                func rewrite(_ op: Operand) -> Operand {
                    if case .variable(_, let id, _) = op,
                       let replacement = instrReplacements[id] {
                        return replacement
                    }
                    return op
                }
                newInstrs = newInstrs.map { $0.remapOperands(rewrite) }
                newTerm = newTerm.remapOperands(rewrite)

                // Also rewrite successor blocks' phi args that reference header
                // phi dests via the exit block label (nested loop case).
                for succLabel in exitBlock.terminator.successorLabels {
                    if let succIdx = blocks.firstIndex(where: { $0.label == succLabel }) {
                        let succBlock = blocks[succIdx]
                        let updatedPhis = succBlock.phis.map { phi -> Phi in
                            let updatedArgs = phi.args.map { arg -> (label: String, value: Operand) in
                                guard arg.label == exitLabel else { return arg }
                                return (label: arg.label, value: rewrite(arg.value))
                            }
                            return Phi(dest: phi.dest, args: updatedArgs)
                        }
                        if true {  // always update to be safe
                            blocks[succIdx] = Block(
                                label: succBlock.label, phis: updatedPhis,
                                instructions: succBlock.instructions,
                                terminator: succBlock.terminator
                            )
                        }
                    }
                }
            }

            blocks[exitIdx] = Block(
                label: exitLabel, phis: newPhis,
                instructions: newInstrs, terminator: newTerm
            )
        }

        // 5. Insert cloned blocks + trampolines.
        let insertionPoint = sortedLoopBlocks.last! + 1
        blocks.insert(contentsOf: clonedBlocks + trampolineBlocks, at: insertionPoint)

        changed = true
        break
    }

    guard changed else { return function }
    return withBlocks(function, blocks)
}
