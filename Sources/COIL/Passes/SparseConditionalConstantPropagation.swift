import Tree

/// Sparse Conditional Constant Propagation (Wegman-Zadeck algorithm).
///
/// Subsumes constant folding, branch simplification, and unreachable block elimination.
/// Uses two worklists: CFG edges and SSA def-use edges.
/// Tracks executable *edges* (not just reachable blocks) for correct phi evaluation.
public func sccp(in function: Function) -> Function {
    let blocks = function.blocks
    let n = blocks.count
    guard n > 0 else { return function }

    let labelIndex = buildLabelIndex(blocks)

    // ── Lattice ─────────────────────────────────────────────────────────
    var lattice: [Int: LatticeValue] = [:]

    // Parameters are overdefined (we don't know their values at compile time).
    for param in function.params {
        if case .local(let id) = param.storage {
            lattice[id] = .bottom
        }
    }

    // Mark variables that SCCP cannot safely track as overdefined (.bottom):
    // 1. Address-taken variables (modified through memory)
    // 2. Aggregate types (arrays, structs, unions) — represent memory locations
    // 3. Variables with multiple definitions (not in SSA form)
    // 4. Variables used but never defined in this function (globals, string literals)
    var defCount: [Int: Int] = [:]
    var usedVarIds: Set<Int> = []
    for block in blocks {
        for phi in block.phis {
            defCount[phi.dest.id, default: 0] += 1
            for arg in phi.args {
                if case .variable(_, let id, _) = arg.value { usedVarIds.insert(id) }
            }
        }
        for instr in block.instructions {
            if let dest = instr.dest {
                defCount[dest.id, default: 0] += 1
            }
            for op in instr.operands {
                if case .variable(_, let id, _) = op { usedVarIds.insert(id) }
            }
            if case .addressOf(_, let src) = instr,
               case .variable(_, let id, _) = src {
                lattice[id] = .bottom
            }
        }
        for op in block.terminator.operands {
            if case .variable(_, let id, _) = op { usedVarIds.insert(id) }
        }
    }
    // Multiple definitions → not SSA, treat as overdefined.
    for (id, count) in defCount where count > 1 {
        lattice[id] = .bottom
    }
    // Used but never defined → global/extern, treat as overdefined.
    for id in usedVarIds where defCount[id] == nil {
        lattice[id] = .bottom
    }
    // Aggregate-typed locals → memory locations, not scalar values.
    for local in function.locals {
        if case .local(let id) = local.storage {
            switch local.type {
            case .array, .structType, .unionType, .vla:
                lattice[id] = .bottom
            default:
                break
            }
        }
    }

    func getLattice(_ op: Operand) -> LatticeValue {
        switch op {
        case .intConst(let v, _): return .constant(v)
        case .floatConst(let v, _): return .floatConstant(v)
        case .variable(_, let id, _): return lattice[id] ?? .top
        case .labelAddr: return .bottom
        }
    }

    func meetTwo(_ a: LatticeValue, _ b: LatticeValue) -> LatticeValue {
        switch (a, b) {
        case (.top, _): return b
        case (_, .top): return a
        case (.bottom, _), (_, .bottom): return .bottom
        case (.constant(let x), .constant(let y)):
            return x == y ? .constant(x) : .bottom
        case (.floatConstant(let x), .floatConstant(let y)):
            return x == y ? .floatConstant(x) : .bottom
        default:
            return .bottom
        }
    }

    // ── Build use map: varId → [(blockIdx, instrOrPhiIndex)] ─────────
    struct UseLocation {
        let blockIdx: Int
        let isPhi: Bool
        let index: Int
    }
    var useMap: [Int: [UseLocation]] = [:]

    func recordUse(_ op: Operand, blockIdx: Int, isPhi: Bool, index: Int) {
        if case .variable(_, let id, _) = op {
            useMap[id, default: []].append(
                UseLocation(blockIdx: blockIdx, isPhi: isPhi, index: index))
        }
    }

    for (bi, block) in blocks.enumerated() {
        for (pi, phi) in block.phis.enumerated() {
            for arg in phi.args { recordUse(arg.value, blockIdx: bi, isPhi: true, index: pi) }
        }
        for (ii, instr) in block.instructions.enumerated() {
            for op in instr.operands { recordUse(op, blockIdx: bi, isPhi: false, index: ii) }
        }
        for op in block.terminator.operands {
            recordUse(op, blockIdx: bi, isPhi: false, index: -1)
        }
    }

    // ── Worklists ───────────────────────────────────────────────────────
    // Track executable EDGES, not just reachable blocks.
    // An edge is encoded as (from * n + to) for efficient set lookup.
    var executableEdges: Set<Int> = []
    var blockReachable = Array(repeating: false, count: n)
    // CFG worklist contains edges: (from, to) encoded as from * n + to.
    // Special: entry block uses sentinel from = -1, encoded as n * n + 0.
    var cfgWorklist: [(from: Int, to: Int)] = [(from: -1, to: 0)]
    var ssaWorklist: [UseLocation] = []

    func edgeKey(_ from: Int, _ to: Int) -> Int { from * n + to }

    func updateLattice(_ id: Int, _ newVal: LatticeValue) {
        let old = lattice[id] ?? .top
        let merged = meetTwo(old, newVal)
        if !sameLattice(old, merged) {
            lattice[id] = merged
            for use in useMap[id] ?? [] {
                ssaWorklist.append(use)
            }
        }
    }

    // ── Evaluate an instruction ─────────────────────────────────────────
    func evaluateInstr(_ instr: Instr) -> LatticeValue? {
        guard let dest = instr.dest else { return nil }
        switch instr {
        case .assign(_, let src):
            return getLattice(src)

        case .binary(_, let op, let lhs, let rhs):
            let lv = getLattice(lhs), rv = getLattice(rhs)
            switch (lv, rv) {
            case (.bottom, _), (_, .bottom): return .bottom
            case (.top, _), (_, .top): return .top
            case (.constant(let a), .constant(let b)):
                // For comparison ops, signedness depends on operand type, not dest type.
                let evalType: CType
                switch op {
                case .lt, .le, .eq, .ne:
                    evalType = lhs.type
                default:
                    evalType = dest.type
                }
                if let result = evalBinary(op, a, b, type: evalType) {
                    return .constant(result)
                }
                return .bottom
            default: return .bottom
            }

        case .unary(_, let op, let src):
            let sv = getLattice(src)
            switch sv {
            case .bottom: return .bottom
            case .top: return .top
            case .constant(let a):
                if let result = evalUnary(op, a, type: dest.type) {
                    return .constant(result)
                }
                return .bottom
            default: return .bottom
            }

        case .cast(_, let src, let toType):
            let sv = getLattice(src)
            switch sv {
            case .bottom: return .bottom
            case .top: return .top
            case .constant(let a):
                switch toType {
                case .float, .double, .longDouble:
                    // Must respect source signedness for int→float conversion.
                    if !isSigned(src.type) {
                        return .floatConstant(Double(UInt64(bitPattern: a)))
                    }
                    return .floatConstant(Double(a))
                default:
                    return .constant(truncateToType(a, toType))
                }
            case .floatConstant(let f):
                switch toType {
                case .bool: return .constant(f != 0 ? 1 : 0)
                case .char, .short, .int, .long:
                    // Float-to-int is UB when out of range; treat as bottom.
                    guard f.isFinite && f >= -9.2e18 && f < 9.2e18 else { return .bottom }
                    return .constant(truncateToType(Int64(f), toType))
                case .float, .double, .longDouble:
                    return .floatConstant(f)
                default: return .bottom
                }
            }

        case .call, .load, .addressOf, .member, .cas, .exchange:
            return .bottom

        default:
            return nil
        }
    }

    // ── Evaluate a phi ──────────────────────────────────────────────────
    func evaluatePhi(_ phi: Phi, blockIdx: Int) -> LatticeValue {
        var result: LatticeValue = .top
        for arg in phi.args {
            // Only consider arguments from predecessors with executable edges TO this block.
            guard let predIdx = labelIndex[arg.label],
                  executableEdges.contains(edgeKey(predIdx, blockIdx)) else { continue }
            result = meetTwo(result, getLattice(arg.value))
            if case .bottom = result { break }
        }
        return result
    }

    // ── Evaluate branch terminator ──────────────────────────────────────
    func evaluateBranch(_ block: Block) -> [String] {
        guard case .branch(let cond, let thenL, let elseL) = block.terminator else {
            return block.terminator.successorLabels
        }
        guard let last = block.instructions.last else { return [thenL, elseL] }
        switch last {
        case .compare(let lhs, let rhs):
            let lv = getLattice(lhs), rv = getLattice(rhs)
            if case .constant(let a) = lv, case .constant(let b) = rv {
                return evaluateCompare(a, b, cond, unsigned: !isSigned(lhs.type)) ? [thenL] : [elseL]
            }
        case .test(let v):
            if case .constant(let a) = getLattice(v) {
                return evaluateTest(a, cond) ? [thenL] : [elseL]
            }
        default:
            break
        }
        return [thenL, elseL]
    }

    // ── Mark successor edges from a block ─────────────────────────────
    func markSuccessors(_ bi: Int) {
        let block = blocks[bi]
        let succs = evaluateBranch(block)
        for succLabel in succs {
            if let si = labelIndex[succLabel] {
                let ek = edgeKey(bi, si)
                if executableEdges.insert(ek).inserted {
                    // New edge discovered.
                    if !blockReachable[si] {
                        // First time reaching this block — process it fully.
                        blockReachable[si] = true
                        cfgWorklist.append((from: bi, to: si))
                    } else {
                        // Block already reachable, but new edge means phis need re-evaluation.
                        let succBlock = blocks[si]
                        for phi in succBlock.phis {
                            let val = evaluatePhi(phi, blockIdx: si)
                            updateLattice(phi.dest.id, val)
                        }
                    }
                }
            }
        }
    }

    // ── Process a block ─────────────────────────────────────────────────
    func processBlock(_ bi: Int) {
        let block = blocks[bi]

        // Evaluate phis.
        for phi in block.phis {
            let val = evaluatePhi(phi, blockIdx: bi)
            updateLattice(phi.dest.id, val)
        }

        // Evaluate instructions.
        for instr in block.instructions {
            if let val = evaluateInstr(instr), let dest = instr.dest {
                updateLattice(dest.id, val)
            }
        }

        // Mark successor edges.
        markSuccessors(bi)
    }

    // ── Main loop ───────────────────────────────────────────────────────
    blockReachable[0] = true
    while !cfgWorklist.isEmpty || !ssaWorklist.isEmpty {
        while let edge = cfgWorklist.popLast() {
            processBlock(edge.to)
        }
        while let use = ssaWorklist.popLast() {
            guard blockReachable[use.blockIdx] else { continue }
            if use.isPhi {
                let phi = blocks[use.blockIdx].phis[use.index]
                let val = evaluatePhi(phi, blockIdx: use.blockIdx)
                updateLattice(phi.dest.id, val)
            } else if use.index >= 0 {
                let instr = blocks[use.blockIdx].instructions[use.index]
                if let val = evaluateInstr(instr), let dest = instr.dest {
                    updateLattice(dest.id, val)
                }
            }
            // Re-evaluate the block's successors (terminator might now be resolvable).
            markSuccessors(use.blockIdx)
        }
    }

    // ── Rewrite ─────────────────────────────────────────────────────────
    func rewriteOperand(_ op: Operand) -> Operand {
        guard case .variable(_, let id, let type) = op else { return op }
        switch lattice[id] {
        case .constant(let v): return .intConst(v, type: type)
        case .floatConstant(let v): return .floatConst(v, type: type)
        default: return op
        }
    }

    // Don't remove unreachable blocks here — leave that to eliminateDeadBlocks/threadJumps.
    // Only rewrite constants and simplify branches in reachable blocks.
    let newBlocks = blocks.enumerated().map { (bi, block) -> Block in
        guard blockReachable[bi] else { return block }

        let newPhis = block.phis.map { phi in
            Phi(dest: phi.dest, args: phi.args.map {
                (label: $0.label, value: rewriteOperand($0.value))
            })
        }

        let newInstrs = block.instructions.map { $0.remapOperands(rewriteOperand) }

        var newTerm = block.terminator.remapOperands(rewriteOperand)

        // Simplify branches with known conditions.
        if case .branch = newTerm {
            let succs = evaluateBranch(Block(label: block.label, phis: newPhis,
                                             instructions: newInstrs, terminator: newTerm))
            if succs.count == 1 {
                newTerm = .goto(succs[0])
            }
        }

        // Remove dead compare/test if branch was simplified to goto.
        var finalInstrs = newInstrs
        if case .goto = newTerm, let last = finalInstrs.last {
            switch last {
            case .compare, .test:
                finalInstrs.removeLast()
            default:
                break
            }
        }

        return block.with(phis: newPhis, instructions: finalInstrs)
            .with(terminator: newTerm)
    }

    var result = withBlocks(function, newBlocks)
    result.invalidateCFG()
    return result
}

// MARK: - Lattice Value

private enum LatticeValue {
    case top
    case constant(Int64)
    case floatConstant(Double)
    case bottom
}

private func sameLattice(_ a: LatticeValue, _ b: LatticeValue) -> Bool {
    switch (a, b) {
    case (.top, .top), (.bottom, .bottom): return true
    case (.constant(let x), .constant(let y)): return x == y
    case (.floatConstant(let x), .floatConstant(let y)): return x == y
    default: return false
    }
}

