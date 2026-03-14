/// Converts a COIL `Function` (or `Program`) from non-SSA form into SSA form
/// by inserting phi functions and renaming variables.
///
/// Uses the Cytron et al. algorithm:
///   1. CFG pre-processing (dead block elimination, jump threading, block merging)
///   2. Dominator tree computation (Cooper-Harvey-Kennedy iterative algorithm)
///   3. Dominance frontier computation
///   4. Phi insertion at iterated dominance frontiers
///   5. Variable renaming via dominator-tree preorder traversal
import Tree

// MARK: - Variable Renamer

public struct SSABuilder {

    public init() {}

    // MARK: - Public API

    /// Convert an entire program to SSA form.
    public func build(_ program: Program) -> Program {
        Program(
            functions: program.functions.map { build($0) },
            globals: program.globals
        )
    }

    /// Convert a single function to SSA form.
    public func build(_ function: Function) -> Function {
        guard !function.blocks.isEmpty else { return function }

        // Step 1: CFG pre-processing
        var f = eliminateDeadBlocks(in: function)
        f = threadJumps(in: f)
        f = mergeBlocks(in: f)

        // Step 2-5: SSA construction
        return constructSSA(f)
    }

    // MARK: - SSA Construction

    private func constructSSA(_ function: Function) -> Function {
        let blocks = function.blocks
        guard blocks.count > 1 else { return function }

        // ── Compute dominator tree (Cooper-Harvey-Kennedy) ───────────────
        let domTree = DominatorTree(function)
        let preds = domTree.preds
        let idom = domTree.idom
        let labelIndex = domTree.labelIndex

        // ── Compute dominance frontiers ──────────────────────────────────
        let df = domTree.dominanceFrontiers()

        // ── Identify SSA-eligible variables ──────────────────────────────
        let addressTaken = collectAddressTaken(in: blocks)

        // Collect source-level variables (positive ID) that are assigned.
        var varTypes: [Int: CType] = [:]
        var varNames: [Int: String] = [:]
        var defSites: [Int: Set<Int>] = [:]

        for (bi, block) in blocks.enumerated() {
            for instr in block.instructions {
                guard let dest = instr.dest else { continue }
                let id = dest.id
                // Exclude: negative IDs (TreeConverter temps), address-taken vars,
                // and aggregate types (struct/union) which live on the stack and
                // cannot be meaningfully phi-merged as register values.
                guard id > 0, !addressTaken.contains(id) else { continue }
                switch dest.type {
                case .structType, .unionType: continue
                default: break
                }
                varTypes[id] = dest.type
                varNames[id] = dest.name
                defSites[id, default: []].insert(bi)
            }
        }

        let eligibleVars = Set(defSites.keys)
        guard !eligibleVars.isEmpty else { return function }

        // ── Insert phi functions (iterated dominance frontier) ───────────
        // phiVarIds[bi] = ordered list of var IDs needing phis at block bi
        var phiVarIds: [Int: [Int]] = [:]

        for varId in eligibleVars.sorted() {
            guard let sites = defSites[varId],
                varTypes[varId] != nil
            else { continue }

            var worklist = Array(sites)
            var visited = sites
            var phiInserted: Set<Int> = []

            while let bi = worklist.popLast() {
                for frontier in df[bi] {
                    guard !phiInserted.contains(frontier) else { continue }
                    phiInserted.insert(frontier)
                    phiVarIds[frontier, default: []].append(varId)

                    if !visited.contains(frontier) {
                        visited.insert(frontier)
                        worklist.append(frontier)
                    }
                }
            }
        }

        // ── Rename variables (dominator-tree preorder walk) ──────────────
        var renamer = VariableRenamer(
            blocks: blocks,
            idom: idom,
            preds: preds,
            children: domTree.children,
            labelIndex: labelIndex,
            eligibleVars: eligibleVars,
            phiVarIds: phiVarIds,
            varTypes: varTypes,
            varNames: varNames,
            params: function.params
        )
        let (newBlocks, newLocals) = renamer.rename()

        return Function(
            name: function.name,
            returnType: function.returnType,
            params: function.params,
            locals: function.locals + newLocals,
            blocks: newBlocks,
            isStatic: function.isStatic,
            isInline: function.isInline
        )
    }

}
private struct VariableRenamer {
    let blocks: [Block]
    let idom: [Int]
    let preds: [[Int]]
    let labelIndex: [String: Int]
    let eligibleVars: Set<Int>
    /// phiVarIds[bi] = ordered list of original var IDs needing phis at block bi.
    let phiVarIds: [Int: [Int]]
    let varTypes: [Int: CType]
    let varNames: [Int: String]
    let params: [CVar]

    private var stacks: [Int: [Operand]] = [:]
    private var versionCounter: Int = 0
    private var synthLocals: [CVar] = []
    private var domChildren: [[Int]]
    private var newBlocks: [Block]

    init(
        blocks: [Block], idom: [Int], preds: [[Int]], children: [[Int]], labelIndex: [String: Int],
        eligibleVars: Set<Int>, phiVarIds: [Int: [Int]],
        varTypes: [Int: CType], varNames: [Int: String], params: [CVar]
    ) {
        self.blocks = blocks
        self.idom = idom
        self.preds = preds
        self.labelIndex = labelIndex
        self.eligibleVars = eligibleVars
        self.phiVarIds = phiVarIds
        self.varTypes = varTypes
        self.varNames = varNames
        self.params = params
        self.newBlocks = blocks
        self.domChildren = children

        // Initialize stacks — parameters provide the initial definition
        for p in params {
            guard case .local(let id) = p.storage, eligibleVars.contains(id) else { continue }
            stacks[id] = [.variable(name: p.name, id: id, type: p.type)]
        }
    }

    mutating func rename() -> ([Block], [CVar]) {
        // Build initial phi nodes with placeholder args
        for (bi, varIds) in phiVarIds {
            var phis: [Phi] = []
            let predLabels = preds[bi].map { blocks[$0].label }
            for varId in varIds {
                let type = varTypes[varId]!
                let name = varNames[varId] ?? "v"
                let place = Place(name: name, id: varId, type: type)
                let args = predLabels.map { label in
                    (label: label, value: Operand.intConst(0, type: type))
                }
                phis.append(Phi(dest: place, args: args))
            }
            newBlocks[bi] = Block(
                label: newBlocks[bi].label, phis: phis,
                instructions: newBlocks[bi].instructions,
                terminator: newBlocks[bi].terminator)
        }

        renameBlock(0)
        return (newBlocks, synthLocals)
    }

    private mutating func renameBlock(_ bi: Int) {
        var pushCounts: [Int: Int] = [:]

        // 1. Rename phi definitions
        if let varIds = phiVarIds[bi] {
            for (i, varId) in varIds.enumerated() {
                let versioned = freshVersion(varId: varId)
                pushCounts[varId, default: 0] += 1
                // Update phi dest to versioned place
                var phis = newBlocks[bi].phis
                phis[i] = Phi(dest: versioned, args: phis[i].args)
                newBlocks[bi] = Block(
                    label: newBlocks[bi].label, phis: phis,
                    instructions: newBlocks[bi].instructions,
                    terminator: newBlocks[bi].terminator)
            }
        }

        // 2. Process instructions: rename uses then defs
        let block = newBlocks[bi]
        var newInstrs: [Instr] = []
        for instr in block.instructions {
            var renamed = instr.remapOperands { renameUse($0) }
            if let dest = renamed.dest, eligibleVars.contains(dest.id) {
                let versioned = freshVersion(varId: dest.id)
                pushCounts[dest.id, default: 0] += 1
                renamed = replaceDest(renamed, with: versioned)
            }
            newInstrs.append(renamed)
        }

        // 3. Rename terminator uses
        let newTerm = block.terminator.remapOperands { renameUse($0) }
        newBlocks[bi] = Block(
            label: block.label, phis: newBlocks[bi].phis,
            instructions: newInstrs, terminator: newTerm)

        // 4. Fill phi args in successor blocks
        for succLabel in newTerm.successorLabels {
            guard let si = labelIndex[succLabel] else { continue }
            fillPhiArgs(predBlock: bi, succBlock: si)
        }

        // 5. Recurse into dominator tree children
        for child in domChildren[bi] {
            renameBlock(child)
        }

        // 6. Pop definitions pushed in this block
        for (varId, count) in pushCounts {
            stacks[varId]?.removeLast(count)
        }
    }

    private func renameUse(_ op: Operand) -> Operand {
        guard case .variable(_, let id, _) = op, eligibleVars.contains(id) else { return op }
        return stacks[id]?.last ?? op
    }

    private mutating func freshVersion(varId: Int) -> Place {
        versionCounter += 1
        let newId = -(versionCounter + 100_000)
        let type = varTypes[varId]!
        let name = "\(varNames[varId] ?? "v").\(versionCounter)"
        let place = Place(name: name, id: newId, type: type)
        stacks[varId, default: []].append(place.asOperand)
        synthLocals.append(CVar(name: name, type: type, storage: .local(id: newId)))
        return place
    }

    private mutating func fillPhiArgs(predBlock: Int, succBlock: Int) {
        guard let varIds = phiVarIds[succBlock] else { return }
        var phis = newBlocks[succBlock].phis
        let predLabel = blocks[predBlock].label

        for (i, varId) in varIds.enumerated() {
            let currentVal = stacks[varId]?.last ?? .intConst(0, type: phis[i].dest.type)
            for j in phis[i].args.indices where phis[i].args[j].label == predLabel {
                phis[i].args[j] = (label: predLabel, value: currentVal)
            }
        }

        newBlocks[succBlock] = Block(
            label: newBlocks[succBlock].label, phis: phis,
            instructions: newBlocks[succBlock].instructions,
            terminator: newBlocks[succBlock].terminator)
    }

    private func replaceDest(_ instr: Instr, with newDest: Place) -> Instr {
        switch instr {
        case .assign(_, let s): return .assign(dest: newDest, src: s)
        case .binary(_, let op, let l, let r): return .binary(dest: newDest, op: op, lhs: l, rhs: r)
        case .unary(_, let op, let s): return .unary(dest: newDest, op: op, src: s)
        case .call(_, let c, let args): return .call(dest: newDest, callee: c, args: args)
        case .addressOf(_, let s): return .addressOf(dest: newDest, src: s)
        case .load(_, let a): return .load(dest: newDest, addr: a)
        case .cast(_, let s, let t): return .cast(dest: newDest, src: s, to: t)
        case .cas(_, let a, let o, let n): return .cas(dest: newDest, addr: a, old: o, new: n)
        case .exchange(_, let a, let v): return .exchange(dest: newDest, addr: a, value: v)
        case .member(_, let b, let name, let off): return .member(dest: newDest, base: b, name: name, offset: off)
        case .store, .asm, .compare, .test: return instr
        }
    }
}
