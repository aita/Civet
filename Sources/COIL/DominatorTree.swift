/// Reusable dominator tree and related analyses for a COIL function.
///
/// Uses the Cooper-Harvey-Kennedy iterative algorithm (same as SSABuilder).
/// Provides dominance queries, dominance frontiers, and RPO ordering.
public struct DominatorTree: Sendable {
    /// Immediate dominator of each block (by index). `idom[0] == 0` (entry).
    public let idom: [Int]
    /// Reverse post-order number for each block index.
    public let rpo: [Int]
    /// Blocks listed in RPO order.
    public let rpoOrder: [Int]
    /// Dominator tree children for each block.
    public let children: [[Int]]
    /// CFG predecessors for each block (by index).
    public let preds: [[Int]]
    /// CFG successors for each block (by index).
    public let succs: [[Int]]
    /// Block label → block index.
    public let labelIndex: [String: Int]
    /// Block index → block label.
    public let labels: [String]

    /// Build the dominator tree for `function`.
    public init(_ function: Function) {
        let blocks = function.blocks
        let n = blocks.count
        let labels = blocks.map(\.label)
        let labelIndex = Dictionary(uniqueKeysWithValues: labels.enumerated().map { ($1, $0) })

        // ── Predecessors and successors ──────────────────────────────────
        var preds: [[Int]] = Array(repeating: [], count: n)
        var succs: [[Int]] = Array(repeating: [], count: n)
        for (i, block) in blocks.enumerated() {
            for succLabel in block.terminator.successorLabels {
                if let j = labelIndex[succLabel] {
                    preds[j].append(i)
                    succs[i].append(j)
                }
            }
        }

        // Handle computed gotos: add synthetic edges.
        var computedGotoBlocks: [Int] = []
        for (i, block) in blocks.enumerated() {
            if case .computedGoto = block.terminator {
                computedGotoBlocks.append(i)
            }
        }
        let labelAddrTargets: Set<Int> = Set(
            collectLabelAddrTargets(in: blocks).compactMap { labelIndex[$0] }
        )
        if !computedGotoBlocks.isEmpty {
            for target in labelAddrTargets {
                for src in computedGotoBlocks {
                    if !preds[target].contains(src) {
                        preds[target].append(src)
                    }
                    if !succs[src].contains(target) {
                        succs[src].append(target)
                    }
                }
            }
        }

        // ── RPO ─────────────────────────────────────────────────────────
        var rpoArr = Array(repeating: n, count: n)
        var visited = Array(repeating: false, count: n)
        var order: [Int] = []
        order.reserveCapacity(n)

        func dfs(_ node: Int) {
            visited[node] = true
            for si in succs[node] where !visited[si] {
                dfs(si)
            }
            order.append(node)
        }
        if n > 0 { dfs(0) }

        let rpoOrder = order.reversed().map { $0 }
        for (rpoNum, blockIdx) in rpoOrder.enumerated() {
            rpoArr[blockIdx] = rpoNum
        }

        // ── Dominator tree (Cooper-Harvey-Kennedy) ──────────────────────
        var idom = Array(repeating: -1, count: n)
        if n > 0 { idom[0] = 0 }

        func intersect(_ b1: Int, _ b2: Int) -> Int {
            var f1 = b1, f2 = b2
            while f1 != f2 {
                while rpoArr[f1] > rpoArr[f2] { f1 = idom[f1] }
                while rpoArr[f2] > rpoArr[f1] { f2 = idom[f2] }
            }
            return f1
        }

        var changed = true
        while changed {
            changed = false
            for b in rpoOrder where b != 0 {
                var newIdom = -1
                for p in preds[b] where idom[p] != -1 {
                    newIdom = p
                    break
                }
                guard newIdom != -1 else { continue }
                for p in preds[b] where p != newIdom && idom[p] != -1 {
                    newIdom = intersect(newIdom, p)
                }
                if idom[b] != newIdom {
                    idom[b] = newIdom
                    changed = true
                }
            }
        }

        // ── Dominator tree children ─────────────────────────────────────
        var children: [[Int]] = Array(repeating: [], count: n)
        for i in 0..<n where i != 0 && idom[i] >= 0 {
            children[idom[i]].append(i)
        }

        self.idom = idom
        self.rpo = rpoArr
        self.rpoOrder = rpoOrder
        self.children = children
        self.preds = preds
        self.succs = succs
        self.labelIndex = labelIndex
        self.labels = labels
    }

    /// Returns `true` if block `a` dominates block `b`.
    public func dominates(_ a: Int, _ b: Int) -> Bool {
        if a == b { return true }
        var runner = b
        while runner > 0 {
            runner = idom[runner]
            if runner < 0 { return false } // unreachable block
            if runner == a { return true }
        }
        return false
    }

    /// Compute dominance frontiers for all blocks.
    public func dominanceFrontiers() -> [[Int]] {
        let n = idom.count
        var df: [Set<Int>] = Array(repeating: [], count: n)
        for b in 0..<n {
            guard preds[b].count >= 2 else { continue }
            for p in preds[b] {
                var runner = p
                while runner >= 0 && runner != idom[b] {
                    df[runner].insert(b)
                    runner = idom[runner]
                }
            }
        }
        return df.map { Array($0) }
    }
}
