/// A natural loop in the CFG.
public struct Loop {
    /// Block index of the loop header.
    public let header: Int
    /// All block indices in the loop body (including header).
    public let blocks: Set<Int>
    /// Block indices outside the loop that have a predecessor inside the loop.
    public let exitBlocks: Set<Int>
    /// Single predecessor of header that is outside the loop (if exists).
    public let preheader: Int?
}

/// Detects natural loops in a COIL function using back edges in the dominator tree.
public struct LoopInfo {
    /// All natural loops, sorted innermost first (smallest body).
    public let loops: [Loop]

    /// Build loop information from a function and its dominator tree.
    public init(_ function: Function, domTree: DominatorTree) {
        let n = function.blocks.count
        guard n > 0 else { self.loops = []; return }

        // ── Find back edges: (source, header) where header dominates source
        var backEdges: [(source: Int, header: Int)] = []
        for (i, block) in function.blocks.enumerated() {
            for succLabel in block.terminator.successorLabels {
                guard let j = domTree.labelIndex[succLabel] else { continue }
                if domTree.dominates(j, i) {
                    backEdges.append((source: i, header: j))
                }
            }
        }

        // ── Build natural loops from back edges
        // Group back edges by header and merge loops with the same header.
        var headerToSources: [Int: [Int]] = [:]
        for edge in backEdges {
            headerToSources[edge.header, default: []].append(edge.source)
        }

        var loops: [Loop] = []
        for (header, sources) in headerToSources {
            // Compute loop body: walk predecessors backward from each source until header.
            var body: Set<Int> = [header]
            var worklist: [Int] = []
            for src in sources {
                if body.insert(src).inserted {
                    worklist.append(src)
                }
            }
            while let b = worklist.popLast() {
                for pred in domTree.preds[b] {
                    if body.insert(pred).inserted {
                        worklist.append(pred)
                    }
                }
            }

            // Exit blocks: successors of loop blocks that are outside the loop.
            var exitBlocks: Set<Int> = []
            for b in body {
                for s in domTree.succs[b] where !body.contains(s) {
                    exitBlocks.insert(s)
                }
            }

            // Preheader: single predecessor of header that is outside the loop.
            let outsidePreds = domTree.preds[header].filter { !body.contains($0) }
            let preheader = outsidePreds.count == 1 ? outsidePreds[0] : nil

            loops.append(Loop(header: header, blocks: body,
                              exitBlocks: exitBlocks, preheader: preheader))
        }

        // Sort innermost first (smallest body).
        loops.sort { $0.blocks.count < $1.blocks.count }
        self.loops = loops
    }

    /// Returns the innermost loop containing `block`, or `nil` if none.
    public func loopFor(block: Int) -> Loop? {
        loops.first { $0.blocks.contains(block) }
    }
}
