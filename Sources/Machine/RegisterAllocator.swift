import Foundation
import COIL
import Tree


// MARK: - Public API

/// Allocate physical registers for all functions in a machine program.
public func allocateRegisters(_ program: Program) -> Program {
    var result = program
    for i in result.functions.indices {
        result.functions[i] = allocateRegisters(result.functions[i])
    }
    return result
}

/// Allocate physical registers for a single machine function using linear scan.
public func allocateRegisters(_ function: Function) -> Function {
    var allocator = LinearScanAllocator(function: function)
    return allocator.allocate()
}

/// Fix illegal instructions that can arise after register allocation
/// (e.g., mem-to-mem moves from spilling).
/// Fix illegal x86-64 instructions (mem-to-mem, large immediates, etc.)
public func fixIllegalInstructions(_ program: Program) -> Program {
    var result = program
    for i in result.functions.indices {
        fixIllegalInstrs(&result.functions[i])
    }
    return result
}

private func fixIllegalInstrs(_ function: inout Function) {
    for bi in function.blocks.indices {
        var fixed: [Instr] = []
        for instr in function.blocks[bi].instructions {
            switch instr {
            // movq $large_imm, mem — imm must fit in sign-extended 32 bits
            case .movIM(.qword, let v, let mem)
                where v > Int64(Int32.max) || v < Int64(Int32.min):
                let scratch = scavengeGP(instr)
                fixed.append(.movIR(.qword, imm: v, dst: .physical(scratch)))
                fixed.append(.movRM(.qword, src: .physical(scratch), dst: mem))
                continue
            // movMM: mem→mem must go through scratch register
            case .movMM(let sz, let src, let dst):
                let scratch = scavengeGP(instr)
                fixed.append(.movMR(sz, src: src, dst: .physical(scratch)))
                fixed.append(.movRM(sz, src: .physical(scratch), dst: dst))
                continue
            // aluRmiR/cmpRmiR with .mem src are legal x86-64 instructions
            // (e.g. addl (%rax), %ecx) — no expansion needed.
            default:
                break
            }
            fixed.append(instr)
        }
        function.blocks[bi].instructions = fixed
    }
}

/// Scavenge a GP register not used by the given instruction.
private func scavengeGP(_ instr: Instr) -> PhysReg {
    let usedRegs = Set((defsOf(instr) + usesOf(instr)).compactMap { reg -> PhysReg? in
        if case .physical(let p) = reg { return p }
        return nil
    })
    // Also collect registers used in memory addressing modes
    var memBaseRegs = Set<PhysReg>()
    _ = instr.mapMemory { mem in
        if case .physical(let p) = mem.base { memBaseRegs.insert(p) }
        if case .physical(let p) = mem.index { memBaseRegs.insert(p) }
        return mem
    }
    let allUsed = usedRegs.union(memBaseRegs)
    if let scratch = PhysReg.allocatableGP.first(where: { !allUsed.contains($0) }) {
        return scratch
    }
    // Emergency: all registers in use — use push/pop around a borrowed register.
    // This shouldn't happen in practice (13 GP regs, instructions use at most ~4).
    return PhysReg.allocatableGP[0]
}

// MARK: - Live Interval

struct LiveInterval {
    let vreg: Int           // virtual register number
    var start: Int          // first instruction index (definition)
    var end: Int            // last instruction index (use)
    var reg: PhysReg?       // assigned physical register
    var spillSlot: Int32?   // stack offset if spilled
    var isFloat: Bool       // needs XMM register
    var spansCall: Bool     // true if interval crosses a call instruction
    var loopDepth: Int = 0  // maximum loop nesting depth of the interval
    var rematInstr: Instr?  // defining instruction if rematerializable (cheap to recompute)

    /// Spill weight: higher weight = harder/more costly to spill.
    /// Intervals inside loops are 10x more expensive to spill per depth level.
    var spillWeight: Double {
        let length = max(1, end - start)
        return Double(length) * pow(10.0, Double(loopDepth))
    }
}

// MARK: - Linear Scan Allocator

struct LinearScanAllocator {
    var function: Function

    // Scratch registers reserved for spill code (not allocatable).
    // gpScratch2 is needed when one instruction has two spilled uses
    // (e.g. add V11, V14 where both are spilled — two-address conflict).
    static let gpScratch:  PhysReg = .r11
    static let gpScratch2: PhysReg = .r10
    static let sseScratch: PhysReg = .xmm15

    mutating func allocate() -> Function {
        // 1. Number instructions linearly across all blocks
        let totalInstrs = function.blocks.reduce(0) { $0 + $1.instructions.count }
        guard totalInstrs > 0 else { return function }

        // Build a flat instruction position map: (blockIndex, instrIndex) for each linear position
        var posMap: [(blockIdx: Int, instrIdx: Int)] = []
        posMap.reserveCapacity(totalInstrs)
        for (bi, block) in function.blocks.enumerated() {
            for ii in block.instructions.indices {
                posMap.append((bi, ii))
            }
        }

        // 2. Build fixed intervals from regConstraint and explicit physical reg usage
        var fixedIntervals: [PhysReg: [(start: Int, end: Int)]] = [:]
        var callPositions: Set<Int> = []

        for (pos, loc) in posMap.enumerated() {
            let instr = function.blocks[loc.blockIdx].instructions[loc.instrIdx]
            if case .call = instr { callPositions.insert(pos) }

            // Record fixed intervals from regConstraint metadata.
            // Call clobbers are excluded — they are handled by the spansCall
            // mechanism instead, because System V ABI has no callee-saved XMM
            // registers and blocking all XMM at call sites would make float
            // allocation impossible.
            let rc = regConstraint(for: instr)
            for phys in rc.inputs {
                fixedIntervals[phys, default: []].append((pos, pos))
            }
            for phys in rc.outputs {
                fixedIntervals[phys, default: []].append((pos, pos))
            }
            // Clobbers from non-call instructions (there are currently none,
            // but this is future-proof)
            if case .call = instr {} else {
                for phys in rc.clobbers {
                    fixedIntervals[phys, default: []].append((pos, pos))
                }
            }

            // Also record explicit physical register operands
            for reg in defsOf(instr) + usesOf(instr) {
                if case .physical(let p) = reg {
                    fixedIntervals[p, default: []].append((pos, pos))
                }
            }
        }

        // 3. Compute live intervals for each virtual register
        var intervals: [Int: LiveInterval] = [:]  // vreg -> interval
        var vregDefPositions: [Int: [Int]] = [:]   // vreg -> list of definition positions

        // MachPhi destinations are defined at block entry (before any instruction).
        // Seed their intervals using blockStartPos (best approximation before posMap is built).
        // We use the first instruction position of each block as a proxy for block-start.
        var blockFirstPos: [Int: Int] = [:]  // blockIdx -> first pos (or 0 if empty)
        var blockLastPos:  [Int: Int] = [:]  // blockIdx -> last pos
        for (pos, loc) in posMap.enumerated() {
            if blockFirstPos[loc.blockIdx] == nil { blockFirstPos[loc.blockIdx] = pos }
            blockLastPos[loc.blockIdx] = pos
        }
        for (bi, block) in function.blocks.enumerated() {
            let bStart = blockFirstPos[bi] ?? 0
            for phi in block.phis {
                if case .virtual(let v) = phi.dest {
                    let isFloatPhi = phi.size == .single || phi.size == .double_
                    vregDefPositions[v, default: []].append(bStart)
                    if intervals[v] == nil {
                        intervals[v] = LiveInterval(vreg: v, start: bStart, end: bStart,
                                                     reg: nil, spillSlot: nil,
                                                     isFloat: isFloatPhi, spansCall: false)
                    } else {
                        // Already defined elsewhere (shouldn't happen in SSA, but be safe)
                        intervals[v]!.end = max(intervals[v]!.end, bStart)
                    }
                }
            }
        }

        for (pos, loc) in posMap.enumerated() {
            let instr = function.blocks[loc.blockIdx].instructions[loc.instrIdx]

            // Process definitions
            for reg in defsOf(instr) {
                if case .virtual(let v) = reg {
                    vregDefPositions[v, default: []].append(pos)
                    if intervals[v] == nil {
                        let isFloat = isFloatDef(instr)
                        intervals[v] = LiveInterval(vreg: v, start: pos, end: pos,
                                                     reg: nil, spillSlot: nil,
                                                     isFloat: isFloat, spansCall: false)
                    } else {
                        intervals[v]!.end = pos
                    }
                }
            }

            // Process uses
            for reg in usesOf(instr) {
                if case .virtual(let v) = reg {
                    if intervals[v] != nil {
                        intervals[v]!.end = pos
                    } else {
                        // Use before def (can happen with parameters)
                        intervals[v] = LiveInterval(vreg: v, start: 0, end: pos,
                                                     reg: nil, spillSlot: nil,
                                                     isFloat: false, spansCall: false)
                    }
                }
            }
        }

        // 3a. Tag rematerializable definitions.
        // A rematerializable instruction is cheap to recompute (mov $imm, lea global)
        // and uses no virtual registers, so it can replace a stack reload.
        for (_, loc) in posMap.enumerated() {
            let instr = function.blocks[loc.blockIdx].instructions[loc.instrIdx]
            if let v = rematCandidate(instr) {
                intervals[v]?.rematInstr = instr
            }
        }

        // 3b. Extend live intervals using phi-aware CFG liveness analysis.
        // This handles both loop back-edges and phi arg variables.
        extendIntervalsWithCFGLiveness(&intervals, posMap: posMap)

        // 3c. Annotate intervals with loop depth (for spill weight in eviction).
        let blockDepths = computeBlockLoopDepths()
        let loopBlocks = blockDepths.enumerated().filter { $0.element > 0 }
        for v in intervals.keys {
            var maxDepth = 0
            let iv = intervals[v]!
            for (bi, d) in loopBlocks {
                let bStart = blockFirstPos[bi] ?? 0
                let bEnd = blockLastPos[bi] ?? 0
                if iv.start <= bEnd && iv.end >= bStart {
                    maxDepth = max(maxDepth, d)
                }
            }
            if maxDepth > 0 { intervals[v]!.loopDepth = maxDepth }
        }

        // 4. Mark intervals that span calls (binary search per interval)
        let sortedCalls = callPositions.sorted()
        for v in intervals.keys {
            let iv = intervals[v]!
            // Binary search for first call position > iv.start
            var lo = 0, hi = sortedCalls.count
            while lo < hi {
                let mid = (lo + hi) / 2
                if sortedCalls[mid] <= iv.start { lo = mid + 1 } else { hi = mid }
            }
            if lo < sortedCalls.count && sortedCalls[lo] < iv.end {
                intervals[v]!.spansCall = true
            }
        }


        // 4b. Phi coalescing + copy coalescing: merge non-interfering interval pairs
        // so they share the same physical register, turning copies into noops.
        var coalescingUF = coalescePhis(intervals, blockLastPos: blockLastPos)
        coalesceCopies(intervals, uf: &coalescingUF)
        let originalVregs = Set(intervals.keys)
        mergeCoalescedIntervals(&intervals, uf: &coalescingUF)

        // 4c. Build copy-hint map: vreg → related vreg (from movRR/xmmMovRR)
        // After coalescing, some copies remain. Hints allow pickReg to prefer the
        // physical register already assigned to the copy partner.
        var copyHintSource: [Int: Int] = [:]
        for block in function.blocks {
            for instr in block.instructions {
                switch instr {
                case .movRR(_, let src, let dst), .xmmMovRR(_, let src, let dst):
                    if case .virtual(let sv) = src, case .virtual(let dv) = dst {
                        let rs = coalescingUF.find(sv), rd = coalescingUF.find(dv)
                        if rs != rd && intervals[rs] != nil && intervals[rd] != nil {
                            copyHintSource[rs] = rd
                            copyHintSource[rd] = rs
                        }
                    }
                default: break
                }
            }
        }

        // 5. Sort intervals by start position (break ties by vreg number for determinism)
        var sorted = Array(intervals.values).sorted {
            $0.start != $1.start ? $0.start < $1.start : $0.vreg < $1.vreg
        }

        // 6. Linear scan allocation with unhandled stack (supports live range splitting).
        // unhandled stores indices into sorted in descending start order; popLast = min start.
        var unhandled: [Int] = Array(sorted.indices.reversed())
        var active: [Int] = []  // indices into sorted, sorted by end
        var freeGP = PhysReg.allocatableGP.sorted { $0.rawValue < $1.rawValue }
        if !function.usesFramePointer {
            // RBP is callee-saved and usable as a general register when frame pointer is omitted.
            let idx = freeGP.firstIndex { $0.rawValue >= PhysReg.rbp.rawValue } ?? freeGP.endIndex
            freeGP.insert(.rbp, at: idx)
        }
        var freeSSE = PhysReg.allSSE.sorted { $0.rawValue < $1.rawValue }

        var spillOffset = function.stackSize
        var usedCalleeSaved: Set<PhysReg> = []
        var vregAssignment: [Int: PhysReg] = [:]  // vreg → assigned physical register (for hints)
        var sharedSpillSlots: Set<Int32> = []  // spill slots used for split boundaries

        while let i = unhandled.popLast() {
            let current = sorted[i]

            // Expire old intervals
            active = active.filter { j in
                if sorted[j].end < current.start {
                    // Return register to free pool (maintain sorted order)
                    if let r = sorted[j].reg {
                        if sorted[j].isFloat {
                            let idx = freeSSE.firstIndex { $0.rawValue >= r.rawValue } ?? freeSSE.endIndex
                            freeSSE.insert(r, at: idx)
                        } else {
                            let idx = freeGP.firstIndex { $0.rawValue >= r.rawValue } ?? freeGP.endIndex
                            freeGP.insert(r, at: idx)
                        }
                    }
                    return false
                }
                return true
            }

            // Compute register hint from copy-related vregs
            let hint = copyHintSource[current.vreg].flatMap { vregAssignment[$0] }

            // Try to allocate (spansCall float now goes through pickReg→nil→splitOrSpill
            // instead of force-spill, enabling split at call boundary)
            if current.isFloat {
                if let reg = pickReg(from: &freeSSE, spansCall: current.spansCall,
                                     isFloat: true,
                                     interval: current, fixedIntervals: fixedIntervals,
                                     hint: hint) {
                    sorted[i].reg = reg
                    vregAssignment[current.vreg] = reg
                    let insertPos = active.firstIndex { sorted[$0].end >= sorted[i].end } ?? active.endIndex
                    active.insert(i, at: insertPos)
                } else {
                    splitOrSpill(&sorted, index: i, active: &active,
                                 freeGP: &freeGP, freeSSE: &freeSSE,
                                 spillOffset: &spillOffset, unhandled: &unhandled,
                                 sharedSpillSlots: &sharedSpillSlots,
                                 sortedCalls: sortedCalls,
                                 fixedIntervals: fixedIntervals,
                                 usedCalleeSaved: &usedCalleeSaved,
                                 vregAssignment: &vregAssignment,
                                 copyHintSource: copyHintSource)
                }
            } else {
                if let reg = pickReg(from: &freeGP, spansCall: current.spansCall,
                                     isFloat: false,
                                     interval: current, fixedIntervals: fixedIntervals,
                                     hint: hint) {
                    sorted[i].reg = reg
                    vregAssignment[current.vreg] = reg
                    if PhysReg.calleeSavedGP.contains(reg) || reg == .rbp { usedCalleeSaved.insert(reg) }
                    let insertPos = active.firstIndex { sorted[$0].end >= sorted[i].end } ?? active.endIndex
                    active.insert(i, at: insertPos)
                } else {
                    splitOrSpill(&sorted, index: i, active: &active,
                                 freeGP: &freeGP, freeSSE: &freeSSE,
                                 spillOffset: &spillOffset, unhandled: &unhandled,
                                 sharedSpillSlots: &sharedSpillSlots,
                                 sortedCalls: sortedCalls,
                                 fixedIntervals: fixedIntervals,
                                 usedCalleeSaved: &usedCalleeSaved,
                                 vregAssignment: &vregAssignment,
                                 copyHintSource: copyHintSource)
                }
            }
        }

        // 6b. Stack slot coloring — reuse slots whose live intervals don't overlap.
        // Exclude shared spill slots from coloring (split sub-intervals must share the same slot).
        let baseStackSize = function.stackSize
        let spilledIndices = sorted.indices.filter {
            sorted[$0].spillSlot != nil && !sharedSpillSlots.contains(sorted[$0].spillSlot!)
        }.sorted { sorted[$0].start < sorted[$1].start }
        if !spilledIndices.isEmpty {
            var availableSlots: [(offset: Int32, freeAfter: Int)] = []
            var nextOffset = baseStackSize
            for idx in spilledIndices {
                let iv = sorted[idx]
                // Find a reusable slot (freed before this interval starts)
                if let slotIdx = availableSlots.firstIndex(where: { $0.freeAfter < iv.start }) {
                    sorted[idx].spillSlot = availableSlots[slotIdx].offset
                    availableSlots[slotIdx].freeAfter = iv.end
                } else {
                    nextOffset += 8
                    sorted[idx].spillSlot = nextOffset
                    availableSlots.append((offset: nextOffset, freeAfter: iv.end))
                }
            }
            spillOffset = nextOffset  // update spillOffset to reflect colored slots
        }


        // 6c. Second-Chance Allocation: try to assign registers to spilled intervals
        // that fit entirely within a free range (no overlap with any active assignment).
        // Prioritize by spill weight (loop-heavy intervals benefit most from re-allocation).
        let spilledByWeight = sorted.indices
            .filter { sorted[$0].reg == nil && sorted[$0].spillSlot != nil
                      && !sharedSpillSlots.contains(sorted[$0].spillSlot!) }
            .sorted { sorted[$0].spillWeight > sorted[$1].spillWeight }

        for idx in spilledByWeight {
            let iv = sorted[idx]

            // Find physical registers that are free for the entire [start, end] range.
            // A register is free if no other assigned interval overlaps this range.
            var occupiedRegs = Set<PhysReg>()
            for other in sorted where other.reg != nil {
                if other.start <= iv.end && other.end >= iv.start {
                    occupiedRegs.insert(other.reg!)
                }
            }
            // Also check fixed intervals
            for (preg, ranges) in fixedIntervals {
                for r in ranges {
                    if r.start <= iv.end && r.end >= iv.start {
                        occupiedRegs.insert(preg)
                        break
                    }
                }
            }

            // Choose a free register respecting spansCall constraint
            let candidates: [PhysReg]
            if iv.spansCall {
                if iv.isFloat { continue }  // SSE + spansCall → stay spilled
                var cs = PhysReg.calleeSavedGP.filter { !occupiedRegs.contains($0) }
                if !function.usesFramePointer && !occupiedRegs.contains(.rbp) { cs.append(.rbp) }
                candidates = cs
            } else if iv.isFloat {
                candidates = PhysReg.allSSE.filter { !occupiedRegs.contains($0) }
            } else {
                var alloc = PhysReg.allocatableGP.filter { !occupiedRegs.contains($0) }
                if !function.usesFramePointer && !occupiedRegs.contains(.rbp) { alloc.append(.rbp) }
                candidates = alloc
            }

            // Try hint first, then any candidate
            let scHint = copyHintSource[iv.vreg].flatMap { vregAssignment[$0] }
            if let h = scHint, candidates.contains(h) {
                sorted[idx].reg = h
            } else if let reg = candidates.first {
                sorted[idx].reg = reg
            }

            if sorted[idx].reg != nil {
                // Don't clear spillSlot for shared split slots (needed for boundary copies)
                if !sharedSpillSlots.contains(sorted[idx].spillSlot ?? 0) {
                    sorted[idx].spillSlot = nil
                }
                if !iv.isFloat, let r = sorted[idx].reg,
                   PhysReg.calleeSavedGP.contains(r) || r == .rbp {
                    usedCalleeSaved.insert(r)
                }
                vregAssignment[iv.vreg] = sorted[idx].reg
            }
        }

        // 7. Build vreg → assignment map (position-aware for split vregs).
        // Detect split vregs: same vreg with multiple intervals in sorted.
        var vregCount: [Int: Int] = [:]
        for iv in sorted { vregCount[iv.vreg, default: 0] += 1 }
        var splitVregs = Set(vregCount.filter { $0.value > 1 }.map { $0.key })

        // Non-split vregs: simple assignMap/spillMap
        var assignMap: [Int: PhysReg] = [:]
        var spillMap: [Int: Int32] = [:]
        var rematMap: [Int: Instr] = [:]
        for iv in sorted where !splitVregs.contains(iv.vreg) {
            if let r = iv.reg {
                assignMap[iv.vreg] = r
            }
            if let s = iv.spillSlot, iv.reg == nil {
                spillMap[iv.vreg] = s
                if let ri = iv.rematInstr { rematMap[iv.vreg] = ri }
            }
        }

        // Split vregs: position-aware range lookup.
        // Each sub-interval keeps its allocated register (if any).
        // Boundary stores save first half's reg to shared slot before split point.
        // Boundary loads restore from shared slot into second half's reg after split point.
        var splitRanges: [Int: [(start: Int, end: Int, reg: PhysReg?, spillSlot: Int32?)]] = [:]
        var secondHalfStarts: Set<Int> = []  // sorted indices that are second+ halves
        var splitGroups: [Int: [(sortedIdx: Int, iv: LiveInterval)]] = [:]
        for (idx, iv) in sorted.enumerated() where splitVregs.contains(iv.vreg) {
            splitGroups[iv.vreg, default: []].append((sortedIdx: idx, iv: iv))
        }
        for (vreg, group) in splitGroups {
            let sortedGroup = group.sorted { $0.iv.start < $1.iv.start }
            for (idx, entry) in sortedGroup.enumerated() {
                let iv = entry.iv
                if idx == 0 {
                    // First sub-interval: use register if available
                    splitRanges[vreg, default: []].append(
                        (start: iv.start, end: iv.end,
                         reg: iv.reg,
                         spillSlot: iv.reg != nil ? nil : iv.spillSlot))
                } else {
                    // Subsequent sub-intervals: keep allocated register only if:
                    // 1. The boundary position is a call position (boundary load goes
                    //    after the call, safe from argument register conflicts).
                    // 2. No redefinitions of the vreg within the second half's range
                    //    (boundary load captures value once; redefs would make it stale).
                    let bpos = iv.start
                    let hasRedefInRange = (vregDefPositions[vreg] ?? []).contains {
                        $0 > bpos && $0 <= iv.end
                    }
                    let canUseReg = iv.reg != nil && callPositions.contains(bpos)
                                    && !hasRedefInRange
                    splitRanges[vreg, default: []].append(
                        (start: iv.start, end: iv.end,
                         reg: canUseReg ? iv.reg : nil,
                         spillSlot: iv.spillSlot))
                    if canUseReg { secondHalfStarts.insert(entry.sortedIdx) }
                }
            }
        }

        // 7b. Propagate coalesced allocations to all member vregs.
        for v in originalVregs {
            let rep = coalescingUF.find(v)
            guard rep != v else { continue }
            if splitVregs.contains(rep) {
                splitVregs.insert(v)
                splitRanges[v] = splitRanges[rep]
            } else {
                if let r = assignMap[rep] { assignMap[v] = r }
                if let s = spillMap[rep]  { spillMap[v] = s }
                if let ri = rematMap[rep] { rematMap[v] = ri }
            }
        }

        // 7c. Build float vreg set for O(1) lookup during rewrite.
        let floatVregs = Set(sorted.filter { $0.isFloat }.map { $0.vreg })

        // 7d. Precompute per-position occupied physical registers for scratch scavenging.
        // This allows the rewrite phase to dynamically find free registers instead of
        // reserving dedicated scratch registers (r10, r11, xmm15).
        var liveRegsAt = Array(repeating: Set<PhysReg>(), count: posMap.count)
        for (sivIdx, iv) in sorted.enumerated() where iv.reg != nil {
            // Second-half split intervals: register isn't live at start (boundary load
            // happens after the instruction at start), so begin from start+1.
            let lo = max(0, secondHalfStarts.contains(sivIdx) ? iv.start + 1 : iv.start)
            let hi = min(posMap.count - 1, iv.end)
            if lo <= hi {
                for pos in lo...hi {
                    liveRegsAt[pos].insert(iv.reg!)
                }
            }
        }
        // Also include fixed intervals (explicit physical register uses at specific positions).
        for (preg, ranges) in fixedIntervals {
            for (start, end) in ranges {
                let lo = max(0, start)
                let hi = min(posMap.count - 1, end)
                if lo <= hi {
                    for pos in lo...hi {
                        liveRegsAt[pos].insert(preg)
                    }
                }
            }
        }

        // Build (blockIdx, instrIdx) → position map for the rewrite phase.
        var instrToPos: [[Int]] = function.blocks.map { Array(repeating: -1, count: $0.instructions.count) }
        for (pos, loc) in posMap.enumerated() {
            instrToPos[loc.blockIdx][loc.instrIdx] = pos
        }

        // 7e. Block start/end positions for phi rewrite.
        var blockStartPos2: [Int] = function.blocks.map { _ in 0 }
        var blockEndPos2: [Int] = function.blocks.map { _ in 0 }
        for bi in function.blocks.indices {
            if !instrToPos[bi].isEmpty {
                blockStartPos2[bi] = instrToPos[bi].first ?? 0
                blockEndPos2[bi] = instrToPos[bi].last ?? 0
            }
        }
        let labelToBlockIdx = Dictionary(uniqueKeysWithValues:
            function.blocks.enumerated().map { ($1.label, $0) })

        // 7f. Boundary copies at split points.
        // Store: first half reg → shared slot (BEFORE instruction at bpos).
        // Load:  shared slot → second half reg (AFTER instruction at bpos).
        var boundaryCopiesBeforePos: [Int: [Instr]] = [:]
        var boundaryCopiesAfterPos: [Int: [Instr]] = [:]
        for (vreg, ranges) in splitRanges {
            let isFloat = floatVregs.contains(vreg)
            for j in 0..<(ranges.count - 1) {
                let first = ranges[j], second = ranges[j + 1]
                // Find shared slot from either half
                let slot: Int32
                if let s = second.spillSlot { slot = s }
                else if let s = first.spillSlot { slot = s }
                else if let s = sorted.first(where: { $0.vreg == vreg && $0.spillSlot != nil })?.spillSlot { slot = s }
                else { continue }

                let bpos = second.start

                // Store first half's register to shared slot (before bpos)
                if let r1 = first.reg {
                    if isFloat {
                        boundaryCopiesBeforePos[bpos, default: []].append(
                            .xmmMovRM(.double_, src: .physical(r1), dst: .stack(slot)))
                    } else {
                        boundaryCopiesBeforePos[bpos, default: []].append(
                            .movRM(.qword, src: .physical(r1), dst: .stack(slot)))
                    }
                }

                // Load shared slot into second half's register (after bpos).
                // Only emit boundary load when bpos is a call position — this
                // ensures the load goes after the call instruction, avoiding
                // clobbering argument registers during call setup.
                // For non-call split points, the second half uses spillSlot normally.
                if let r2 = second.reg, callPositions.contains(bpos) {
                    if isFloat {
                        boundaryCopiesAfterPos[bpos, default: []].append(
                            .xmmMovMR(.double_, src: .stack(slot), dst: .physical(r2)))
                    } else {
                        boundaryCopiesAfterPos[bpos, default: []].append(
                            .movMR(.qword, src: .stack(slot), dst: .physical(r2)))
                    }
                }
            }
        }

        // Helper: look up the assignment for a split vreg at a given position.
        // At the exact start of a second+ half with a register, the boundary load
        // hasn't executed yet, so return spillSlot instead of reg.
        func splitLookup(_ vreg: Int, at pos: Int) -> (reg: PhysReg?, spillSlot: Int32?) {
            guard let ranges = splitRanges[vreg] else { return (nil, nil) }
            for (idx, r) in ranges.enumerated() {
                if r.start <= pos && pos <= r.end {
                    // At exact start of second+ half with reg: boundary load is after
                    // this instruction, so use spillSlot for reload at this position.
                    if idx > 0 && pos == r.start && r.reg != nil {
                        return (nil, r.spillSlot)
                    }
                    return (r.reg, r.spillSlot)
                }
            }
            // Fallback: nearest range
            if let last = ranges.last(where: { $0.end < pos }) { return (last.reg, last.spillSlot) }
            if let first = ranges.first { return (first.reg, first.spillSlot) }
            return (nil, nil)
        }

        // Helper: resolve a vreg to its effective assignment at a position.
        func effectiveAssignment(_ v: Int, at pos: Int) -> (reg: PhysReg?, spillSlot: Int32?) {
            if splitVregs.contains(v) {
                return splitLookup(v, at: pos)
            }
            return (assignMap[v], spillMap[v])
        }

        // 8. Rewrite instructions
        for bi in function.blocks.indices {
            var newInstrs: [Instr] = []
            for (instrIdx, instr) in function.blocks[bi].instructions.enumerated() {
                let pos = instrIdx < instrToPos[bi].count ? instrToPos[bi][instrIdx] : -1

                // Insert split boundary store copies before this instruction
                if pos >= 0, let copies = boundaryCopiesBeforePos[pos] {
                    newInstrs.append(contentsOf: copies)
                }

                // Special handling for pcopy: spilled vregs are replaced with their
                // spill slot memory operands directly, avoiding scratch register conflicts
                // when multiple float vregs are spilled in the same pcopy.
                if case .pcopy(let copies) = instr {
                    let rewrittenCopies = copies.map { copy -> (src: Operand, dst: Operand, sz: Size) in
                        var src = copy.src
                        var dst = copy.dst
                        if case .reg(.virtual(let v)) = src {
                            let (r, s) = effectiveAssignment(v, at: pos)
                            if r == nil, let slot = s {
                                src = .mem(.stack(slot))
                            } else if let phys = r {
                                src = .reg(.physical(phys))
                            }
                        }
                        if case .reg(.virtual(let v)) = dst {
                            let (r, s) = effectiveAssignment(v, at: pos)
                            if r == nil, let slot = s {
                                dst = .mem(.stack(slot))
                            } else if let phys = r {
                                dst = .reg(.physical(phys))
                            }
                        }
                        return (src: src, dst: dst, sz: copy.sz)
                    }
                    newInstrs.append(.pcopy(rewrittenCopies))
                    continue
                }

                // Scavenge scratch registers: find physical registers not live at this position.
                let occupied = pos >= 0 ? liveRegsAt[pos] : Set<PhysReg>()
                var freeGPScavenge = PhysReg.allocatableGP.filter { !occupied.contains($0) }
                var freeSSEScavenge = PhysReg.allSSE.filter { !occupied.contains($0) }

                // Build per-position override maps for split vregs used/defined in this instruction.
                var posAssignOverride: [Int: PhysReg] = [:]
                var posSpillOverride: [Int: Int32] = [:]
                if !splitVregs.isEmpty && pos >= 0 {
                    for reg in usesOf(instr) + defsOf(instr) {
                        if case .virtual(let v) = reg, splitVregs.contains(v) {
                            let (r, s) = splitLookup(v, at: pos)
                            if let r = r { posAssignOverride[v] = r }
                            if let s = s { posSpillOverride[v] = s }
                            // debug: split vreg with no assignment at this position
                        }
                    }
                }

                // Insert reloads for used spilled vregs.
                let used = usesOf(instr)
                var reloadMap: [Int: PhysReg] = [:]
                for reg in used {
                    if case .virtual(let v) = reg, reloadMap[v] == nil {
                        // Determine effective spill slot (split-aware)
                        let slot: Int32?
                        if let s = posSpillOverride[v] { slot = s }
                        else if posAssignOverride[v] != nil { slot = nil } // has register
                        else { slot = spillMap[v] }

                        guard let effectiveSlot = slot else { continue }

                        let scratch: PhysReg
                        if isFloatVreg(v, floatVregs) {
                            guard let s = freeSSEScavenge.popLast() else {
                                fatalError("No free SSE register for spill reload at pos \(pos)")
                            }
                            scratch = s
                        } else {
                            guard let s = freeGPScavenge.popLast() else {
                                fatalError("No free GP register for spill reload at pos \(pos)")
                            }
                            scratch = s
                        }
                        // Rematerialization: recompute cheap values instead of loading from stack
                        if let ri = rematMap[v] {
                            newInstrs.append(emitRemat(ri, scratch: scratch))
                        } else if isFloatVreg(v, floatVregs) {
                            newInstrs.append(.xmmMovMR(.double_, src: .stack(effectiveSlot),
                                                       dst: .physical(scratch)))
                        } else {
                            newInstrs.append(.movMR(.qword, src: .stack(effectiveSlot),
                                                   dst: .physical(scratch)))
                        }
                        reloadMap[v] = scratch
                    }
                }

                // Build def rewrite map: spilled defs go through scavenged scratch register.
                let defined = defsOf(instr)
                for reg in defined {
                    if case .virtual(let v) = reg, reloadMap[v] == nil {
                        let isSpilled: Bool
                        if let _ = posSpillOverride[v] { isSpilled = true }
                        else if posAssignOverride[v] != nil { isSpilled = false }
                        else { isSpilled = spillMap[v] != nil }

                        guard isSpilled else { continue }
                        if isFloatVreg(v, floatVregs) {
                            guard let s = freeSSEScavenge.popLast() else {
                                fatalError("No free SSE register for spill def at pos \(pos)")
                            }
                            reloadMap[v] = s
                        } else {
                            guard let s = freeGPScavenge.popLast() else {
                                fatalError("No free GP register for spill def at pos \(pos)")
                            }
                            reloadMap[v] = s
                        }
                    }
                }

                // Merge position overrides into assignMap for rewriteInstr
                var effectiveAssignMap = assignMap
                for (v, r) in posAssignOverride { effectiveAssignMap[v] = r }

                // Rewrite the instruction (both uses and defs through scratch)
                let rewritten = rewriteInstr(instr, assignMap: effectiveAssignMap, reloadMap: reloadMap)
                // Eliminate redundant copies (same src == dst after coalescing)
                if !isRedundantCopy(rewritten) {
                    newInstrs.append(rewritten)
                }

                // Insert stores for defined spilled vregs using the scratch assigned above.
                for reg in defined {
                    if case .virtual(let v) = reg, rematMap[v] == nil {
                        let effectiveSlot: Int32?
                        if let s = posSpillOverride[v] { effectiveSlot = s }
                        else if posAssignOverride[v] != nil { effectiveSlot = nil }
                        else { effectiveSlot = spillMap[v] }

                        if let slot = effectiveSlot, let scratch = reloadMap[v] {
                            if isFloatVreg(v, floatVregs) {
                                newInstrs.append(.xmmMovRM(.double_, src: .physical(scratch),
                                                           dst: .stack(slot)))
                            } else {
                                newInstrs.append(.movRM(.qword, src: .physical(scratch),
                                                       dst: .stack(slot)))
                            }
                        }
                    }
                }

                // Insert split boundary load copies after this instruction.
                // These load the shared spill slot into the second half's register.
                if pos >= 0, let copies = boundaryCopiesAfterPos[pos] {
                    newInstrs.append(contentsOf: copies)
                }
            }
            function.blocks[bi].instructions = newInstrs
        }

        // 8b. Rewrite Machine phi nodes (dest + arg srcs → physical regs or spill slots).
        // Split vregs need position-aware lookup (phi dest → block start, phi arg → pred end).
        for bi in function.blocks.indices {
            let destPos = blockStartPos2[bi]
            for pi in function.blocks[bi].phis.indices {
                if case .virtual(let v) = function.blocks[bi].phis[pi].dest {
                    let (r, s) = effectiveAssignment(v, at: destPos)
                    if let phys = r {
                        function.blocks[bi].phis[pi].dest = .physical(phys)
                    } else if let slot = s {
                        // Make this spill slot visible to eliminateMachinePhis
                        spillMap[v] = slot
                    }
                }
                function.blocks[bi].phis[pi].args = function.blocks[bi].phis[pi].args.map { arg in
                    var src = arg.src
                    if case .reg(.virtual(let v)) = src {
                        let predPos: Int
                        if let pbi = labelToBlockIdx[arg.label] {
                            predPos = blockEndPos2[pbi]
                        } else {
                            predPos = 0
                        }
                        let (r, s) = effectiveAssignment(v, at: predPos)
                        if let phys = r {
                            src = .reg(.physical(phys))
                        } else if let slot = s {
                            src = .mem(.stack(slot))
                        }
                    }
                    return (label: arg.label, src: src)
                }
            }
        }

        // 9a. Phi elimination: convert Machine phi nodes to parallel copies in predecessors.
        // Must run BEFORE adjustStackOffsets so inserted instructions get the csShift applied.
        eliminateMachinePhis(&function, spillMap: spillMap)

        // 9b. Expand prologue/epilogue
        let calleeSaved = Array(usedCalleeSaved).sorted { $0.rawValue < $1.rawValue }
        function.calleeSaved = calleeSaved

        let useFP = function.usesFramePointer

        // Callee-saved pushes occupy space between rbp and the local frame.
        // Adjust all stack-relative (rbp-based) memory operands to account for this.
        let csShift = Int32(calleeSaved.count * 8)
        if useFP {
            if csShift > 0 {
                adjustStackOffsets(&function, by: csShift)
            }
        }

        // Adjust stack size: original + spill area + callee-saved area, aligned to 16
        let totalStack = spillOffset + csShift
        // Account for return address + rbp push (if FP used) + callee-saved pushes.
        let pushCount = calleeSaved.count + (useFP ? 2 : 1)  // +1 for return addr, +1 for rbp if FP
        let frameAdjust = totalStack
        let totalPushed = Int32(pushCount * 8)
        let aligned = alignUp(frameAdjust, to: 16, considering: totalPushed)
        function.stackSize = aligned

        // Red zone: leaf functions with ≤128 bytes of stack can skip sub/add rsp.
        // System V AMD64 ABI guarantees 128 bytes below RSP are not clobbered.
        let isLeaf = !function.blocks.contains { block in
            block.instructions.contains { if case .call = $0 { return true }; return false }
        }
        let useRedZone = isLeaf && !function.hasAlloca && aligned <= 128
        let effectiveStackAdj = useRedZone ? Int32(0) : aligned

        if !useFP {
            convertToRSPAddressing(&function, csShift: csShift, stackAdj: effectiveStackAdj)
        }

        expandPrologueEpilogue(&function, calleeSaved: calleeSaved, stackAdj: effectiveStackAdj)

        return function
    }

    /// Lower Machine phi nodes to parallel-copy instructions inserted at the end
    /// of each predecessor block (before the terminating branch).
    private func eliminateMachinePhis(_ function: inout Function, spillMap: [Int: Int32]) {
        guard function.blocks.contains(where: { !$0.phis.isEmpty }) else { return }

        let labelToIdx = Dictionary(uniqueKeysWithValues:
            function.blocks.enumerated().map { ($1.label, $0) })

        for bi in function.blocks.indices {
            let phis = function.blocks[bi].phis
            guard !phis.isEmpty else { continue }

            // Group copies by predecessor label.
            var predCopies: [String: [(src: Operand, dst: Operand, sz: Size)]] = [:]
            for phi in phis {
                let dst: Operand
                if case .virtual(let v) = phi.dest, let slot = spillMap[v] {
                    dst = .mem(.stack(slot))
                } else {
                    dst = .reg(phi.dest)
                }
                for arg in phi.args {
                    guard !machOperandEqual(arg.src, dst) else { continue }
                    predCopies[arg.label, default: []].append(
                        (src: arg.src, dst: dst, sz: phi.size))
                }
            }

            // Insert parallel copies at the end of each predecessor, before its branch.
            for (predLabel, copies) in predCopies {
                guard let predBi = labelToIdx[predLabel] else { continue }
                let ins = insertionPoint(in: function.blocks[predBi].instructions)
                if copies.count == 1 {
                    let c = copies[0]
                    function.blocks[predBi].instructions.insert(
                        machMovInstr(c.sz, src: c.src, dst: c.dst), at: ins)
                } else {
                    function.blocks[predBi].instructions.insert(
                        .pcopy(copies), at: ins)
                }
            }
            function.blocks[bi].phis = []
        }
    }

    /// Find the insertion point just before the final branch sequence in a block.
    private func insertionPoint(in instrs: [Instr]) -> Int {
        var i = instrs.count
        while i > 0 {
            switch instrs[i - 1] {
            case .jmp, .jmpIf, .ret, .tailCall, .jmpIndirect: i -= 1
            default: return i
            }
        }
        return i
    }

    /// Rewrite a single operand's virtual registers to physical regs or spill slots.
    private func rewriteOperand(_ op: Operand, assignMap: [Int: PhysReg],
                                 spillMap: [Int: Int32]) -> Operand {
        if case .reg(.virtual(let v)) = op {
            if let phys = assignMap[v] { return .reg(.physical(phys)) }
            if let slot = spillMap[v]  { return .mem(.stack(slot)) }
        }
        return op
    }

    // MARK: - Phi Coalescing

    /// Conservative phi coalescing: merge non-interfering (dest, arg) vreg pairs.
    /// Returns a UnionFind that maps each vreg to its canonical representative.
    private func coalescePhis(_ intervals: [Int: LiveInterval],
                               blockLastPos: [Int: Int]) -> UnionFind {
        // Build label → blockIdx map for predecessor lookups.
        let labelToIdx = Dictionary(uniqueKeysWithValues:
            function.blocks.enumerated().map { ($1.label, $0) })

        var uf = UnionFind()
        for block in function.blocks {
            for phi in block.phis {
                guard case .virtual(let d) = phi.dest, let ivD = intervals[d] else { continue }
                nextArg: for arg in phi.args {
                    guard case .reg(.virtual(let s)) = arg.src,
                          let ivS = intervals[s] else { continue }
                    // Must be the same register class (GP vs float)
                    guard ivD.isFloat == ivS.isFloat else { continue }
                    // Skip float intervals that span calls (must be spilled)
                    if ivD.isFloat && (ivD.spansCall || ivS.spansCall) { continue }
                    // Already in the same coalescing group
                    if uf.find(d) == uf.find(s) { continue }
                    // Conservative interference check: intervals overlap strictly?
                    // Boundary touch (ivD.start == ivS.end) is exactly the phi copy
                    // point and is NOT interference — coalescing is valid there.
                    let overlaps = ivD.start < ivS.end && ivS.start < ivD.end
                    guard !overlaps else { continue }
                    // Critical-edge check: for each OTHER predecessor Q (not the one
                    // contributing arg s), if s is live at Q's phi-copy point (end of Q),
                    // coalescing would cause Q's phi copy to overwrite s's register while
                    // s is still live on paths that flow through Q to other successors.
                    for otherArg in phi.args where otherArg.label != arg.label {
                        guard let qi = labelToIdx[otherArg.label],
                              let qEnd = blockLastPos[qi] else { continue }
                        if ivS.end >= qEnd { continue nextArg }
                    }
                    uf.union(d, s)
                }
            }
        }
        return uf
    }

    /// Merge coalesced interval groups into their representative interval.
    /// Non-representative vregs are removed from the map; their allocation will
    /// be propagated from the representative after linear scan (step 7b).
    private func mergeCoalescedIntervals(_ intervals: inout [Int: LiveInterval],
                                          uf: inout UnionFind) {
        var groups: [Int: [Int]] = [:]
        for v in intervals.keys { groups[uf.find(v), default: []].append(v) }
        for (rep, members) in groups where members.count > 1 {
            guard var merged = intervals[rep] else { continue }
            for v in members where v != rep {
                guard let iv = intervals[v] else { continue }
                merged.start     = min(merged.start, iv.start)
                merged.end       = max(merged.end, iv.end)
                merged.spansCall = merged.spansCall || iv.spansCall
                merged.loopDepth = max(merged.loopDepth, iv.loopDepth)
                intervals.removeValue(forKey: v)
            }
            intervals[rep] = merged
        }
    }

    // MARK: - Copy Coalescing

    /// Briggs conservative coalescing (George & Appel, "Iterated Register Coalescing", 1996).
    ///
    /// Builds an interference graph from live intervals, then iteratively coalesces
    /// copy-related vreg pairs that pass the Briggs criterion: the merged node must
    /// have fewer than K neighbors of significant degree (degree ≥ K), guaranteeing
    /// that coalescing does not introduce new spills.
    private func coalesceCopies(_ intervals: [Int: LiveInterval],
                                uf: inout UnionFind) {
        // ── 1. Compute group intervals reflecting prior phi coalescing ──
        var groupInterval: [Int: (start: Int, end: Int, isFloat: Bool, spansCall: Bool)] = [:]
        for (v, iv) in intervals {
            let rep = uf.find(v)
            if var g = groupInterval[rep] {
                g.start     = min(g.start, iv.start)
                g.end       = max(g.end, iv.end)
                g.spansCall = g.spansCall || iv.spansCall
                groupInterval[rep] = g
            } else {
                groupInterval[rep] = (iv.start, iv.end, iv.isFloat, iv.spansCall)
            }
        }

        // ── 2. Build interference graph (sweep-line) ──
        var adjList: [Int: Set<Int>] = [:]
        let reps = Array(groupInterval.keys)
            .sorted { groupInterval[$0]!.start < groupInterval[$1]!.start }
        for i in 0..<reps.count {
            let a = reps[i]
            let ivA = groupInterval[a]!
            for j in (i + 1)..<reps.count {
                let b = reps[j]
                let ivB = groupInterval[b]!
                if ivB.start >= ivA.end { break }
                if ivA.isFloat == ivB.isFloat {
                    adjList[a, default: []].insert(b)
                    adjList[b, default: []].insert(a)
                }
            }
        }

        // ── 3. Collect copy worklist (deduplicated) ──
        var worklist: [[Int]] = []
        var seen: Set<Int> = []  // Cantor pairing for dedup
        for block in function.blocks {
            for instr in block.instructions {
                let pair: (Int, Int)?
                switch instr {
                case .movRR(_, let src, let dst):
                    if case .virtual(let s) = src,
                       case .virtual(let d) = dst { pair = (s, d) }
                    else { pair = nil }
                case .xmmMovRR(_, let src, let dst):
                    if case .virtual(let s) = src,
                       case .virtual(let d) = dst { pair = (s, d) }
                    else { pair = nil }
                default:
                    pair = nil
                }
                guard let (s, d) = pair else { continue }
                let rs = uf.find(s), rd = uf.find(d)
                guard rs != rd else { continue }
                let lo = min(rs, rd), hi = max(rs, rd)
                let key = lo &* 1_000_003 &+ hi
                if seen.insert(key).inserted {
                    worklist.append([lo, hi])
                }
            }
        }

        // ── 4. Iterated Briggs coalescing ──
        let kGP  = PhysReg.allocatableGP.count - 2  // 12
        let kSSE = 15

        var changed = true
        while changed {
            changed = false
            worklist = worklist.filter { pair in
                let u = uf.find(pair[0]), v = uf.find(pair[1])
                if u == v { return false }  // already coalesced

                guard let ivU = groupInterval[u], let ivV = groupInterval[v] else { return false }
                // Different register classes cannot coalesce
                guard ivU.isFloat == ivV.isFloat else { return true }
                // Float intervals spanning calls must be spilled (no callee-saved XMM)
                if ivU.isFloat && (ivU.spansCall || ivV.spansCall) { return true }
                // Interfering pair cannot coalesce
                if adjList[u]?.contains(v) == true { return true }

                // Briggs criterion: merged node must have < K significant-degree neighbors
                let k = ivU.isFloat ? kSSE : kGP
                let neighborsUV = (adjList[u] ?? [])
                    .union(adjList[v] ?? [])
                    .subtracting([u, v])
                var significantCount = 0
                for n in neighborsUV {
                    if (adjList[n]?.count ?? 0) >= k {
                        significantCount += 1
                        if significantCount >= k { return true }  // early exit
                    }
                }

                // ── Coalesce ──
                uf.union(u, v)
                let rep = uf.find(u)
                let other = (rep == u) ? v : u

                // Update group interval
                groupInterval[rep] = (
                    min(ivU.start, ivV.start), max(ivU.end, ivV.end),
                    ivU.isFloat, ivU.spansCall || ivV.spansCall
                )
                groupInterval.removeValue(forKey: other)

                // Merge adjacency: transfer other's edges to rep
                if let otherNeighbors = adjList.removeValue(forKey: other) {
                    for n in otherNeighbors {
                        adjList[n]?.remove(other)
                        if n != rep {
                            adjList[n, default: []].insert(rep)
                            adjList[rep, default: []].insert(n)
                        }
                    }
                }

                // Extended interval may create new interference edges
                let merged = groupInterval[rep]!
                for (r, iv) in groupInterval where r != rep {
                    if iv.isFloat == merged.isFloat &&
                       merged.start < iv.end && iv.start < merged.end {
                        if adjList[rep, default: []].insert(r).inserted {
                            adjList[r, default: []].insert(rep)
                        }
                    }
                }

                changed = true
                return false  // remove from worklist
            }
        }
    }

    /// Check if an instruction is a redundant copy (same src and dst after allocation).
    private func isRedundantCopy(_ instr: Instr) -> Bool {
        switch instr {
        case .movRR(_, let src, let dst):
            return src == dst
        case .xmmMovRR(_, let src, let dst):
            if src == dst { return true }
        default:
            break
        }
        return false
    }

    // MARK: - Rematerialization

    /// Returns the destination vreg if `instr` is rematerializable (cheap to recompute
    /// with no vreg inputs). Covers: mov $imm, lea global/label, xor zeroing.
    private func rematCandidate(_ instr: Instr) -> Int? {
        switch instr {
        case .movIR(_, _, let dst):
            // mov $imm, %vreg — constant load
            if case .virtual(let v) = dst { return v }
            return nil
        case .lea(_, _, let dst):
            // lea symbol(%rip), %vreg — address computation (no memory access)
            if case .virtual(let v) = dst { return v }
            return nil
        default:
            return nil
        }
    }

    /// Emit a rematerialization instruction, rewriting the dest vreg to the given scratch register.
    private func emitRemat(_ rematInstr: Instr, scratch: PhysReg) -> Instr {
        return mapRegs(rematInstr) { reg in
            if case .virtual = reg { return .physical(scratch) }
            return reg
        }
    }

    // MARK: - Loop Depth

    /// Compute loop nesting depth per block using back-edge detection.
    /// A back edge (B → H) exists when H appears before B in block order.
    /// Each back edge adds 1 to the depth of all blocks from H to B (inclusive).
    private func computeBlockLoopDepths() -> [Int] {
        let n = function.blocks.count
        var depth = [Int](repeating: 0, count: n)
        let labelIdx = Dictionary(uniqueKeysWithValues:
            function.blocks.enumerated().map { ($1.label, $0) })
        for (bi, block) in function.blocks.enumerated() {
            for instr in block.instructions {
                let target: String?
                switch instr {
                case .jmp(let l): target = l
                case .jmpIf(_, let l): target = l
                default: target = nil
                }
                if let t = target, let ti = labelIdx[t], ti <= bi {
                    // Back edge bi → ti: mark all blocks ti...bi as inside a loop
                    for j in ti...bi { depth[j] += 1 }
                }
            }
        }
        return depth
    }

    // MARK: - CFG-aware liveness

    /// Extend live intervals using phi-aware CFG dataflow liveness analysis.
    /// Handles both loop back-edges and Machine phi node liveness:
    /// - phi.dest is a kill at block start (re-defined by the phi).
    /// - phi.arg.src values are treated as "used at end of predecessor" (gen of predecessor).
    private func extendIntervalsWithCFGLiveness(
        _ intervals: inout [Int: LiveInterval],
        posMap: [(blockIdx: Int, instrIdx: Int)]
    ) {
        let blocks = function.blocks
        guard blocks.count > 1 else { return }

        // Build block boundaries and label → index mapping.
        var blockStartPos = [Int](repeating: 0, count: blocks.count)
        var blockEndPos   = [Int](repeating: 0, count: blocks.count)
        var labelToIdx: [String: Int] = [:]
        for (bi, b) in blocks.enumerated() { labelToIdx[b.label] = bi }
        for (pos, loc) in posMap.enumerated() {
            let bi = loc.blockIdx
            if loc.instrIdx == 0 { blockStartPos[bi] = pos }
            blockEndPos[bi] = pos
        }

        // Build successor map from jump instructions.
        var successors: [[Int]] = Array(repeating: [], count: blocks.count)
        // Track blocks with indirect jumps and all label address targets.
        var indirectJumpBlocks: [Int] = []
        var labelAddrTargets: Set<Int> = []
        for (bi, block) in blocks.enumerated() {
            for instr in block.instructions {
                switch instr {
                case .jmp(let l):    if let si = labelToIdx[l] { successors[bi].append(si) }
                case .jmpIf(_, let l): if let si = labelToIdx[l] { successors[bi].append(si) }
                case .jmpIndirect:   indirectJumpBlocks.append(bi)
                default: break
                }
                // Detect lea of a block label (used for computed goto: &&label)
                if case .lea(_, let mem, _) = instr,
                   let name = mem.symbol,
                   let si = labelToIdx[name] {
                    labelAddrTargets.insert(si)
                }
            }
            // Add fallthrough edge: if block doesn't end with unconditional jump/return,
            // it falls through to the next block.
            if bi + 1 < blocks.count {
                let lastInstr = block.instructions.last
                let endsWithJump: Bool
                switch lastInstr {
                case .jmp, .jmpIndirect, .ret, .tailCall: endsWithJump = true
                default: endsWithJump = false
                }
                if !endsWithJump && !successors[bi].contains(bi + 1) {
                    successors[bi].append(bi + 1)
                }
            }
        }
        // Add synthetic edges from indirect jump blocks to all label address targets.
        // This ensures values are kept live across computed goto boundaries.
        if !indirectJumpBlocks.isEmpty && !labelAddrTargets.isEmpty {
            for bi in indirectJumpBlocks {
                for target in labelAddrTargets {
                    if !successors[bi].contains(target) {
                        successors[bi].append(target)
                    }
                }
            }
        }

        // Compute gen/kill per block, including phi node contributions.
        var gen:  [Set<Int>] = Array(repeating: [], count: blocks.count)
        var kill: [Set<Int>] = Array(repeating: [], count: blocks.count)
        for (bi, block) in blocks.enumerated() {
            var killed: Set<Int> = []
            var generated: Set<Int> = []

            // phi.dest is a kill at block start.
            for phi in block.phis {
                if case .virtual(let v) = phi.dest { killed.insert(v) }
            }

            // Standard instruction gen/kill.
            for instr in block.instructions {
                for reg in usesOf(instr) {
                    if case .virtual(let v) = reg, !killed.contains(v) { generated.insert(v) }
                }
                for reg in defsOf(instr) {
                    if case .virtual(let v) = reg { killed.insert(v) }
                }
            }

            // phi.arg.src of SUCCESSOR phis are used at the end of THIS block.
            // Note: the !killed check is intentionally omitted here.
            // A phi arg variable may be defined (killed) in this block AND used as a phi arg
            // at the very end of this block. We add it to generated unconditionally so
            // the interval extension covers the end of this block, preventing the register
            // from being reused after the variable's definition but before the phi copy.
            for si in successors[bi] {
                for phi in blocks[si].phis {
                    if let arg = phi.args.first(where: { $0.label == block.label }) {
                        if case .reg(.virtual(let v)) = arg.src {
                            generated.insert(v)
                        }
                    }
                }
            }

            gen[bi]  = generated
            kill[bi] = killed
        }

        // Dataflow to fixed point (reverse order for faster convergence).
        var liveIn:  [Set<Int>] = Array(repeating: [], count: blocks.count)
        var liveOut: [Set<Int>] = Array(repeating: [], count: blocks.count)
        var changed = true
        while changed {
            changed = false
            for bi in (0..<blocks.count).reversed() {
                var newLiveOut: Set<Int> = []
                for si in successors[bi] { newLiveOut.formUnion(liveIn[si]) }
                var newLiveIn = gen[bi]
                newLiveIn.formUnion(newLiveOut.subtracting(kill[bi]))
                if newLiveIn != liveIn[bi] || newLiveOut != liveOut[bi] {
                    changed = true
                    liveIn[bi]  = newLiveIn
                    liveOut[bi] = newLiveOut
                }
            }
        }

        // Extend intervals to cover every block where the vreg is live.
        for bi in 0..<blocks.count {
            let live = liveIn[bi].union(liveOut[bi])
            guard !live.isEmpty else { continue }
            let bStart = blockStartPos[bi]
            let bEnd   = blockEndPos[bi]
            for v in live {
                if var iv = intervals[v] {
                    if bStart < iv.start { iv.start = bStart }
                    if bEnd   > iv.end   { iv.end   = bEnd   }
                    intervals[v] = iv
                }
            }
        }
    }

    // MARK: - Register picking

    /// Pick a register from the free pool, preferring callee-saved if the interval spans a call.
    /// Skips registers whose fixed intervals overlap the virtual register's live range.
    /// For float intervals that span a call, returns nil to force a spill — System V AMD64
    /// ABI has no callee-saved XMM registers, so the value must live on the stack.
    private func pickReg(from pool: inout [PhysReg], spansCall: Bool,
                         isFloat: Bool,
                         interval: LiveInterval,
                         fixedIntervals: [PhysReg: [(start: Int, end: Int)]],
                         hint: PhysReg? = nil) -> PhysReg? {
        if pool.isEmpty { return nil }

        // All XMM registers are caller-saved in System V ABI.
        // A float interval spanning a call must be spilled.
        if spansCall && isFloat { return nil }

        // Filter out candidates that overlap fixed intervals
        let viable = pool.indices.filter { idx in
            !overlapsFixed(pool[idx], start: interval.start, end: interval.end,
                           fixedIntervals: fixedIntervals)
        }
        if viable.isEmpty { return nil }

        // Try hint first: if the hint register is viable and satisfies constraints, use it.
        // Only use hint when it matches the preferred class to avoid disrupting allocation.
        let isCalleeSaved: (PhysReg) -> Bool = { PhysReg.calleeSavedGP.contains($0) || $0 == .rbp }

        if let h = hint, let idx = viable.first(where: { pool[$0] == h }) {
            if spansCall {
                // spansCall needs callee-saved
                if !isFloat && isCalleeSaved(h) {
                    return pool.remove(at: idx)
                }
            } else if isFloat {
                // SSE has no callee-saved, any hint is fine
                return pool.remove(at: idx)
            } else if PhysReg.callerSavedGP.contains(h) {
                // Non-spansCall GP prefers caller-saved — only accept caller-saved hints
                return pool.remove(at: idx)
            }
        }

        if spansCall {
            // MUST use callee-saved register — caller-saved would be clobbered by the call.
            if let idx = viable.first(where: { isCalleeSaved(pool[$0]) }) {
                return pool.remove(at: idx)
            }
            // No callee-saved available → force spill (return nil).
            return nil
        }
        // Prefer caller-saved (shorter-lived)
        if let idx = viable.first(where: { PhysReg.callerSavedGP.contains(pool[$0]) }) {
            return pool.remove(at: idx)
        }
        // Any viable
        return pool.remove(at: viable[0])
    }

    /// Check if a physical register's fixed intervals overlap the given range.
    private func overlapsFixed(_ reg: PhysReg, start: Int, end: Int,
                               fixedIntervals: [PhysReg: [(start: Int, end: Int)]]) -> Bool {
        guard let fixed = fixedIntervals[reg] else { return false }
        for f in fixed {
            if f.start <= end && f.end >= start { return true }
        }
        return false
    }

    // MARK: - Spilling

    private func spill(_ intervals: inout [LiveInterval], index i: Int,
                       active: inout [Int], freePool: inout [PhysReg],
                       spillOffset: inout Int32) {
        // Find the active interval with the lowest spill weight (cheapest to evict).
        // If the current interval is cheaper than any active interval, spill current instead.
        // Only consider evicting intervals of the same register class (GP vs SSE).
        // spansCall float: no callee-saved XMM in SysV ABI → always spill (skip eviction).
        // spansCall GP: only consider callee-saved holders (caller-saved would be clobbered).
        let isFloat = intervals[i].isFloat
        if intervals[i].spansCall && isFloat {
            if intervals[i].spillSlot == nil {
                spillOffset += 8
                intervals[i].spillSlot = spillOffset
            }
            return
        }
        let candidates: [Int]
        let sameClassActive = active.filter { intervals[$0].isFloat == isFloat }
        if intervals[i].spansCall {
            candidates = sameClassActive.filter {
                if let r = intervals[$0].reg { return PhysReg.calleeSavedGP.contains(r) || r == .rbp }
                return false
            }
        } else {
            candidates = sameClassActive
        }
        let evictIdx = candidates.min(by: { intervals[$0].spillWeight < intervals[$1].spillWeight })
        let currentWeight = intervals[i].spillWeight
        if let eidx = evictIdx, intervals[eidx].spillWeight < currentWeight {
            // Evict the cheapest active interval, give its register to current
            let stolen = intervals[eidx].reg!
            intervals[i].reg = stolen
            if intervals[eidx].spillSlot == nil {
                spillOffset += 8
                intervals[eidx].spillSlot = spillOffset
            }
            intervals[eidx].reg = nil
            active.removeAll { $0 == eidx }
            active.append(i)
            active.sort { intervals[$0].end < intervals[$1].end }
        } else {
            // Spill current interval
            if intervals[i].spillSlot == nil {
                spillOffset += 8
                intervals[i].spillSlot = spillOffset
            }
        }
    }

    // MARK: - Live Range Splitting

    /// Try to split the interval at an optimal position before falling back to full spill.
    /// Splitting creates two sub-intervals for the same vreg with a shared spill slot
    /// for value transfer at the boundary.
    private mutating func splitOrSpill(
        _ intervals: inout [LiveInterval], index i: Int,
        active: inout [Int],
        freeGP: inout [PhysReg], freeSSE: inout [PhysReg],
        spillOffset: inout Int32,
        unhandled: inout [Int],
        sharedSpillSlots: inout Set<Int32>,
        sortedCalls: [Int],
        fixedIntervals: [PhysReg: [(start: Int, end: Int)]],
        usedCalleeSaved: inout Set<PhysReg>,
        vregAssignment: inout [Int: PhysReg],
        copyHintSource: [Int: Int]
    ) {
        let current = intervals[i]
        let isFloat = current.isFloat

        // Try to find an optimal split point.
        // Don't re-split intervals that already have a spillSlot from a prior split
        // (recursive splitting creates conflicting shared slots for boundary copies).
        if current.spillSlot == nil,
           let splitPos = findOptimalSplitPoint(current, sortedCalls: sortedCalls),
           splitPos > current.start + 1, splitPos < current.end {

            // Allocate shared spill slot for value transfer at boundary
            spillOffset += 8
            let sharedSlot = spillOffset
            sharedSpillSlots.insert(sharedSlot)

            // Create second half: [splitPos, original.end]
            var secondHalf = current
            secondHalf.start = splitPos
            secondHalf.reg = nil
            secondHalf.spillSlot = sharedSlot
            // A call AT the start of a split sub-interval means the boundary load
            // (inserted before the call) would be clobbered. Mark spansCall=true.
            secondHalf.spansCall = isCallAt(splitPos, sortedCalls)
                                || hasCallInRange(splitPos, current.end, sortedCalls)
            let newIdx = intervals.count
            intervals.append(secondHalf)

            // Insert into unhandled at correct position (descending start order,
            // popLast gives smallest start)
            let insertAt = unhandled.firstIndex { intervals[$0].start <= splitPos }
                           ?? unhandled.endIndex
            unhandled.insert(newIdx, at: insertAt)

            // Shorten first half: [original.start, splitPos - 1]
            intervals[i].end = splitPos - 1
            intervals[i].spillSlot = sharedSlot
            // If this is a re-split sub-interval whose start is a call position,
            // the boundary load before that call would be clobbered.
            intervals[i].spansCall = isCallAt(intervals[i].start, sortedCalls)
                                   || hasCallInRange(intervals[i].start, splitPos - 1, sortedCalls)

            // Try to allocate first half (it's shorter, may succeed now)
            let hint = copyHintSource[current.vreg].flatMap { vregAssignment[$0] }

            if isFloat {
                if let reg = pickReg(from: &freeSSE, spansCall: intervals[i].spansCall,
                                     isFloat: true, interval: intervals[i],
                                     fixedIntervals: fixedIntervals, hint: hint) {
                    intervals[i].reg = reg
                    vregAssignment[current.vreg] = reg
                    let insertPos = active.firstIndex { intervals[$0].end >= intervals[i].end } ?? active.endIndex
                    active.insert(i, at: insertPos)
                    return
                }
            } else {
                if let reg = pickReg(from: &freeGP, spansCall: intervals[i].spansCall,
                                     isFloat: false, interval: intervals[i],
                                     fixedIntervals: fixedIntervals, hint: hint) {
                    intervals[i].reg = reg
                    vregAssignment[current.vreg] = reg
                    if PhysReg.calleeSavedGP.contains(reg) || reg == .rbp { usedCalleeSaved.insert(reg) }
                    let insertPos = active.firstIndex { intervals[$0].end >= intervals[i].end } ?? active.endIndex
                    active.insert(i, at: insertPos)
                    return
                }
            }

            // First half also can't get a register — fall through to spill.
            // spillSlot is already pre-assigned (sharedSlot), so spill() reuses it.
            if isFloat {
                spill(&intervals, index: i, active: &active, freePool: &freeSSE,
                      spillOffset: &spillOffset)
            } else {
                spill(&intervals, index: i, active: &active, freePool: &freeGP,
                      spillOffset: &spillOffset)
            }
        } else {
            // Can't split (too short) — standard spill
            if isFloat {
                spill(&intervals, index: i, active: &active, freePool: &freeSSE,
                      spillOffset: &spillOffset)
            } else {
                spill(&intervals, index: i, active: &active, freePool: &freeGP,
                      spillOffset: &spillOffset)
            }
        }
    }

    /// Find the optimal position to split an interval.
    /// Prefers call boundaries (resolves spansCall), then midpoint.
    private func findOptimalSplitPoint(
        _ interval: LiveInterval, sortedCalls: [Int]
    ) -> Int? {
        let lo = interval.start
        let hi = interval.end
        guard hi - lo > 2 else { return nil }  // too short to split

        // Priority 1: first call position within the interval
        var left = 0, right = sortedCalls.count
        while left < right {
            let mid = (left + right) / 2
            if sortedCalls[mid] <= lo { left = mid + 1 } else { right = mid }
        }
        if left < sortedCalls.count && sortedCalls[left] < hi {
            return sortedCalls[left]
        }

        // Priority 2: midpoint
        let mid = (lo + hi) / 2
        if mid > lo + 1 && mid < hi { return mid }

        return nil
    }

    /// Check if there's a call instruction in the range (start, end) — exclusive both ends.
    /// For original intervals, this is correct: a call at the exact start (def point) or end
    /// (last use) doesn't require the value to survive across it.
    private func hasCallInRange(_ start: Int, _ end: Int, _ sortedCalls: [Int]) -> Bool {
        var lo = 0, hi = sortedCalls.count
        while lo < hi {
            let mid = (lo + hi) / 2
            if sortedCalls[mid] <= start { lo = mid + 1 } else { hi = mid }
        }
        return lo < sortedCalls.count && sortedCalls[lo] < end
    }

    /// Check if there's a call exactly at the given position (binary search).
    private func isCallAt(_ pos: Int, _ sortedCalls: [Int]) -> Bool {
        var lo = 0, hi = sortedCalls.count
        while lo < hi {
            let mid = (lo + hi) / 2
            if sortedCalls[mid] < pos { lo = mid + 1 }
            else if sortedCalls[mid] > pos { hi = mid }
            else { return true }
        }
        return false
    }

    // MARK: - Instruction rewriting

    private func rewriteInstr(_ instr: Instr, assignMap: [Int: PhysReg],
                               reloadMap: [Int: PhysReg]) -> Instr {
        return mapRegs(instr) { reg in
            if case .virtual(let v) = reg {
                // Check reload map first (for spilled uses)
                if let scratch = reloadMap[v] {
                    return .physical(scratch)
                }
                // Check assignment map
                if let phys = assignMap[v] {
                    return .physical(phys)
                }
            }
            return reg
        }
    }

    // MARK: - Stack offset adjustment for callee-saved registers

    /// Shift all rbp-relative stack memory operands by `shift` bytes to make room
    /// for callee-saved register pushes between rbp and the local frame.
    private func adjustStackOffsets(_ function: inout Function, by shift: Int32) {
        for bi in function.blocks.indices {
            function.blocks[bi].instructions = function.blocks[bi].instructions.map { instr in
                instr.mapMemory { mem in
                    // Only adjust stack frame references with negative displacement (locals)
                    if mem.isFrameRef, mem.displacement < 0 {
                        var m = mem
                        m.displacement -= shift
                        return m
                    }
                    return mem
                }
            }
        }
    }

    // MARK: - RSP-based addressing conversion (frame pointer omission)

    /// Convert all RBP-relative memory references to RSP-relative.
    ///
    /// Without FP, stack layout after prologue (push CS...; sub stackAdj, %rsp):
    ///   entry_rsp:                return addr
    ///   entry_rsp - csShift:      after callee-saved pushes
    ///   entry_rsp - csShift - stackAdj: RSP (after sub)
    ///
    /// Locals (disp < 0, before adjustStackOffsets):
    ///   Original: -(localOffset)(%rbp), physical = entry_rsp - 8 - localOffset (FP world)
    ///   Without FP, local is at entry_rsp - csShift - localOffset
    ///   RSP-relative: RSP + stackAdj - localOffset → delta_local = stackAdj
    ///   (adjustStackOffsets was skipped, so disp is still -localOffset)
    ///
    /// Stack args (disp > 0, e.g. 16(%rbp)):
    ///   Original: disp(%rbp), physical = entry_rsp - 8 + disp (FP world)
    ///   Without FP: same physical = RSP + csShift + stackAdj - 8 + disp
    ///   delta_arg = csShift + stackAdj - 8
    private func convertToRSPAddressing(_ function: inout Function,
                                         csShift: Int32, stackAdj: Int32) {
        let deltaLocal = stackAdj             // for negative (local) displacements
        let deltaArg = csShift + stackAdj - 8 // for positive (stack arg) displacements
        for bi in function.blocks.indices {
            function.blocks[bi].instructions = function.blocks[bi].instructions.map { instr in
                instr.mapMemory { mem in
                    guard mem.isFrameRef else { return mem }
                    var m = mem
                    m.base = .physical(.rsp)
                    m.displacement += (mem.displacement < 0) ? deltaLocal : deltaArg
                    m.isFrameRef = false
                    return m
                }
            }
        }
    }

    // MARK: - Prologue / Epilogue expansion

    private func expandPrologueEpilogue(_ function: inout Function,
                                         calleeSaved: [PhysReg],
                                         stackAdj: Int32) {
        let useFP = function.usesFramePointer
        for bi in function.blocks.indices {
            var expanded: [Instr] = []
            for instr in function.blocks[bi].instructions {
                switch instr {
                case .prologue:
                    if useFP {
                        expanded.append(.push(.qword, .reg(.physical(.rbp))))
                        expanded.append(.movRR(.qword, src: .physical(.rsp),
                                               dst: .physical(.rbp)))
                    }
                    for r in calleeSaved {
                        expanded.append(.push(.qword, .reg(.physical(r))))
                    }
                    if stackAdj > 0 {
                        expanded.append(.aluRmiR(.sub, .qword, src: .imm(Int64(stackAdj)),
                                                 dst: .physical(.rsp)))
                    }

                case .epilogue:
                    if useFP {
                        // Use RBP-based restore to handle alloca (dynamic RSP changes).
                        let calleeSaveSize = Int32(calleeSaved.count * 8)
                        if calleeSaveSize > 0 {
                            expanded.append(.lea(.qword,
                                src: Memory(base: .physical(.rbp), displacement: -calleeSaveSize),
                                dst: .physical(.rsp)))
                        } else {
                            expanded.append(.movRR(.qword, src: .physical(.rbp), dst: .physical(.rsp)))
                        }
                        for r in calleeSaved.reversed() {
                            expanded.append(.pop(.qword, .physical(r)))
                        }
                        expanded.append(.pop(.qword, .physical(.rbp)))
                    } else {
                        // No frame pointer: restore RSP then pop callee-saved.
                        if stackAdj > 0 {
                            expanded.append(.aluRmiR(.add, .qword, src: .imm(Int64(stackAdj)),
                                                     dst: .physical(.rsp)))
                        }
                        for r in calleeSaved.reversed() {
                            expanded.append(.pop(.qword, .physical(r)))
                        }
                    }

                default:
                    expanded.append(instr)
                }
            }
            function.blocks[bi].instructions = expanded
        }
    }

    // MARK: - Alignment helper

    private func alignUp(_ value: Int32, to alignment: Int32,
                          considering pushed: Int32 = 0) -> Int32 {
        guard alignment > 0 else { return value }
        // After pushing `pushed` bytes + subtracting `value`, total frame must be 16-aligned
        let total = pushed + value
        let aligned = (total + alignment - 1) / alignment * alignment
        return aligned - pushed
    }

    // MARK: - Float vreg detection

    private func isFloatVreg(_ v: Int, _ floatVregs: Set<Int>) -> Bool {
        return floatVregs.contains(v)
    }
}

// MARK: - Instruction def/use analysis

/// Returns the registers defined (written) by an instruction.
func defsOf(_ instr: Instr) -> [Reg] {
    switch instr {
    // Data movement — dst is defined (reg-targeting variants only)
    case .movRR(_, _, let dst):
        return [dst]
    case .movMR(_, _, let dst):
        return [dst]
    case .movIR(_, _, let dst):
        return [dst]
    case .movRM, .movIM, .movMM:
        // Store to memory — no register def
        return []
    case .movsxRmR(_, _, _, let dst), .movzxRmR(_, _, _, let dst):
        return [dst]
    case .lea(_, _, let dst):
        return [dst]
    case .pop(_, let op):
        return [op]

    // Arithmetic — dst is read+written
    case .aluRmiR(_, _, _, let dst), .imul(_, _, let dst):
        return [dst]
    case .unaryRm(_, _, let op):
        return [op]

    // signExtendData/gpDiv implicit defs handled by regConstraint + fixedIntervals
    case .signExtendData:
        return []
    case .gpDiv:
        return []

    // Bitwise/shift — dst is read+written
    case .shiftR(_, _, _, let dst):
        return [dst]

    // Comparison/test — no register def (only flags)
    case .cmpRmiR:
        return []

    // Conditional
    case .setcc(_, let op):
        return [op]
    case .cmove(_, _, _, let dst):
        return [dst]

    // Control flow
    case .jmp, .jmpIf, .jmpIndirect, .ret, .tailCall:
        return []

    // Call clobbers handled by regConstraint + fixedIntervals
    case .call:
        return []

    // SSE
    case .xmmMovRR(_, _, let dst), .xmmMovMR(_, _, let dst):
        return [dst]
    case .xmmMovRM:
        return []
    case .xmmRmR(_, _, _, let dst):
        return [dst]
    case .xmmCmp:
        return []
    case .cvt(_, _, _, let dst):
        return [dst]

    // Parallel copy
    case .pcopy(let copies):
        return copies.flatMap { regsIn($0.dst) }

    // Pseudo / other
    case .prologue, .epilogue, .inlineAsm:
        return []
    case .push:
        return []

    // Constraint pseudo-instructions (expanded before regalloc)
    case .idivRemSeq:
        fatalError("pseudo-instructions must be expanded before register allocation")
    }
}

/// Returns the registers used (read) by an instruction.
func usesOf(_ instr: Instr) -> [Reg] {
    switch instr {
    // Data movement
    case .movRR(_, let src, _):
        return [src]
    case .movRM(_, let src, let mem):
        var result: [Reg] = [src]
        if let b = mem.base { result.append(b) }
        if let i = mem.index { result.append(i) }
        return result
    case .movMR(_, let mem, _):
        var result: [Reg] = []
        if let b = mem.base { result.append(b) }
        if let i = mem.index { result.append(i) }
        return result
    case .movIR:
        return []
    case .movIM(_, _, let mem):
        var result: [Reg] = []
        if let b = mem.base { result.append(b) }
        if let i = mem.index { result.append(i) }
        return result
    case .movMM(_, let src, let dst):
        var result: [Reg] = []
        if let b = src.base { result.append(b) }
        if let i = src.index { result.append(i) }
        if let b = dst.base { result.append(b) }
        if let i = dst.index { result.append(i) }
        return result
    case .movsxRmR(_, _, let src, _), .movzxRmR(_, _, let src, _):
        return regsIn(src)
    case .lea(_, let src, _):
        var result: [Reg] = []
        if let b = src.base { result.append(b) }
        if let i = src.index { result.append(i) }
        return result
    case .push(_, let op):
        return regsIn(op)
    case .pop:
        return []

    // Arithmetic
    case .aluRmiR(_, _, let src, let dst), .imul(_, let src, let dst):
        return regsIn(src) + [dst]
    case .unaryRm(_, _, let op):
        return [op]
    // signExtendData/gpDiv implicit uses handled by regConstraint + fixedIntervals
    case .signExtendData:
        return []
    case .gpDiv(_, let op, _):
        return [op]

    // Bitwise/shift
    case .shiftR(_, _, let src, let dst):
        return regsIn(src) + [dst]

    // Comparison
    case .cmpRmiR(_, _, let src, let dst):
        return regsIn(src) + [dst]

    // Conditional
    case .setcc:
        return []
    case .cmove(_, _, let src, let dst):
        return regsIn(src) + [dst]

    // Control flow
    case .jmp, .jmpIf, .ret:
        return []
    case .jmpIndirect(let op):
        return [op]
    case .tailCall(let op):
        return regsIn(op)
    case .call(let op):
        // The callee operand + all argument registers are implicitly used
        return regsIn(op)

    // SSE
    case .xmmMovRR(_, let src, _):
        return [src]
    case .xmmMovRM(_, let src, let mem):
        var result: [Reg] = [src]
        if let b = mem.base { result.append(b) }
        if let i = mem.index { result.append(i) }
        return result
    case .xmmMovMR(_, let mem, _):
        var result: [Reg] = []
        if let b = mem.base { result.append(b) }
        if let i = mem.index { result.append(i) }
        return result
    case .xmmRmR(_, _, let src, let dst):
        return regsIn(src) + [dst]
    case .xmmCmp(_, let src, let dst):
        return regsIn(src) + [dst]
    case .cvt(_, _, let src, _):
        return regsIn(src)

    // Parallel copy
    case .pcopy(let copies):
        return copies.flatMap { regsIn($0.src) + regsInMem($0.dst) }

    // Pseudo / other
    case .prologue, .epilogue, .inlineAsm:
        return []

    case .idivRemSeq:
        fatalError("pseudo-instructions must be expanded before register allocation")
    }
}

/// Extract register references from an operand (reg or memory base/index).
private func regsIn(_ op: Operand) -> [Reg] {
    switch op {
    case .reg(let r):
        return [r]
    case .mem(let m):
        var result: [Reg] = []
        if let b = m.base { result.append(b) }
        if let i = m.index { result.append(i) }
        return result
    case .imm, .label:
        return []
    }
}

/// Extract only memory-related register references (base/index), not the register itself.
/// Used for dst operands in mov-like instructions where the dst register is defined, not used,
/// but memory base/index are used.
private func regsInMem(_ op: Operand) -> [Reg] {
    if case .mem(let m) = op {
        var result: [Reg] = []
        if let b = m.base { result.append(b) }
        if let i = m.index { result.append(i) }
        return result
    }
    return []
}

/// Detect if an instruction's definition is for a float register.
private func isFloatDef(_ instr: Instr) -> Bool {
    switch instr {
    case .xmmMovRR, .xmmMovMR, .xmmRmR:
        return true
    case .cvt(_, let to, _, _):
        return to == .single || to == .double_
    default:
        return false
    }
}

// MARK: - Union-Find for phi coalescing

/// Path-compressed union-find over vreg integers.
struct UnionFind {
    private var parent: [Int: Int] = [:]

    mutating func find(_ x: Int) -> Int {
        guard let p = parent[x] else { return x }
        let root = find(p)
        parent[x] = root
        return root
    }

    mutating func union(_ a: Int, _ b: Int) {
        let ra = find(a), rb = find(b)
        if ra != rb { parent[ra] = rb }
    }
}

// MARK: - Register rewriting

/// Apply a register mapping function to all registers in an instruction.
func mapRegs(_ instr: Instr, _ f: (Reg) -> Reg) -> Instr {
    switch instr {
    case .movRR(let sz, let src, let dst):
        return .movRR(sz, src: f(src), dst: f(dst))
    case .movRM(let sz, let src, let mem):
        let mappedMem = Memory(base: mem.base.map(f), index: mem.index.map(f),
                               scale: mem.scale, displacement: mem.displacement,
                               symbol: mem.symbol)
        return .movRM(sz, src: f(src), dst: mappedMem)
    case .movMR(let sz, let mem, let dst):
        let mappedMem = Memory(base: mem.base.map(f), index: mem.index.map(f),
                               scale: mem.scale, displacement: mem.displacement,
                               symbol: mem.symbol)
        return .movMR(sz, src: mappedMem, dst: f(dst))
    case .movIR(let sz, let imm, let dst):
        return .movIR(sz, imm: imm, dst: f(dst))
    case .movIM(let sz, let imm, let mem):
        let mappedMem = Memory(base: mem.base.map(f), index: mem.index.map(f),
                               scale: mem.scale, displacement: mem.displacement,
                               symbol: mem.symbol)
        return .movIM(sz, imm: imm, dst: mappedMem)
    case .movMM(let sz, let src, let dst):
        let mappedSrc = Memory(base: src.base.map(f), index: src.index.map(f),
                               scale: src.scale, displacement: src.displacement,
                               symbol: src.symbol)
        let mappedDst = Memory(base: dst.base.map(f), index: dst.index.map(f),
                               scale: dst.scale, displacement: dst.displacement,
                               symbol: dst.symbol)
        return .movMM(sz, src: mappedSrc, dst: mappedDst)
    case .movsxRmR(let from, let to, let src, let dst):
        return .movsxRmR(from: from, to: to, src: mapOp(src, f), dst: f(dst))
    case .movzxRmR(let from, let to, let src, let dst):
        return .movzxRmR(from: from, to: to, src: mapOp(src, f), dst: f(dst))
    case .lea(let sz, let src, let dst):
        let mappedMem = Memory(base: src.base.map(f), index: src.index.map(f),
                               scale: src.scale, displacement: src.displacement,
                               symbol: src.symbol)
        return .lea(sz, src: mappedMem, dst: f(dst))
    case .push(let sz, let op):
        return .push(sz, mapOp(op, f))
    case .pop(let sz, let op):
        return .pop(sz, f(op))

    case .aluRmiR(let op, let sz, let src, let dst):
        return .aluRmiR(op, sz, src: mapOp(src, f), dst: f(dst))
    case .imul(let sz, let src, let dst):
        return .imul(sz, src: mapOp(src, f), dst: f(dst))
    case .signExtendData(let sz):
        return .signExtendData(sz)
    case .gpDiv(let sz, let op, let signed):
        return .gpDiv(sz, f(op), signed: signed)
    case .unaryRm(let op, let sz, let operand):
        return .unaryRm(op, sz, f(operand))

    case .shiftR(let op, let sz, let src, let dst):
        return .shiftR(op, sz, src: mapOp(src, f), dst: f(dst))

    case .cmpRmiR(let op, let sz, let src, let dst):
        return .cmpRmiR(op, sz, src: mapOp(src, f), dst: f(dst))

    case .setcc(let cc, let op):
        return .setcc(cc, f(op))
    case .cmove(let cc, let sz, let src, let dst):
        return .cmove(cc, sz, src: mapOp(src, f), dst: f(dst))

    case .jmp(let l):
        return .jmp(l)
    case .jmpIf(let cc, let l):
        return .jmpIf(cc, l)
    case .jmpIndirect(let op):
        return .jmpIndirect(f(op))
    case .tailCall(let op):
        return .tailCall(mapOp(op, f))
    case .call(let op):
        return .call(mapOp(op, f))
    case .ret:
        return .ret

    case .xmmMovRR(let prec, let src, let dst):
        return .xmmMovRR(prec, src: f(src), dst: f(dst))
    case .xmmMovRM(let prec, let src, let dst):
        let mappedMem = Memory(base: dst.base.map(f), index: dst.index.map(f),
                               scale: dst.scale, displacement: dst.displacement,
                               symbol: dst.symbol)
        return .xmmMovRM(prec, src: f(src), dst: mappedMem)
    case .xmmMovMR(let prec, let src, let dst):
        let mappedMem = Memory(base: src.base.map(f), index: src.index.map(f),
                               scale: src.scale, displacement: src.displacement,
                               symbol: src.symbol)
        return .xmmMovMR(prec, src: mappedMem, dst: f(dst))
    case .xmmRmR(let op, let prec, let src, let dst):
        return .xmmRmR(op, prec, src: mapOp(src, f), dst: f(dst))
    case .xmmCmp(let prec, let src, let dst):
        return .xmmCmp(prec, src: mapOp(src, f), dst: f(dst))
    case .cvt(let from, let to, let src, let dst):
        return .cvt(from: from, to: to, src: mapOp(src, f), dst: f(dst))

    case .pcopy(let copies):
        return .pcopy(copies.map { (src: mapOp($0.src, f), dst: mapOp($0.dst, f), sz: $0.sz) })

    case .prologue:
        return .prologue
    case .epilogue:
        return .epilogue
    case .inlineAsm(let s):
        return .inlineAsm(s)

    case .idivRemSeq:
        fatalError("pseudo-instructions must be expanded before register allocation")
    }
}

/// Apply a register mapping function to an operand.
/// Compare two Machine operands for equality (used by phi elimination to skip trivial copies).
private func machOperandEqual(_ a: Operand, _ b: Operand) -> Bool {
    switch (a, b) {
    case (.reg(let r1), .reg(let r2)):     return r1 == r2
    case (.imm(let v1), .imm(let v2)):     return v1 == v2
    case (.mem(let m1), .mem(let m2)):     return m1 == m2
    case (.label(let s1), .label(let s2)): return s1 == s2
    default: return false
    }
}

/// Emit the appropriate move instruction for the given size.
private func machMovInstr(_ sz: Size, src: Operand, dst: Operand) -> Instr {
    switch sz {
    case .single:  return .xmmMov(.single, src: src, dst: dst)   // factory dispatches
    case .double_: return .xmmMov(.double_, src: src, dst: dst) // factory dispatches
    default:       return .mov(sz, src: src, dst: dst)
    }
}

private func mapOp(_ op: Operand, _ f: (Reg) -> Reg) -> Operand {
    switch op {
    case .reg(let r):
        return .reg(f(r))
    case .mem(let m):
        return .mem(Memory(base: m.base.map(f), index: m.index.map(f),
                           scale: m.scale, displacement: m.displacement,
                           symbol: m.symbol))
    case .imm, .label:
        return op
    }
}
