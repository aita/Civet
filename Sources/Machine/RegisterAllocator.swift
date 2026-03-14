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
    let gpScratch: Reg = .physical(LinearScanAllocator.gpScratch)

    for bi in function.blocks.indices {
        var fixed: [Instr] = []
        for instr in function.blocks[bi].instructions {
            switch instr {
            // movq $large_imm, mem — imm must fit in sign-extended 32 bits
            case .movIM(.qword, let v, let mem)
                where v > Int64(Int32.max) || v < Int64(Int32.min):
                fixed.append(.movIR(.qword, imm: v, dst: gpScratch))
                fixed.append(.movRM(.qword, src: gpScratch, dst: mem))
                continue
            // movMM: mem→mem must go through scratch register
            case .movMM(let sz, let src, let dst):
                fixed.append(.movMR(sz, src: src, dst: gpScratch))
                fixed.append(.movRM(sz, src: gpScratch, dst: dst))
                continue
            case .aluRmiR(let op, let sz, let src, let dst):
                if case .mem = src {
                    fixed.append(.mov(sz, src: src, dst: .reg(gpScratch)))
                    fixed.append(.aluRmiR(op, sz, src: .reg(gpScratch), dst: dst))
                    continue
                }
            case .cmpRmiR(let op, let sz, let src, let dst):
                if case .mem = src {
                    fixed.append(.mov(sz, src: src, dst: .reg(gpScratch)))
                    fixed.append(.cmpRmiR(op, sz, src: .reg(gpScratch), dst: dst))
                    continue
                }
            default:
                break
            }
            fixed.append(instr)
        }
        function.blocks[bi].instructions = fixed
    }
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
        for pos in 0..<posMap.count {
            let blockIdx = posMap[pos].blockIdx
            let d = blockDepths[blockIdx]
            guard d > 0 else { continue }
            for v in intervals.keys {
                if intervals[v]!.start <= pos && intervals[v]!.end >= pos {
                    intervals[v]!.loopDepth = max(intervals[v]!.loopDepth, d)
                }
            }
        }

        // 4. Mark intervals that span calls
        for pos in callPositions {
            for v in intervals.keys {
                if intervals[v]!.start < pos && intervals[v]!.end > pos {
                    intervals[v]!.spansCall = true
                }
            }
        }


        // 4b. Phi coalescing + copy coalescing: merge non-interfering interval pairs
        // so they share the same physical register, turning copies into noops.
        var coalescingUF = coalescePhis(intervals, blockLastPos: blockLastPos)
        coalesceCopies(intervals, uf: &coalescingUF)
        let originalVregs = Set(intervals.keys)
        mergeCoalescedIntervals(&intervals, uf: &coalescingUF)

        // 5. Sort intervals by start position (break ties by vreg number for determinism)
        var sorted = Array(intervals.values).sorted {
            $0.start != $1.start ? $0.start < $1.start : $0.vreg < $1.vreg
        }



        // 6. Linear scan allocation
        var active: [Int] = []  // indices into sorted, sorted by end
        var freeGP = PhysReg.allocatableGP.filter { $0 != Self.gpScratch && $0 != Self.gpScratch2 }
            .sorted { $0.rawValue < $1.rawValue }
        var freeSSE = (PhysReg.sseArgRegs + [.xmm8, .xmm9, .xmm10, .xmm11,
                                              .xmm12, .xmm13, .xmm14])
            .sorted { $0.rawValue < $1.rawValue }
        // xmm15 reserved as scratch

        var spillOffset = function.stackSize
        var usedCalleeSaved: Set<PhysReg> = []

        for i in sorted.indices {
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

            // Try to allocate
            if current.isFloat {
                if current.spansCall {
                    // All XMM registers are caller-saved — force spill, never steal a register.
                    spillOffset += 8
                    sorted[i].spillSlot = spillOffset
                } else if let reg = pickReg(from: &freeSSE, spansCall: current.spansCall,
                                     isFloat: true,
                                     interval: current, fixedIntervals: fixedIntervals) {
                    sorted[i].reg = reg
                    active.append(i)
                    active.sort { sorted[$0].end < sorted[$1].end }
                } else {
                    // Spill
                    spill(&sorted, index: i, active: &active, freePool: &freeSSE,
                          spillOffset: &spillOffset)
                }
            } else {
                if let reg = pickReg(from: &freeGP, spansCall: current.spansCall,
                                     isFloat: false,
                                     interval: current, fixedIntervals: fixedIntervals) {
                    sorted[i].reg = reg
                    if PhysReg.calleeSavedGP.contains(reg) { usedCalleeSaved.insert(reg) }
                    active.append(i)
                    active.sort { sorted[$0].end < sorted[$1].end }
                } else {
                    // Spill
                    spill(&sorted, index: i, active: &active, freePool: &freeGP,
                          spillOffset: &spillOffset)
                }
            }
        }

        // 6b. Stack slot coloring — reuse slots whose live intervals don't overlap
        let baseStackSize = function.stackSize
        let spilledIndices = sorted.indices.filter { sorted[$0].spillSlot != nil }
            .sorted { sorted[$0].start < sorted[$1].start }
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


        // 7. Build vreg → assignment map
        var assignMap: [Int: PhysReg] = [:]
        var spillMap: [Int: Int32] = [:]
        var rematMap: [Int: Instr] = [:]
        for iv in sorted {
            if let r = iv.reg {
                assignMap[iv.vreg] = r
            }
            if let s = iv.spillSlot {
                spillMap[iv.vreg] = s
                // Rematerializable spilled vregs: recompute instead of reload from stack.
                if let ri = iv.rematInstr { rematMap[iv.vreg] = ri }
            }
        }

        // 7b. Propagate coalesced allocations to all member vregs.
        for v in originalVregs {
            let rep = coalescingUF.find(v)
            guard rep != v else { continue }
            if let r = assignMap[rep] { assignMap[v] = r }
            if let s = spillMap[rep]  { spillMap[v] = s }
            if let ri = rematMap[rep] { rematMap[v] = ri }
        }

        // 8. Rewrite instructions
        for bi in function.blocks.indices {
            var newInstrs: [Instr] = []
            for instr in function.blocks[bi].instructions {
                // Special handling for pcopy: spilled vregs are replaced with their
                // spill slot memory operands directly, avoiding scratch register conflicts
                // when multiple float vregs are spilled in the same pcopy.
                if case .pcopy(let copies) = instr {
                    let rewrittenCopies = copies.map { copy -> (src: Operand, dst: Operand, sz: Size) in
                        var src = copy.src
                        var dst = copy.dst
                        if case .reg(.virtual(let v)) = src {
                            if let slot = spillMap[v] {
                                src = .mem(.stack(slot))
                            } else if let phys = assignMap[v] {
                                src = .reg(.physical(phys))
                            }
                        }
                        if case .reg(.virtual(let v)) = dst {
                            if let slot = spillMap[v] {
                                dst = .mem(.stack(slot))
                            } else if let phys = assignMap[v] {
                                dst = .reg(.physical(phys))
                            }
                        }
                        return (src: src, dst: dst, sz: copy.sz)
                    }
                    newInstrs.append(.pcopy(rewrittenCopies))
                    continue
                }

                // Insert reloads for used spilled vregs.
                // When an instruction has multiple spilled GP uses (e.g. add V11, V14 where
                // both are spilled), the second unique spilled vreg gets gpScratch2 (r10)
                // to avoid the two-address conflict where both uses would otherwise share r11.
                let used = usesOf(instr)
                var reloadMap: [Int: PhysReg] = [:]
                var gpScratchUsed = false
                for reg in used {
                    if case .virtual(let v) = reg, let slot = spillMap[v],
                       reloadMap[v] == nil {
                        let scratch: PhysReg
                        if isFloatVreg(v, sorted) {
                            scratch = Self.sseScratch
                        } else if !gpScratchUsed {
                            scratch = Self.gpScratch
                            gpScratchUsed = true
                        } else {
                            scratch = Self.gpScratch2
                        }
                        // Rematerialization: recompute cheap values instead of loading from stack
                        if let ri = rematMap[v] {
                            newInstrs.append(emitRemat(ri, scratch: scratch))
                        } else if isFloatVreg(v, sorted) {
                            newInstrs.append(.xmmMovMR(.double_, src: .stack(slot),
                                                       dst: .physical(scratch)))
                        } else {
                            newInstrs.append(.movMR(.qword, src: .stack(slot),
                                                   dst: .physical(scratch)))
                        }
                        reloadMap[v] = scratch
                    }
                }

                // Build def rewrite map: spilled defs go through scratch register.
                // If the def vreg was already assigned a scratch as a use (two-address),
                // keep that scratch. Otherwise use the primary scratch.
                let defined = defsOf(instr)
                for reg in defined {
                    if case .virtual(let v) = reg, spillMap[v] != nil, reloadMap[v] == nil {
                        let scratch: PhysReg = isFloatVreg(v, sorted) ? Self.sseScratch : Self.gpScratch
                        reloadMap[v] = scratch
                    }
                }

                // Rewrite the instruction (both uses and defs through scratch)
                let rewritten = rewriteInstr(instr, assignMap: assignMap, reloadMap: reloadMap)
                // Eliminate redundant copies (same src == dst after coalescing)
                if !isRedundantCopy(rewritten) {
                    newInstrs.append(rewritten)
                }

                // Insert stores for defined spilled vregs using the scratch assigned above.
                // Skip store for rematerializable values — they'll be recomputed on reload.
                for reg in defined {
                    if case .virtual(let v) = reg, let slot = spillMap[v], rematMap[v] == nil {
                        let scratch: PhysReg = reloadMap[v] ?? (isFloatVreg(v, sorted) ? Self.sseScratch : Self.gpScratch)
                        if isFloatVreg(v, sorted) {
                            newInstrs.append(.xmmMovRM(.double_, src: .physical(scratch),
                                                       dst: .stack(slot)))
                        } else {
                            newInstrs.append(.movRM(.qword, src: .physical(scratch),
                                                   dst: .stack(slot)))
                        }
                    }
                }
            }
            function.blocks[bi].instructions = newInstrs
        }

        // 8b. Rewrite Machine phi nodes (dest + arg srcs → physical regs or spill slots).
        for bi in function.blocks.indices {
            for pi in function.blocks[bi].phis.indices {
                if case .virtual(let v) = function.blocks[bi].phis[pi].dest,
                   let phys = assignMap[v] {
                    function.blocks[bi].phis[pi].dest = .physical(phys)
                }
                function.blocks[bi].phis[pi].args = function.blocks[bi].phis[pi].args.map { arg in
                    (label: arg.label, src: rewriteOperand(arg.src, assignMap: assignMap, spillMap: spillMap))
                }
            }
        }

        // 9a. Phi elimination: convert Machine phi nodes to parallel copies in predecessors.
        // Must run BEFORE adjustStackOffsets so inserted instructions get the csShift applied.
        eliminateMachinePhis(&function, spillMap: spillMap)

        // 9b. Expand prologue/epilogue
        let calleeSaved = Array(usedCalleeSaved).sorted { $0.rawValue < $1.rawValue }
        function.calleeSaved = calleeSaved

        // Callee-saved pushes occupy space between rbp and the local frame.
        // Adjust all stack-relative (rbp-based) memory operands to account for this.
        let csShift = Int32(calleeSaved.count * 8)
        if csShift > 0 {
            adjustStackOffsets(&function, by: csShift)
        }

        // Adjust stack size: original + spill area + callee-saved area, aligned to 16
        let totalStack = spillOffset + csShift
        // Account for return address + rbp push + callee-saved pushes.
        // The return address is already on the stack at function entry.
        let pushCount = calleeSaved.count + 2  // +1 for rbp, +1 for return address
        let frameAdjust = totalStack
        // Ensure 16-byte alignment of the entire frame
        let totalPushed = Int32(pushCount * 8)
        let aligned = alignUp(frameAdjust, to: 16, considering: totalPushed)
        function.stackSize = aligned

        expandPrologueEpilogue(&function, calleeSaved: calleeSaved, stackAdj: aligned)

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
                         fixedIntervals: [PhysReg: [(start: Int, end: Int)]]) -> PhysReg? {
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

        if spansCall {
            // MUST use callee-saved register — caller-saved would be clobbered by the call.
            if let idx = viable.first(where: { PhysReg.calleeSavedGP.contains(pool[$0]) }) {
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
        // When the current interval spans a call, only consider evicting intervals
        // that hold callee-saved registers (caller-saved would be clobbered).
        let candidates: [Int]
        if intervals[i].spansCall && !intervals[i].isFloat {
            candidates = active.filter {
                if let r = intervals[$0].reg { return PhysReg.calleeSavedGP.contains(r) }
                return false
            }
        } else {
            candidates = active
        }
        let evictIdx = candidates.min(by: { intervals[$0].spillWeight < intervals[$1].spillWeight })
        let currentWeight = intervals[i].spillWeight
        if let eidx = evictIdx, intervals[eidx].spillWeight < currentWeight {
            // Evict the cheapest active interval, give its register to current
            let stolen = intervals[eidx].reg!
            intervals[i].reg = stolen
            spillOffset += 8
            intervals[eidx].spillSlot = spillOffset
            intervals[eidx].reg = nil
            active.removeAll { $0 == eidx }
            active.append(i)
            active.sort { intervals[$0].end < intervals[$1].end }
        } else {
            // Spill current interval
            spillOffset += 8
            intervals[i].spillSlot = spillOffset
        }
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
                    // Only adjust rbp-based stack references (negative displacement)
                    if case .physical(.rbp) = mem.base, mem.symbol == nil,
                       mem.displacement < 0 {
                        var m = mem
                        m.displacement -= shift
                        return m
                    }
                    return mem
                }
            }
        }
    }

    // MARK: - Prologue / Epilogue expansion

    private func expandPrologueEpilogue(_ function: inout Function,
                                         calleeSaved: [PhysReg],
                                         stackAdj: Int32) {
        for bi in function.blocks.indices {
            var expanded: [Instr] = []
            for instr in function.blocks[bi].instructions {
                switch instr {
                case .prologue:
                    expanded.append(.push(.qword, .reg(.physical(.rbp))))
                    expanded.append(.movRR(.qword, src: .physical(.rsp),
                                           dst: .physical(.rbp)))
                    for r in calleeSaved {
                        expanded.append(.push(.qword, .reg(.physical(r))))
                    }
                    if stackAdj > 0 {
                        expanded.append(.aluRmiR(.sub, .qword, src: .imm(Int64(stackAdj)),
                                                 dst: .physical(.rsp)))
                    }

                case .epilogue:
                    if stackAdj > 0 {
                        expanded.append(.aluRmiR(.add, .qword, src: .imm(Int64(stackAdj)),
                                                 dst: .physical(.rsp)))
                    }
                    for r in calleeSaved.reversed() {
                        expanded.append(.pop(.qword, .physical(r)))
                    }
                    expanded.append(.pop(.qword, .physical(.rbp)))

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

    private func isFloatVreg(_ v: Int, _ intervals: [LiveInterval]) -> Bool {
        return intervals.first(where: { $0.vreg == v })?.isFloat ?? false
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
