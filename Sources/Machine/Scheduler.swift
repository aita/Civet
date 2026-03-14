/// Post-register-allocation list scheduling for basic blocks.
/// Reorders instructions within barrier-delimited regions to hide latencies.
public func schedule(_ program: Program) -> Program {
    var result = program
    for i in result.functions.indices {
        result.functions[i] = scheduleFunction(result.functions[i])
    }
    return result
}

private func scheduleFunction(_ f: Function) -> Function {
    var f = f
    for bi in f.blocks.indices {
        f.blocks[bi].instructions = scheduleBlock(f.blocks[bi].instructions)
    }
    return f
}

// MARK: - Block scheduling

/// Split a block at barriers, schedule each region independently, reassemble.
private func scheduleBlock(_ instrs: [Instr]) -> [Instr] {
    guard instrs.count > 1 else { return instrs }

    // Find all barriers. Then for any region between a flag-defining barrier
    // (cmp/test) and a flag-using barrier (jcc/setcc/cmovcc), all flag-clobbering
    // instructions in that region must also be treated as barriers to prevent
    // them from overwriting the flags that the next barrier expects.
    var barrierSet: Set<Int> = []
    for i in instrs.indices {
        if isBarrier(instrs[i]) {
            barrierSet.insert(i)
        }
    }

    // Second pass: for each flag-using barrier, if the previous barrier
    // defines flags, mark all flag-clobbering instructions between them.
    var prevBarrier: Int = -1
    for i in instrs.indices {
        if barrierSet.contains(i) {
            if usesFlags(instrs[i]) && prevBarrier >= 0 && defsFlags(instrs[prevBarrier]) {
                // All flag-clobbering instructions in (prevBarrier, i) must be barriers.
                for j in (prevBarrier + 1)..<i {
                    if defsFlags(instrs[j]) {
                        barrierSet.insert(j)
                    }
                }
            }
            prevBarrier = i
        }
    }

    var result: [Instr] = []
    result.reserveCapacity(instrs.count)
    var regionStart = 0

    for i in instrs.indices {
        if barrierSet.contains(i) {
            if i > regionStart {
                result.append(contentsOf: scheduleRegion(Array(instrs[regionStart..<i])))
            }
            result.append(instrs[i])
            regionStart = i + 1
        }
    }
    // Schedule trailing region
    if regionStart < instrs.count {
        result.append(contentsOf: scheduleRegion(Array(instrs[regionStart...])))
    }

    return result
}

// MARK: - List scheduling core

private func scheduleRegion(_ instrs: [Instr]) -> [Instr] {
    let n = instrs.count
    guard n > 1 else { return instrs }

    // Build dependency graph
    var succs: [[Edge]] = Array(repeating: [], count: n)  // successors
    var predCount: [Int] = Array(repeating: 0, count: n)

    buildDependencyGraph(instrs, succs: &succs, predCount: &predCount)

    // Compute priority = longest path from node to any exit (bottom-up critical path)
    var priority = Array(repeating: 0, count: n)
    computePriorities(instrs, succs: succs, priority: &priority)

    // List scheduling: pick ready nodes by priority (descending)
    var scheduled: [Int] = []
    scheduled.reserveCapacity(n)

    var remainingPreds = predCount
    // Collect initially ready nodes
    var ready: [Int] = []
    for i in 0..<n {
        if remainingPreds[i] == 0 {
            ready.append(i)
        }
    }

    while !ready.isEmpty {
        // Pick highest priority
        ready.sort { priority[$0] > priority[$1] }
        let best = ready.removeFirst()
        scheduled.append(best)

        // Release successors
        for edge in succs[best] {
            remainingPreds[edge.to] -= 1
            if remainingPreds[edge.to] == 0 {
                ready.append(edge.to)
            }
        }
    }

    // If we missed any (shouldn't happen), append in original order
    if scheduled.count < n {
        let scheduledSet = Set(scheduled)
        for i in 0..<n where !scheduledSet.contains(i) {
            scheduled.append(i)
        }
    }

    return scheduled.map { instrs[$0] }
}

// MARK: - Dependency graph

private struct Edge {
    let to: Int
    let latency: Int
}

private func buildDependencyGraph(_ instrs: [Instr],
                                   succs: inout [[Edge]],
                                   predCount: inout [Int]) {
    let n = instrs.count

    // Track last writer/readers per physical register for dependency edges
    // Using a dictionary keyed by PhysReg raw value
    var lastWriter: [PhysReg: Int] = [:]    // reg → last instruction that wrote it
    var lastReaders: [PhysReg: [Int]] = [:] // reg → instructions that read it since last write

    // Flags tracking (virtual "register")
    var lastFlagWriter: Int = -1
    var lastFlagReaders: [Int] = []

    // Memory tracking (conservative: all stores/loads ordered)
    var lastMemWrite: Int = -1
    var lastMemReads: [Int] = []

    for i in 0..<n {
        let instr = instrs[i]
        let defs = physDefs(instr)
        let uses = physUses(instr)
        let defFlags = defsFlags(instr)
        let useFlags = usesFlags(instr)
        let memAccess = memoryAccess(instr)

        // Register dependencies
        for reg in uses {
            // RAW: writer → reader
            if let w = lastWriter[reg] {
                addEdge(from: w, to: i, latency: latency(instrs[w]),
                        succs: &succs, predCount: &predCount)
            }
        }

        for reg in defs {
            // WAR: readers → writer
            if let readers = lastReaders[reg] {
                for r in readers {
                    addEdge(from: r, to: i, latency: 1,
                            succs: &succs, predCount: &predCount)
                }
            }
            // WAW: writer → writer
            if let w = lastWriter[reg] {
                addEdge(from: w, to: i, latency: latency(instrs[w]),
                        succs: &succs, predCount: &predCount)
            }
        }

        // Flags dependencies
        if useFlags {
            if lastFlagWriter >= 0 {
                addEdge(from: lastFlagWriter, to: i, latency: latency(instrs[lastFlagWriter]),
                        succs: &succs, predCount: &predCount)
            }
            lastFlagReaders.append(i)
        }

        if defFlags {
            // WAR: flag readers → this writer
            for r in lastFlagReaders {
                addEdge(from: r, to: i, latency: 1,
                        succs: &succs, predCount: &predCount)
            }
            // WAW: previous flag writer → this writer
            if lastFlagWriter >= 0 {
                addEdge(from: lastFlagWriter, to: i, latency: latency(instrs[lastFlagWriter]),
                        succs: &succs, predCount: &predCount)
            }
            lastFlagWriter = i
            lastFlagReaders = []
        }

        // Memory dependencies (conservative)
        if memAccess.read {
            if lastMemWrite >= 0 {
                addEdge(from: lastMemWrite, to: i, latency: latency(instrs[lastMemWrite]),
                        succs: &succs, predCount: &predCount)
            }
            lastMemReads.append(i)
        }
        if memAccess.write {
            // WAR: mem readers → this store
            for r in lastMemReads {
                addEdge(from: r, to: i, latency: 1,
                        succs: &succs, predCount: &predCount)
            }
            // WAW: previous store → this store
            if lastMemWrite >= 0 {
                addEdge(from: lastMemWrite, to: i, latency: latency(instrs[lastMemWrite]),
                        succs: &succs, predCount: &predCount)
            }
            lastMemWrite = i
            lastMemReads = []
        }

        // Update register tracking
        for reg in defs {
            lastWriter[reg] = i
            lastReaders[reg] = []
        }
        for reg in uses {
            lastReaders[reg, default: []].append(i)
        }
    }
}

/// Add a dependency edge, avoiding duplicates (keep max latency).
private func addEdge(from: Int, to: Int, latency: Int,
                     succs: inout [[Edge]], predCount: inout [Int]) {
    guard from != to else { return }
    // Check if edge already exists
    if let idx = succs[from].firstIndex(where: { $0.to == to }) {
        if succs[from][idx].latency < latency {
            succs[from][idx] = Edge(to: to, latency: latency)
        }
        return
    }
    succs[from].append(Edge(to: to, latency: latency))
    predCount[to] += 1
}

// MARK: - Priority computation

/// Bottom-up longest path (critical path heuristic).
private func computePriorities(_ instrs: [Instr], succs: [[Edge]],
                                priority: inout [Int]) {
    let n = instrs.count
    // Process in reverse topological order (reverse index as approximation)
    for i in stride(from: n - 1, through: 0, by: -1) {
        var maxSucc = 0
        for edge in succs[i] {
            maxSucc = max(maxSucc, edge.latency + priority[edge.to])
        }
        priority[i] = maxSucc + latency(instrs[i])
    }
}

// MARK: - Latency model

/// Approximate result-ready latencies in cycles for Intel Skylake/Ice Lake.
/// Source: Agner Fog's instruction tables (https://www.agner.org/optimize/)
///
/// These are register-to-register latencies. Memory operands add ~4-5 cycles
/// (L1 hit) but we don't distinguish that here for simplicity.
private func latency(_ instr: Instr) -> Int {
    switch instr {
    case .movRR, .movRM, .movMR, .movIR, .movIM, .movMM,
         .movsxRmR, .movzxRmR, .lea:       return 1  // may be 0 via register renaming
    case .push, .pop:                       return 1
    case .aluRmiR, .unaryRm:               return 1
    case .shiftR:                           return 1
    case .cmpRmiR:                          return 1
    case .setcc:                            return 1
    case .cmove:                            return 1
    case .imul:                             return 3  // Skylake: 3
    case .signExtendData:                   return 1
    case .gpDiv:                            return 20 // Skylake: 26-90+ depending on size
    case .xmmMovRR, .xmmMovRM, .xmmMovMR:  return 1
    case .xmmRmR(let op, _, _, _):
        switch op {
        case .add, .sub:                    return 4  // Skylake: 4
        case .mul:                          return 5  // Skylake: 4, conservative
        case .div:
            // divss ~11, divsd ~14; we don't distinguish size here, use conservative
            return 14
        }
    case .xmmCmp:                          return 3  // Skylake: 2-3
    case .cvt:                              return 4  // Skylake: 4-5
    case .jmp, .jmpIf, .jmpIndirect, .ret, .tailCall: return 1
    case .call:                             return 1
    case .prologue, .epilogue, .inlineAsm: return 1
    case .pcopy:
        fatalError("pcopy must be expanded before scheduling")
    case .idivRemSeq:
        fatalError("pseudo-instructions must be expanded before scheduling")
    }
}

// MARK: - Barrier detection

private func isBarrier(_ instr: Instr) -> Bool {
    switch instr {
    case .call, .ret, .jmp, .jmpIf, .jmpIndirect, .tailCall: return true
    case .push, .pop:                            return true
    case .signExtendData:                        return true
    case .gpDiv:                                 return true
    // Compare/test are barriers to prevent flag-clobbering instructions
    // from being scheduled between them and a subsequent jcc.
    case .cmpRmiR, .xmmCmp:                      return true
    // Shifts with %cl must not be separated from the preceding mov→rcx
    case .shiftR(_, _, let src, _):
        if case .reg(.physical(.rcx)) = src { return true }
        return false
    case .inlineAsm, .prologue, .epilogue:       return true
    default:
        // Any instruction that writes rsp or rbp is a barrier (e.g. sub rsp for stack frame).
        if writesStackPointer(instr) { return true }
        return false
    }
}

/// Check if an instruction writes to rsp or rbp (stack frame registers).
private func writesStackPointer(_ instr: Instr) -> Bool {
    for reg in physDefs(instr) {
        if reg == .rsp || reg == .rbp { return true }
    }
    return false
}

// MARK: - Physical register defs/uses for scheduling

/// Physical registers defined by an instruction.
private func physDefs(_ instr: Instr) -> [PhysReg] {
    switch instr {
    case .movRR(_, _, let dst), .movMR(_, _, let dst), .movIR(_, _, let dst):
        if case .physical(let p) = dst { return [p] }
        return []
    case .movRM, .movIM, .movMM:
        return []
    case .movsxRmR(_, _, _, let dst), .movzxRmR(_, _, _, let dst):
        if case .physical(let p) = dst { return [p] }
        return []
    case .lea(_, _, let dst):
        return physRegsOf(dst)
    case .pop(_, let r):
        return physRegsOf(r)

    case .aluRmiR(_, _, _, let dst), .imul(_, _, let dst):
        return physRegsOf(dst)
    case .unaryRm(_, _, let r):
        return physRegsOf(r)
    case .signExtendData:
        return [.rdx]
    case .gpDiv:
        return [.rax, .rdx]

    case .shiftR(_, _, _, let dst):
        return physRegsOf(dst)

    case .cmpRmiR:
        return []  // only flags
    case .setcc(_, let r):
        return physRegsOf(r)
    case .cmove(_, _, _, let dst):
        return physRegsOf(dst)

    case .call:
        return PhysReg.callerSavedGP + PhysReg.allSSE
    case .jmp, .jmpIf, .jmpIndirect, .ret, .tailCall:
        return []

    case .xmmMovRR(_, _, let dst), .xmmMovMR(_, _, let dst):
        if case .physical(let p) = dst { return [p] }
        return []
    case .xmmMovRM:
        return []
    case .xmmRmR(_, _, _, let dst):
        return physRegsOf(dst)
    case .xmmCmp:
        return []
    case .cvt(_, _, _, let dst):
        return physRegsOf(dst)

    case .push, .prologue, .epilogue, .inlineAsm:
        return []
    case .pcopy:
        fatalError("pcopy must be expanded before scheduling")
    case .idivRemSeq:
        fatalError("pseudo-instructions must be expanded before scheduling")
    }
}

/// Physical registers used by an instruction.
private func physUses(_ instr: Instr) -> [PhysReg] {
    switch instr {
    case .movRR(_, let src, _):
        if case .physical(let p) = src { return [p] }
        return []
    case .movRM(_, let src, let dst):
        var regs: [PhysReg] = []
        if case .physical(let p) = src { regs.append(p) }
        regs.append(contentsOf: physRegsInMem(dst))
        return regs
    case .movMR(_, let src, _):
        return physRegsInMem(src)
    case .movIR:
        return []
    case .movIM(_, _, let dst):
        return physRegsInMem(dst)
    case .movMM(_, let src, let dst):
        return physRegsInMem(src) + physRegsInMem(dst)
    case .movsxRmR(_, _, let src, _), .movzxRmR(_, _, let src, _):
        return physRegsOf(src)
    case .lea(_, let src, _):
        return physRegsInMem(src)
    case .push(_, let op):
        return physRegsOf(op)
    case .pop:
        return []

    case .aluRmiR(_, _, let src, let dst), .imul(_, let src, let dst):
        return physRegsOf(src) + physRegsOf(dst)
    case .unaryRm(_, _, let r):
        return physRegsOf(r)
    case .signExtendData:
        return [.rax]
    case .gpDiv(_, let r, _):
        return physRegsOf(r) + [.rax, .rdx]

    case .shiftR(_, _, let src, let dst):
        return physRegsOf(src) + physRegsOf(dst)

    case .cmpRmiR(_, _, let src, let dst):
        return physRegsOf(src) + physRegsOf(dst)

    case .setcc:
        return []  // reads flags only
    case .cmove(_, _, let src, let dst):
        return physRegsOf(src) + physRegsOf(dst)

    case .call(let op):
        return physRegsOf(op)
    case .jmpIndirect(let r):
        return physRegsOf(r)
    case .tailCall(let op):
        return physRegsOf(op)
    case .jmp, .jmpIf, .ret:
        return []

    case .xmmMovRR(_, let src, _):
        if case .physical(let p) = src { return [p] }
        return []
    case .xmmMovRM(_, let src, let dst):
        var regs: [PhysReg] = []
        if case .physical(let p) = src { regs.append(p) }
        regs.append(contentsOf: physRegsInMem(dst))
        return regs
    case .xmmMovMR(_, let src, _):
        return physRegsInMem(src)
    case .xmmRmR(_, _, let src, let dst):
        return physRegsOf(src) + physRegsOf(dst)
    case .xmmCmp(_, let src, let dst):
        return physRegsOf(src) + physRegsOf(dst)
    case .cvt(_, _, let src, _):
        return physRegsOf(src)

    case .prologue, .epilogue, .inlineAsm:
        return []
    case .pcopy:
        fatalError("pcopy must be expanded before scheduling")
    case .idivRemSeq:
        fatalError("pseudo-instructions must be expanded before scheduling")
    }
}

// MARK: - Flags tracking

/// Is this a compare or test instruction (intentional flag setter for branches)?
private func isCompareOrTest(_ instr: Instr) -> Bool {
    switch instr {
    case .cmpRmiR, .xmmCmp: return true
    default: return false
    }
}

/// Does this instruction define (write) the flags register?
private func defsFlags(_ instr: Instr) -> Bool {
    switch instr {
    case .aluRmiR, .imul, .unaryRm:        return true
    case .shiftR:                           return true
    case .cmpRmiR, .xmmCmp:                return true
    case .gpDiv:                            return true
    default:                               return false
    }
}

/// Does this instruction use (read) the flags register?
private func usesFlags(_ instr: Instr) -> Bool {
    switch instr {
    case .setcc:   return true
    case .cmove:   return true
    case .jmpIf:   return true
    default:       return false
    }
}

// MARK: - Memory access tracking

private func memoryAccess(_ instr: Instr) -> (read: Bool, write: Bool) {
    switch instr {
    case .movRR, .movIR:
        return (read: false, write: false)
    case .movMR:
        return (read: true, write: false)
    case .movRM, .movIM:
        return (read: false, write: true)
    case .movMM:
        return (read: true, write: true)
    case .movsxRmR(_, _, let src, _), .movzxRmR(_, _, let src, _):
        return (read: isMem(src), write: false)
    case .lea:
        return (read: false, write: false)  // lea doesn't access memory
    case .push:
        return (read: false, write: true)
    case .pop:
        return (read: true, write: false)

    case .aluRmiR(_, _, let src, _), .imul(_, let src, _):
        return (read: isMem(src), write: false)
    case .shiftR:
        return (read: false, write: false)
    case .unaryRm:
        return (read: false, write: false)

    case .cmpRmiR(_, _, let src, _):
        return (read: isMem(src), write: false)

    case .xmmMovRR:
        return (read: false, write: false)
    case .xmmMovMR:
        return (read: true, write: false)
    case .xmmMovRM:
        return (read: false, write: true)
    case .xmmRmR(_, _, let src, _):
        return (read: isMem(src), write: false)
    case .xmmCmp(_, let src, _):
        return (read: isMem(src), write: false)
    case .cvt(_, _, let src, _):
        return (read: isMem(src), write: false)

    default:
        return (read: false, write: false)
    }
}

private func isMem(_ op: Operand) -> Bool {
    if case .mem = op { return true }
    return false
}

// MARK: - Operand helpers

/// Extract physical register from a Reg.
private func physRegsOf(_ r: Reg) -> [PhysReg] {
    if case .physical(let p) = r { return [p] }
    return []
}

/// Extract physical register from an operand (register or memory base/index).
private func physRegsOf(_ op: Operand) -> [PhysReg] {
    switch op {
    case .reg(let r):
        if case .physical(let p) = r { return [p] }
        return []
    case .mem(let m):
        return physRegsInMem(m)
    case .imm, .label:
        return []
    }
}

/// Extract physical registers from memory base/index.
private func physRegsInMem(_ op: Operand) -> [PhysReg] {
    guard case .mem(let m) = op else { return [] }
    return physRegsInMem(m)
}

private func physRegsInMem(_ m: Memory) -> [PhysReg] {
    var result: [PhysReg] = []
    if case .physical(let p) = m.base { result.append(p) }
    if case .physical(let p) = m.index { result.append(p) }
    return result
}
