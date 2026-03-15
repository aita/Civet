/// Peephole optimizations on Machine IR (post register allocation).
public func peephole(_ program: Program) -> Program {
    var result = program
    for i in result.functions.indices {
        result.functions[i] = peepholeFunction(result.functions[i])
    }
    return result
}

private func peepholeFunction(_ f: Function) -> Function {
    var f = f
    // Tail call optimization (run once before the main loop)
    _ = tailCallOptimize(&f)

    // Run until no more changes
    var changed = true
    while changed {
        changed = false
        for bi in f.blocks.indices {
            let before = f.blocks[bi].instructions.count
            f.blocks[bi].instructions = peepholeBlock(f.blocks[bi].instructions)
            if f.blocks[bi].instructions.count != before { changed = true }
        }

        // Inter-block: jcc+jmp → inverted jcc when fallthrough
        let blockChanged = simplifyBranches(&f)
        if blockChanged { changed = true }

        // If-conversion: diamond CFG → cmov (eliminates branch misprediction)
        let ifChanged = ifConvert(&f)
        if ifChanged { changed = true }

        // Remove empty blocks (no instructions) by redirecting jumps
        let emptyChanged = removeEmptyBlocks(&f)
        if emptyChanged { changed = true }
    }

    return f
}

// MARK: - Intra-block peephole

private func peepholeBlock(_ instrs: [Instr]) -> [Instr] {
    var out: [Instr] = []
    out.reserveCapacity(instrs.count)

    var skip = false
    for i in instrs.indices {
        if skip { skip = false; continue }
        let instr = instrs[i]

        // 1. Remove nop movs: mov %r, %r (same register, same size)
        if case .movRR(_, let src, let dst) = instr, src == dst {
            continue
        }
        if case .xmmMovRR(_, let src, let dst) = instr, src == dst {
            continue
        }

        // 2. Remove add/sub $0
        if case .aluRmiR(.add, _, let src, _) = instr, isZeroImm(src) {
            continue
        }
        if case .aluRmiR(.sub, _, let src, _) = instr, isZeroImm(src) {
            continue
        }

        // 2b. mov $0, %reg → xor %reg, %reg (zeroing idiom)
        // Safe only when flags are dead (no flags consumer before next flags def).
        if case .movIR(let sz, let v, let dst) = instr,
           v == 0,
           (sz == .dword || sz == .qword),
           !flagsLiveAfter(instrs, from: i) {
            let xorSz: Size = sz == .qword ? .dword : sz  // xor %e??, %e?? zero-extends to 64-bit
            out.append(.aluRmiR(.xor, xorSz, src: .reg(dst), dst: dst))
            continue
        }

        // 2c. cmp $0, %reg → test %reg, %reg (shorter encoding, identical flags)
        if case .cmpRmiR(.cmp, let sz, let src, let dst) = instr,
           isZeroImm(src) {
            out.append(.cmpRmiR(.test, sz, src: .reg(dst), dst: dst))
            continue
        }

        // 3. LEA copy+add folding:
        //    movRR(r1, r2); aluRmiR(.add, .imm(c), r2) → lea c(r1), r2
        //    movRR(r1, r2); aluRmiR(.add, .reg(r3), r2) → lea (r1, r3), r2
        //    movRR(r1, r2); aluRmiR(.sub, .imm(c), r2) → lea -c(r1), r2
        if case .movRR(let sz, let r1, let r2) = instr,
           r1 != r2,
           (sz == .dword || sz == .qword),
           i + 1 < instrs.count {
            let next = instrs[i + 1]
            switch next {
            case .aluRmiR(.add, sz, .imm(let c), r2)
                where c >= Int64(Int32.min) && c <= Int64(Int32.max)
                   && !flagsLiveAfter(instrs, from: i + 1):
                out.append(.lea(sz, src: Memory(base: r1, displacement: Int32(c)), dst: r2))
                skip = true
                continue
            case .aluRmiR(.add, sz, .reg(let r3), r2)
                where !flagsLiveAfter(instrs, from: i + 1):
                out.append(.lea(sz, src: Memory(base: r1, index: r3), dst: r2))
                skip = true
                continue
            case .aluRmiR(.sub, sz, .imm(let c), r2)
                where c > Int64(Int32.min) && c <= Int64(Int32.max)
                   && !flagsLiveAfter(instrs, from: i + 1):
                out.append(.lea(sz, src: Memory(base: r1, displacement: Int32(-c)), dst: r2))
                skip = true
                continue
            default:
                break
            }
        }

        // 3b. Address mode folding:
        //    movMR(sz, mem, r1); aluRmiR(op, sz, .reg(r1), dst) where r1 ≠ dst, r1 dead
        //    → aluRmiR(op, sz, .mem(mem), dst)
        //    Also: movMR(sz, mem, r1); cmpRmiR(op, sz, .reg(r1), dst) where r1 dead
        //    → cmpRmiR(op, sz, .mem(mem), dst)
        if case .movMR(let sz, let mem, let r1) = instr,
           (sz == .dword || sz == .qword),
           i + 1 < instrs.count {
            let next = instrs[i + 1]
            switch next {
            case .aluRmiR(let op, sz, .reg(r1), let dst)
                where r1 != dst && !regLiveAfter(instrs, from: i + 1, reg: r1):
                out.append(.aluRmiR(op, sz, src: .mem(mem), dst: dst))
                skip = true
                continue
            case .cmpRmiR(let op, sz, .reg(r1), let dst)
                where r1 != dst && !regLiveAfter(instrs, from: i + 1, reg: r1):
                out.append(.cmpRmiR(op, sz, src: .mem(mem), dst: dst))
                skip = true
                continue
            default:
                break
            }
        }

        // 4. Fold movsx/movzx where src == dst and sizes make it a nop
        //    (e.g. movzx from dword to dword)
        if case .movsxRmR(let from, let to, let src, let dst) = instr,
           from == to, sameOperand(src, .reg(dst)) {
            continue
        }
        if case .movzxRmR(let from, let to, let src, let dst) = instr,
           from == to, sameOperand(src, .reg(dst)) {
            continue
        }

        // 5. Redundant movzx elimination:
        //    32-bit reg write auto-zeroes upper 32 bits on x86-64.
        //    movzxRmR(.dword, .qword, .reg(r), r) after dword def of r → remove
        //    setcc(_, r); movzxRmR(.byte, .dword, .reg(r), r) → remove movzx
        if case .movzxRmR(let from, let to, .reg(let src), let dst) = instr,
           src == dst, !out.isEmpty {
            let prev = out[out.count - 1]
            if let (defR, defSz) = defRegAndSize(prev), defR == dst {
                // dword def → movzx dword→qword: implicit zero-extend
                if from == .dword && to == .qword && defSz == .dword {
                    continue
                }
                // NOTE: setcc only writes the low byte and does NOT zero upper bytes.
                // movzx after setcc is NOT redundant — it's needed to zero-extend.
            }
        }

        // 6. Store-load forwarding (extended):
        //    movRM(sz, src: r1, dst: mem); ...; movMR(sz, src: mem', dst: r2) where mem == mem'
        //    → replace load with movRR(sz, src: r1, dst: r2)
        //    Scans backward through non-aliasing instructions (max 8).
        if case .movMR(let sz, let mem, let dst) = instr, !out.isEmpty {
            var forwarded = false
            for j in stride(from: out.count - 1, through: max(0, out.count - 8), by: -1) {
                let prev = out[j]
                if case .movRM(let sz2, let src, let mem2) = prev, sz == sz2, mem == mem2 {
                    // Check that src register and memory base/index haven't been
                    // redefined between store and load
                    var clobbered = false
                    for k in (j + 1)..<out.count {
                        if let (defR, _) = defRegAndSize(out[k]) {
                            if defR == src { clobbered = true; break }
                            if let b = mem.base, defR == b { clobbered = true; break }
                            if let idx = mem.index, defR == idx { clobbered = true; break }
                        }
                    }
                    if !clobbered {
                        if src == dst {
                            forwarded = true  // store then load to same reg = nop
                        } else {
                            out.append(.movRR(sz, src: src, dst: dst))
                            forwarded = true
                        }
                    }
                    break
                }
                // Stop if an intervening instruction writes to the same memory
                if instrMayWriteMemory(prev, mem) { break }
                // Stop if an intervening instruction redefines the memory's base/index
                if let (defR, _) = defRegAndSize(prev) {
                    if let b = mem.base, defR == b { break }
                    if let idx = mem.index, defR == idx { break }
                }
            }
            if forwarded { continue }
        }

        // 7. inc/dec: add $1 → inc, sub $1 → dec (shorter encoding)
        //    Note: inc/dec don't modify CF, but Civet never uses CF (no adc/sbb).
        if case .aluRmiR(.add, let sz, .imm(1), let dst) = instr,
           !flagsLiveAfter(instrs, from: i) {
            out.append(.unaryRm(.inc, sz, dst))
            continue
        }
        if case .aluRmiR(.sub, let sz, .imm(1), let dst) = instr,
           !flagsLiveAfter(instrs, from: i) {
            out.append(.unaryRm(.dec, sz, dst))
            continue
        }

        // 7a. xor zeroing: mov $0, %reg → xor %reg, %reg (shorter encoding, breaks dep chain)
        //     Only safe when flags are not live (xor clobbers ZF/SF/PF/OF/CF).
        if case .movIR(let sz, 0, let dst) = instr,
           (sz == .dword || sz == .qword),
           !flagsLiveAfter(instrs, from: i) {
            // xorl %r32, %r32 implicitly zero-extends to 64-bit — use .dword always
            out.append(.aluRmiR(.xor, .dword, src: .reg(dst), dst: dst))
            continue
        }

        // 7b. Test-Immediate fusion:
        //     and $mask, %r; test %r, %r → test $mask, %r (when and result is dead)
        if case .cmpRmiR(.test, let sz, .reg(let r), let dst) = instr,
           r == dst, !out.isEmpty {
            if case .aluRmiR(.and, sz, .imm(let mask), dst) = out[out.count - 1] {
                if !regLiveAfter(instrs, from: i, reg: dst) {
                    out[out.count - 1] = .cmpRmiR(.test, sz, src: .imm(mask), dst: dst)
                    continue
                }
            }
        }

        // 8. Redundant test elimination after ALU ops:
        //    ALU defs dst and sets ZF/SF; test dst, dst is redundant.
        //    Scan backward in out through non-flags-affecting instructions.
        if case .cmpRmiR(.test, _, .reg(let r), let dst) = instr, r == dst {
            var canEliminate = false
            for j in stride(from: out.count - 1, through: 0, by: -1) {
                let prev = out[j]
                if peepholeDefsFlags(prev) {
                    if let (defR, _) = defRegAndSize(prev), defR == dst,
                       setsZFSFOnResult(prev) {
                        canEliminate = true
                    }
                    break
                }
                // dst modified between flags-def and test → not redundant
                if let (defR, _) = defRegAndSize(prev), defR == dst {
                    break
                }
            }
            if canEliminate { continue }
        }

        // 9. Redundant store elimination:
        //    movRM(r, mem); movRM(r', mem) → remove first store
        if case .movRM(_, _, let mem) = instr, !out.isEmpty {
            if case .movRM(_, _, let mem2) = out[out.count - 1], mem == mem2 {
                out[out.count - 1] = instr
                continue
            }
        }
        if case .movIM(_, _, let mem) = instr, !out.isEmpty {
            switch out[out.count - 1] {
            case .movRM(_, _, let mem2) where mem == mem2:
                out[out.count - 1] = instr
                continue
            case .movIM(_, _, let mem2) where mem == mem2:
                out[out.count - 1] = instr
                continue
            default: break
            }
        }

        // 10. imul $3/$5/$9 → lea (1-cycle lea vs 3-cycle imul)
        //    imul $3, src, dst → lea (src, src, 2), dst
        //    imul $5, src, dst → lea (src, src, 4), dst
        //    imul $9, src, dst → lea (src, src, 8), dst
        if case .imul(let sz, .imm(let c), let dst) = instr,
           (sz == .dword || sz == .qword),
           !flagsLiveAfter(instrs, from: i) {
            let scale: Int64? = (c == 3) ? 2 : (c == 5) ? 4 : (c == 9) ? 8 : nil
            if let s = scale {
                // lea (dst, dst, scale), dst
                out.append(.lea(sz, src: Memory(base: dst, index: dst,
                                                scale: UInt8(s)), dst: dst))
                continue
            }
        }

        // 11. LEA zero-offset elimination:
        //    lea 0(%r1), %r2 → movRR %r1, %r2 (shorter encoding)
        //    lea 0(%r1), %r1 → remove (nop)
        if case .lea(let sz, let mem, let dst) = instr,
           mem.displacement == 0, mem.index == nil, mem.symbol == nil,
           let base = mem.base {
            if base == dst {
                continue  // nop
            }
            out.append(.movRR(sz, src: base, dst: dst))
            continue
        }

        out.append(instr)
    }

    return out
}

// MARK: - Inter-block branch simplification

/// Simplify branch patterns:
/// 1. jmp to next block → remove (fallthrough)
/// 2. jcc TARGET; jmp FALLTHROUGH → invert/simplify
private func simplifyBranches(_ f: inout Function) -> Bool {
    var changed = false

    for bi in f.blocks.indices {
        let instrs = f.blocks[bi].instructions
        guard !instrs.isEmpty else { continue }

        guard case .jmp(let jmpTarget) = instrs.last else { continue }
        let nextBlockIdx = bi + 1
        guard nextBlockIdx < f.blocks.count else { continue }
        let nextLabel = f.blocks[nextBlockIdx].label

        // Pattern: jmpIf(cc, target); jmp(fallthrough)
        if instrs.count >= 2,
           case .jmpIf(let cc, let jccTarget) = instrs[instrs.count - 2] {
            if jccTarget == nextLabel {
                // jmpIf next_block; jmp elsewhere → jmpIf(!cc) elsewhere
                f.blocks[bi].instructions[instrs.count - 2] = .jmpIf(cc.inverted, jmpTarget)
                f.blocks[bi].instructions.removeLast()
                changed = true
            } else if jmpTarget == nextLabel {
                // jmpIf elsewhere; jmp next_block → jmpIf elsewhere
                f.blocks[bi].instructions.removeLast()
                changed = true
            }
        } else if jmpTarget == nextLabel {
            // Standalone jmp to next block → remove (fallthrough)
            f.blocks[bi].instructions.removeLast()
            changed = true
        }
    }

    return changed
}

// MARK: - Empty block removal

/// Remove empty blocks and jmp-only blocks by rewriting jumps to them to their successor.
/// An empty block falls through to the next block; a jmp-only block contains a single jmp.
private func removeEmptyBlocks(_ f: inout Function) -> Bool {
    // Build redirect map: block label → effective target label
    var redirect: [String: String] = [:]
    for bi in f.blocks.indices {
        if f.blocks[bi].instructions.isEmpty, bi + 1 < f.blocks.count {
            // Empty block: falls through to next
            redirect[f.blocks[bi].label] = f.blocks[bi + 1].label
        } else if f.blocks[bi].instructions.count == 1,
                  case .jmp(let target) = f.blocks[bi].instructions[0],
                  f.blocks[bi].label != target {
            // Jmp-only block: redirects to target (jump threading)
            redirect[f.blocks[bi].label] = target
        }
    }
    guard !redirect.isEmpty else { return false }

    // Chase chains (A→B→C becomes A→C)
    for key in redirect.keys {
        var target = redirect[key]!
        while let next = redirect[target] {
            target = next
        }
        redirect[key] = target
    }

    // Rewrite all jump targets
    var changed = false
    for bi in f.blocks.indices {
        for ii in f.blocks[bi].instructions.indices {
            switch f.blocks[bi].instructions[ii] {
            case .jmp(let label):
                if let newLabel = redirect[label] {
                    f.blocks[bi].instructions[ii] = .jmp(newLabel)
                    changed = true
                }
            case .jmpIf(let cc, let label):
                if let newLabel = redirect[label] {
                    f.blocks[bi].instructions[ii] = .jmpIf(cc, newLabel)
                    changed = true
                }
            default:
                break
            }
        }
    }

    // Remove the empty blocks themselves
    if changed {
        f.blocks.removeAll { b in redirect.keys.contains(b.label) }
    }

    return changed
}

// MARK: - If Conversion

/// Convert simple diamond CFG patterns into cmov sequences, eliminating branches.
///
/// Pattern (after simplifyBranches) — two symmetric layouts:
///
///   Layout A (jcc → then, fallthrough → else):
///     BB0:      ...; jcc .BB_then         (fallthrough to BB_else)
///     BB_else:  mov* src_e, dst; jmp .BB_join
///     BB_then:  mov* src_t, dst            (fallthrough to BB_join)
///
///   Layout B (jcc → else, fallthrough → then):
///     BB0:      ...; jcc .BB_else         (fallthrough to BB_then)
///     BB_then:  mov* src_t, dst; jmp .BB_join
///     BB_else:  mov* src_e, dst            (fallthrough to BB_join)
///
/// Both layouts transform BB0 into:
///   mov  src_fallthrough, dst   (load value from the fallthrough branch)
///   cmovcc src_jcctarget, dst   (if condition, overwrite with jcc-target value)
///
/// Requirements: same dst register for each paired mov; dst is a GP register;
/// src from jcc-target block is a reg or mem (cmovcc doesn't take immediates);
/// fallthrough block is only reachable from BB0 (no explicit jumps to it);
/// jcc-target block has exactly one predecessor (BB0 via the jcc).
///
/// Supports multiple movs per block as long as destinations match pairwise.
@discardableResult
private func ifConvert(_ f: inout Function) -> Bool {
    var changed = false
    var i = 0
    while i < f.blocks.count {
        defer { i += 1 }
        let bb0 = f.blocks[i]
        guard !bb0.instructions.isEmpty else { continue }

        // BB0 must end with a conditional jump.
        guard case .jmpIf(let cc, let jccTargetLabel) = bb0.instructions.last else { continue }

        // BB_fallthrough: next block in layout (reached by fallthrough from BB0)
        guard i + 1 < f.blocks.count else { continue }
        let fallthroughIdx = i + 1
        let bbFallthrough = f.blocks[fallthroughIdx]

        // BB_fallthrough must end with jmp(joinLabel), preceded by 1+ mov instructions.
        guard !bbFallthrough.instructions.isEmpty,
              case .jmp(let joinLabel) = bbFallthrough.instructions.last
        else { continue }
        let fallthroughMovs = Array(bbFallthrough.instructions.dropLast())
        guard !fallthroughMovs.isEmpty,
              fallthroughMovs.allSatisfy({ $0.isMov })
        else { continue }

        // Find BB_jccTarget by label
        guard let jccTargetIdx = f.blocks.firstIndex(where: { $0.label == jccTargetLabel })
        else { continue }
        let bbJccTarget = f.blocks[jccTargetIdx]

        // BB_jccTarget must consist entirely of mov instructions (no explicit jmp),
        // falling through to BB_join which must immediately follow.
        guard !bbJccTarget.instructions.isEmpty,
              bbJccTarget.instructions.allSatisfy({ $0.isMov })
        else { continue }

        // BB_join must immediately follow BB_jccTarget
        guard jccTargetIdx + 1 < f.blocks.count,
              f.blocks[jccTargetIdx + 1].label == joinLabel
        else { continue }

        // Same number of movs in both branches
        guard fallthroughMovs.count == bbJccTarget.instructions.count else { continue }

        // Extract (sz, src, dst) pairs from each branch
        var ftPairs: [(Size, Operand, Operand)] = []
        var jtPairs: [(Size, Operand, Operand)] = []
        var extractOK = true
        for instr in fallthroughMovs {
            guard let mc = instr.movComponents else { extractOK = false; break }
            ftPairs.append((mc.sz, mc.src, mc.dst))
        }
        for instr in bbJccTarget.instructions {
            guard let mc = instr.movComponents else { extractOK = false; break }
            jtPairs.append((mc.sz, mc.src, mc.dst))
        }
        guard extractOK else { continue }

        // For each pair: same GP destination register, same size, jcc-target src is reg/mem.
        var pairsOK = true
        for (fp, jp) in zip(ftPairs, jtPairs) {
            guard case .reg(let fReg) = fp.2, case .reg(let jReg) = jp.2,
                  fReg == jReg else { pairsOK = false; break }
            guard case .physical(let pReg) = fReg, !pReg.isXMM else { pairsOK = false; break }
            guard fp.0 == jp.0 else { pairsOK = false; break }
            // cmovcc source (jcc-target) must be register or memory
            switch jp.1 {
            case .reg, .mem: break
            default: pairsOK = false; break
            }
        }
        guard pairsOK else { continue }

        // Predecessor check:
        //   - Fallthrough block: no explicit jumps target it (BB0 reaches it by fallthrough only).
        //   - JCC-target block: exactly one explicit jump targets it (BB0's jcc).
        let allTargets = f.blocks.flatMap { b in
            b.instructions.compactMap { instr -> String? in
                switch instr {
                case .jmp(let l): return l
                case .jmpIf(_, let l): return l
                default: return nil
                }
            }
        }
        let fallthroughLabel = bbFallthrough.label
        guard allTargets.filter({ $0 == fallthroughLabel }).count == 0 else { continue }
        guard allTargets.filter({ $0 == jccTargetLabel }).count == 1 else { continue }

        // Transform: replace BB0's jcc with (mov + cmovcc) pairs.
        var newInstrs = Array(bb0.instructions.dropLast())  // drop jcc
        for (fp, jp) in zip(ftPairs, jtPairs) {
            newInstrs.append(.mov(fp.0, src: fp.1, dst: fp.2))
            guard case .reg(let jReg) = jp.2 else { continue }
            newInstrs.append(.cmove(cc, jp.0, src: jp.1, dst: jReg))
        }
        f.blocks[i].instructions = newInstrs

        // Remove BB_fallthrough and BB_jccTarget (inlined into BB0).
        let toRemove: Set<String> = [fallthroughLabel, jccTargetLabel]
        f.blocks.removeAll { toRemove.contains($0.label) }

        changed = true
        i -= 1  // re-examine this position after block removal
    }
    return changed
}

// MARK: - Tail Call Optimization

/// Convert `call foo; <identity movs>; jmp epilogue` into
/// `<epilogue sequence>; jmp foo` (tail call).
private func tailCallOptimize(_ f: inout Function) -> Bool {
    // Find the epilogue block.
    guard let epilogueIdx = f.blocks.firstIndex(where: { $0.label == "epilogue" })
    else { return false }

    // Extract the epilogue instruction sequence (everything before ret).
    let epilogueInstrs = f.blocks[epilogueIdx].instructions.filter {
        if case .ret = $0 { return false }
        return true
    }

    var changed = false

    for bi in f.blocks.indices where bi != epilogueIdx {
        let instrs = f.blocks[bi].instructions
        guard !instrs.isEmpty else { continue }

        // The block must end with `jmp "epilogue"`.
        guard case .jmp(let target) = instrs.last, target == "epilogue" else { continue }
        let jmpIdx = instrs.count - 1

        // Scan backwards from the jmp to find the call.
        // Only mov instructions are allowed between call and jmp.
        var callIdx: Int? = nil
        for i in stride(from: jmpIdx - 1, through: 0, by: -1) {
            if case .call = instrs[i] {
                callIdx = i
                break
            }
            guard instrs[i].isMov else { break }
        }
        guard let ci = callIdx else { continue }
        guard case .call(let callee) = instrs[ci] else { continue }

        // Only optimize direct calls to labels (not indirect calls through registers).
        guard case .label = callee else { continue }

        // Check that the movs between call and jmp are an identity chain on %rax.
        let movsRange = (ci + 1)..<jmpIdx
        if !isReturnValueIdentity(instrs, range: movsRange) { continue }

        // Check for stack arguments: pushes that appear after the prologue
        // and before the call indicate stack-passed arguments.
        var hasStackArgs = false
        for i in stride(from: ci - 1, through: 0, by: -1) {
            let instr = instrs[i]
            // The prologue ends with `sub rsp, N` (stack allocation) or
            // `mov rsp, rbp` (if no stack allocation). Stop scanning here.
            if case .aluRmiR(.sub, _, _, .physical(.rsp)) = instr { break }
            if case .movRR(.qword, let src, let dst) = instr,
               src == .physical(.rsp), dst == .physical(.rbp) { break }
            if case .push = instr {
                hasStackArgs = true
                break
            }
        }
        if hasStackArgs { continue }

        // Transform: keep everything before the call, inline epilogue, then tail jump.
        var newInstrs = Array(instrs[..<ci])
        newInstrs.append(contentsOf: epilogueInstrs)
        newInstrs.append(.tailCall(callee))
        f.blocks[bi].instructions = newInstrs
        changed = true
    }

    return changed
}

/// Check that the mov instructions in the given range form an identity chain
/// on the return register (%rax), i.e., after executing them all, %rax still
/// holds the same value it did before.
private func isReturnValueIdentity(_ instrs: [Instr], range: Range<Int>) -> Bool {
    // Track which physical register currently holds the "return value".
    var retReg: PhysReg = .rax
    for i in range {
        guard let mc = instrs[i].movComponents,
              case .reg(.physical(let srcReg)) = mc.src,
              case .reg(.physical(let dstReg)) = mc.dst else { return false }
        if srcReg == retReg {
            retReg = dstReg
        }
        // If the mov doesn't involve retReg as source, it might clobber retReg.
        // But since mov doesn't destroy its source, we only care about the
        // destination: if it overwrites retReg with something else, we fail.
        else if dstReg == retReg {
            return false
        }
    }
    return retReg == .rax
}

private func isRSP(_ op: Operand) -> Bool {
    if case .reg(.physical(.rsp)) = op { return true }
    return false
}

private func isRBP(_ op: Operand) -> Bool {
    if case .reg(.physical(.rbp)) = op { return true }
    return false
}

// MARK: - Helpers

private func sameOperand(_ a: Operand, _ b: Operand) -> Bool {
    switch (a, b) {
    case (.reg(let r1), .reg(let r2)):
        return r1 == r2
    case (.imm(let v1), .imm(let v2)):
        return v1 == v2
    case (.mem(let m1), .mem(let m2)):
        return m1 == m2
    case (.label(let s1), .label(let s2)):
        return s1 == s2
    default:
        return false
    }
}

private func isZeroImm(_ op: Operand) -> Bool {
    if case .imm(0) = op { return true }
    return false
}

// MARK: - Instruction def analysis

/// Returns the register defined by an instruction and its size, if any.
private func defRegAndSize(_ instr: Instr) -> (Reg, Size)? {
    switch instr {
    case .aluRmiR(_, let sz, _, let dst):    return (dst, sz)
    case .imul(let sz, _, let dst):          return (dst, sz)
    case .shiftR(_, let sz, _, let dst):     return (dst, sz)
    case .unaryRm(_, let sz, let r):         return (r, sz)
    case .movRR(let sz, _, let dst):         return (dst, sz)
    case .movMR(let sz, _, let dst):         return (dst, sz)
    case .movIR(let sz, _, let dst):         return (dst, sz)
    case .movsxRmR(_, let to, _, let dst):   return (dst, to)
    case .movzxRmR(_, let to, _, let dst):   return (dst, to)
    case .lea(let sz, _, let dst):           return (dst, sz)
    case .setcc(_, let r):                   return (r, .byte)
    case .cmove(_, let sz, _, let dst):      return (dst, sz)
    case .xmmRmR(_, let sz, _, let dst):     return (dst, sz)
    case .xmmMovRR(let sz, _, let dst):      return (dst, sz)
    case .xmmMovMR(let sz, _, let dst):      return (dst, sz)
    case .cvt(_, let to, _, let dst):        return (dst, to)
    case .pop(let sz, let r):                return (r, sz)
    default:                                 return nil
    }
}

// MARK: - Flags liveness analysis

/// Check if the flags register is live after instruction at index `from`.
/// Returns true if there is a flags-consuming instruction (jcc, cmov, setcc)
/// before the next flags-defining instruction.
private func flagsLiveAfter(_ instrs: [Instr], from idx: Int) -> Bool {
    for j in (idx + 1)..<instrs.count {
        let instr = instrs[j]
        if peepholeUsesFlags(instr) { return true }
        if peepholeDefsFlags(instr) { return false }
    }
    // End of block — conservatively assume flags are live (block terminator may use them).
    return true
}

/// Check if a GP register is used (read) after instruction at index `from` in the block.
/// Conservative: returns true at end of block (may be live-out).
private func regLiveAfter(_ instrs: [Instr], from idx: Int, reg: Reg) -> Bool {
    for j in (idx + 1)..<instrs.count {
        let instr = instrs[j]
        // Check if instr uses reg as source
        if instrUsesReg(instr, reg) { return true }
        // Check if instr defines reg (kills it) before any use
        if let (defR, _) = defRegAndSize(instr), defR == reg { return false }
    }
    // End of block — conservatively assume live
    return true
}

/// Check if an instruction reads a register (as source, not just as destination).
private func instrUsesReg(_ instr: Instr, _ reg: Reg) -> Bool {
    switch instr {
    case .aluRmiR(_, _, let src, let dst):
        return sameReg(src, reg) || dst == reg  // dst is both read and written
    case .imul(_, let src, let dst):
        return sameReg(src, reg) || dst == reg
    case .cmpRmiR(_, _, let src, let dst):
        return sameReg(src, reg) || dst == reg
    case .shiftR(_, _, let src, let dst):
        return sameReg(src, reg) || dst == reg
    case .unaryRm(_, _, let r):
        return r == reg
    case .movRR(_, let src, _):
        return src == reg
    case .movRM(_, let src, let mem):
        return src == reg || memUsesReg(mem, reg)
    case .movMR(_, let mem, _):
        return memUsesReg(mem, reg)
    case .movIR:
        return false
    case .movIM(_, _, let mem):
        return memUsesReg(mem, reg)
    case .movsxRmR(_, _, let src, _):
        return sameReg(src, reg)
    case .movzxRmR(_, _, let src, _):
        return sameReg(src, reg)
    case .lea(_, let mem, _):
        return memUsesReg(mem, reg)
    case .push(_, let op):
        return sameReg(op, reg)
    case .cmove(_, _, let src, _):
        return sameReg(src, reg)
    case .setcc:
        return false
    case .jmpIf:
        return false
    case .jmp:
        return false
    case .jmpIndirect(let r):
        return r == reg
    case .call(let op):
        return sameReg(op, reg)
    case .tailCall(let op):
        return sameReg(op, reg)
    default:
        return true  // conservative
    }
}

private func sameReg(_ op: Operand, _ reg: Reg) -> Bool {
    if case .reg(let r) = op { return r == reg }
    return false
}

private func memUsesReg(_ mem: Memory, _ reg: Reg) -> Bool {
    if let b = mem.base, b == reg { return true }
    if let idx = mem.index, idx == reg { return true }
    return false
}

/// Check if an instruction may write to memory at the given address.
/// Conservative: calls and unknown instructions are assumed to write everywhere.
private func instrMayWriteMemory(_ instr: Instr, _ mem: Memory) -> Bool {
    switch instr {
    case .movRM(_, _, let dst):     return dst == mem || !memDisjoint(dst, mem)
    case .movIM(_, _, let dst):     return dst == mem || !memDisjoint(dst, mem)
    case .movMM(_, _, let dst):     return dst == mem || !memDisjoint(dst, mem)
    case .xmmMovRM(_, _, let dst):  return dst == mem || !memDisjoint(dst, mem)
    case .push:                     return true  // modifies stack
    case .call, .tailCall:          return true  // may modify any memory
    default:                        return false
    }
}

/// Conservative disjointness check: two memory operands are disjoint if they
/// use different base registers or different stack slots with known non-overlapping offsets.
private func memDisjoint(_ a: Memory, _ b: Memory) -> Bool {
    // Different base registers → can't prove disjoint (might alias)
    // Same base + different displacement → disjoint (assuming same size class)
    if a.base == b.base && a.index == nil && b.index == nil
       && a.symbol == nil && b.symbol == nil {
        return a.displacement != b.displacement
    }
    // Different symbols → disjoint (different globals)
    if let sa = a.symbol, let sb = b.symbol, sa != sb,
       a.base == nil && b.base == nil {
        return true
    }
    return false
}

private func peepholeDefsFlags(_ instr: Instr) -> Bool {
    switch instr {
    case .aluRmiR:                         return true
    case .imul:                            return true
    case .unaryRm:                         return true
    case .shiftR:                          return true
    case .cmpRmiR, .xmmCmp:               return true
    case .gpDiv:                           return true
    default:                               return false
    }
}

private func peepholeUsesFlags(_ instr: Instr) -> Bool {
    switch instr {
    case .setcc:   return true
    case .cmove:   return true
    case .jmpIf:   return true
    default:       return false
    }
}

/// Returns true if the instruction sets ZF/SF based on its result value.
/// Used for test elimination: if the previous ALU op sets ZF/SF,
/// a subsequent `test dst, dst` is redundant.
private func setsZFSFOnResult(_ instr: Instr) -> Bool {
    switch instr {
    case .aluRmiR(let op, _, _, _):
        switch op {
        case .add, .sub, .and, .or, .xor: return true
        }
    case .shiftR:
        return true
    case .unaryRm(let op, _, _):
        switch op {
        case .neg, .inc, .dec: return true
        case .not: return false  // NOT doesn't affect flags
        }
    case .imul:
        return false  // ZF/SF undefined after IMUL
    default:
        return false
    }
}
