/// Expand all `pcopy` pseudo-instructions into serialized mov sequences
/// using QBE's parallel copy algorithm.
///
/// Must run after register allocation (all operands are physical registers
/// or stack slots) and before peephole optimization.
public func expandParallelCopies(_ program: Program) -> Program {
    var result = program
    for fi in result.functions.indices {
        for bi in result.functions[fi].blocks.indices {
            var expanded: [Instr] = []
            for instr in result.functions[fi].blocks[bi].instructions {
                if case .pcopy(let copies) = instr {
                    expanded.append(contentsOf: serializePcopy(copies))
                } else {
                    expanded.append(instr)
                }
            }
            result.functions[fi].blocks[bi].instructions = expanded
        }
    }
    return result
}

/// Serialize a parallel copy into a minimal sequence of mov instructions.
///
/// Algorithm (QBE-style):
/// 1. Remove trivial copies (src == dst).
/// 2. Repeatedly emit any copy whose dst is not used as a src by another copy.
/// 3. When only cycles remain, break one by saving a dst to a scratch register,
///    emitting the copy, and rewriting remaining srcs that referenced that dst.
private func serializePcopy(_ copies: [(src: Operand, dst: Operand, sz: Size)]) -> [Instr] {
    var result: [Instr] = []
    var pending = copies.filter { !sameOp($0.src, $0.dst) }

    while !pending.isEmpty {
        // Find a copy whose dst is not any other copy's src
        let readyIdx = pending.indices.first { idx in
            let dst = pending[idx].dst
            return !pending.enumerated().contains {
                $0.offset != idx && sameOp($0.element.src, dst)
            }
        }

        if let idx = readyIdx {
            let c = pending.remove(at: idx)
            result.append(emitMov(c.sz, src: c.src, dst: c.dst))
        } else {
            // All remaining copies form cycles — break one.
            let c = pending[0]
            let isFloat = c.sz == .single || c.sz == .double_
            let tmp: Operand = isFloat
                ? .reg(.physical(LinearScanAllocator.sseScratch))
                : .reg(.physical(LinearScanAllocator.gpScratch))

            // Save c.dst to scratch
            result.append(emitMov(c.sz, src: c.dst, dst: tmp))
            // Emit the copy
            result.append(emitMov(c.sz, src: c.src, dst: c.dst))
            pending.removeFirst()

            // Rewrite remaining copies that read from c.dst to read from scratch
            for i in pending.indices {
                if sameOp(pending[i].src, c.dst) {
                    pending[i].src = tmp
                }
            }
        }
    }

    return result
}

private func emitMov(_ sz: Size, src: Operand, dst: Operand) -> Instr {
    switch sz {
    case .single, .double_: return .xmmMov(sz, src: src, dst: dst)
    default:                return .mov(sz, src: src, dst: dst)
    }
}

private func sameOp(_ a: Operand, _ b: Operand) -> Bool {
    switch (a, b) {
    case (.reg(let r1), .reg(let r2)):   return r1 == r2
    case (.imm(let v1), .imm(let v2)):   return v1 == v2
    case (.mem(let m1), .mem(let m2)):    return m1 == m2
    case (.label(let s1), .label(let s2)): return s1 == s2
    default: return false
    }
}
