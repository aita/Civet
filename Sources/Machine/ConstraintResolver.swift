/// Constraint resolution pass: expands pseudo-instructions and inserts
/// physical register copies based on `regConstraint` metadata.
///
/// Runs after instruction selection and before register allocation.
/// After this pass, no pseudo-instructions remain, and all physical
/// register constraints are expressed as explicit mov instructions.
public func resolveConstraints(_ program: Program) -> Program {
    var result = program
    for i in result.functions.indices {
        resolveConstraints(&result.functions[i])
    }
    return result
}

private func resolveConstraints(_ function: inout Function) {
    let scratch = Reg.physical(.r11)

    for bi in function.blocks.indices {
        var expanded: [Instr] = []

        for instr in function.blocks[bi].instructions {
            switch instr {

            // ── Expand idivRemSeq into idiv/div sequence ────────
            case .idivRemSeq(let sz, let dst, let dividend, let divisor, let signed, let isDiv):
                let rax = Operand.reg(.physical(.rax))
                let rdx = Operand.reg(.physical(.rdx))

                // 1. Move divisor to scratch (r11) to avoid rax/rdx conflict
                expanded.append(.mov(sz, src: divisor, dst: .reg(scratch)))
                // 2. Move dividend to rax
                expanded.append(.mov(sz, src: dividend, dst: rax))
                // 3. Prepare rdx
                if signed {
                    expanded.append(.signExtendData(sz))
                } else {
                    expanded.append(.aluRmiR(.xor, sz, src: rdx, dst: .physical(.rdx)))
                }
                // 4. Divide
                expanded.append(.gpDiv(sz, scratch, signed: signed))
                // 5. Move result to dst
                expanded.append(.mov(sz, src: isDiv ? rax : rdx, dst: dst))

            // ── Fix shift instructions with non-immediate, non-rcx count ─
            case .shiftR(let shiftOp, let sz, let src, let dst):
                if case .imm = src {
                    // Immediate shift: no constraint
                    expanded.append(instr)
                } else if case .reg(.physical(.rcx)) = src {
                    // Already in rcx: no fixup needed
                    expanded.append(instr)
                } else {
                    // Variable shift: must go through rcx
                    // Use scratch (r11) to stage the count to avoid clobbering
                    // dst if it gets allocated to rcx.
                    let rcx = Operand.reg(.physical(.rcx))
                    expanded.append(.mov(sz, src: src, dst: .reg(scratch)))
                    expanded.append(.mov(sz, src: .reg(scratch), dst: rcx))
                    expanded.append(.shiftR(shiftOp, sz, src: rcx, dst: dst))
                }

            default:
                expanded.append(instr)
            }
        }
        function.blocks[bi].instructions = expanded
    }
}
