/// Simplify branches with statically known conditions.
public func simplifyBranches(in function: Function) -> Function {
    var newBlocks = function.blocks.map { block -> Block in
        guard case .branch(let cond, let thenL, let elseL) = block.terminator else {
            return block
        }

        // Case: both targets identical.
        if thenL == elseL {
            var instrs = block.instructions
            if let last = instrs.last, isFlag(last) { instrs.removeLast() }
            return Block(label: block.label, phis: block.phis,
                         instructions: instrs, terminator: .goto(thenL))
        }

        // Case: compare/test with constant operands.
        guard let last = block.instructions.last else { return block }
        let winner: String?
        switch last {
        case .compare(let lhs, let rhs):
            if case .intConst(let a, _) = lhs, case .intConst(let b, _) = rhs {
                winner = evaluateCompare(a, b, cond) ? thenL : elseL
            } else { winner = nil }
        case .test(let v):
            if case .intConst(let a, _) = v {
                winner = evaluateTest(a, cond) ? thenL : elseL
            } else { winner = nil }
        default:
            winner = nil
        }

        if let target = winner {
            var instrs = block.instructions
            instrs.removeLast()
            return Block(label: block.label, phis: block.phis,
                         instructions: instrs, terminator: .goto(target))
        }
        return block
    }

    // Remove phi args for edges that no longer exist.
    let predMap = buildPredMap(newBlocks)
    newBlocks = newBlocks.map { block in
        guard !block.phis.isEmpty else { return block }
        let validPreds = predMap[block.label] ?? []
        let newPhis = block.phis.map { phi in
            Phi(dest: phi.dest, args: phi.args.filter { validPreds.contains($0.label) })
        }
        return Block(label: block.label, phis: newPhis,
                     instructions: block.instructions, terminator: block.terminator)
    }

    return withBlocks(function, newBlocks)
}

private func isFlag(_ instr: Instr) -> Bool {
    switch instr {
    case .compare, .test: return true
    default: return false
    }
}

