import Tree

/// Global Value Numbering using dominator-tree scoped hash tables.
///
/// Extends LVN across block boundaries: the value table from a dominator block
/// is inherited by all dominated blocks. Uses Swift struct value semantics for
/// automatic scope management (copy on recurse, discard on return).
public func gvn(in function: Function) -> Function {
    let blocks = function.blocks
    guard !blocks.isEmpty else { return function }

    var f = function
    let domTree = f.dominatorTree()

    let addressTaken = collectAddressTaken(in: blocks)

    var newBlocks = blocks

    func processBlock(_ bi: Int, _ table: ValueTable) {
        var vt = table
        let block = newBlocks[bi]

        // ── Process phis ────────────────────────────────────────────────
        var newPhis: [Phi] = []
        for phi in block.phis {
            let resolvedArgs = phi.args.map {
                (label: $0.label, value: vt.resolve($0.value))
            }
            // Detect trivial phi: all args are the same (ignoring self-references).
            let values = resolvedArgs.map(\.value)
            let firstNonSelf = values.first { op in
                if case .variable(_, let id, _) = op { return id != phi.dest.id }
                return true
            }
            if let single = firstNonSelf,
               values.allSatisfy({ sameOperand($0, single) || sameOperand($0, phi.dest.asOperand) }) {
                vt.valueMap[phi.dest.id] = single
            }
            newPhis.append(Phi(dest: phi.dest, args: resolvedArgs))
        }

        // ── Process instructions ────────────────────────────────────────
        var instrs: [Instr] = []
        for instr in block.instructions {
            var resolved: Instr
            if case .addressOf(let dest, let src) = instr {
                resolved = .addressOf(dest: dest, src: src)
            } else {
                resolved = instr.remapOperands { vt.resolve($0) }
            }

            // Invalidate address-taken variables on store/call.
            switch resolved {
            case .store, .call:
                for id in addressTaken {
                    vt.valueMap.removeValue(forKey: id)
                }
            default:
                break
            }

            if let dest = resolved.dest {
                let canPropagate = !addressTaken.contains(dest.id)

                switch resolved {
                case .assign(_, let src) where canPropagate:
                    switch dest.type {
                    case .structType, .unionType, .array:
                        break
                    default:
                        vt.valueMap[dest.id] = src
                    }
                case .cast(_, let src, let toType) where canPropagate:
                    if sameType(src.type, toType) {
                        vt.valueMap[dest.id] = src
                    }
                default:
                    break
                }

                // CSE via expression hashing.
                if !resolved.hasSideEffects, let key = ExprKey(resolved) {
                    if let existing = vt.exprMap[key] {
                        vt.valueMap[dest.id] = existing
                        resolved = .assign(dest: dest, src: existing)
                    } else {
                        vt.exprMap[key] = dest.asOperand
                    }
                }
            }

            instrs.append(resolved)
        }

        let term = block.terminator.remapOperands { vt.resolve($0) }
        newBlocks[bi] = Block(label: block.label, phis: newPhis,
                              instructions: instrs, terminator: term)

        // ── Recurse into dominator tree children ────────────────────────
        for child in domTree.children[bi] {
            processBlock(child, vt)
        }
    }

    processBlock(0, ValueTable())
    return withBlocks(function, newBlocks)
}

/// Scoped hash table for value numbering.
/// Copied by value when passed to child blocks in the dominator tree.
private struct ValueTable {
    var valueMap: [Int: Operand] = [:]
    var exprMap: [ExprKey: Operand] = [:]

    func resolve(_ op: Operand) -> Operand {
        if case .variable(_, let id, _) = op, let canonical = valueMap[id] {
            return canonical
        }
        return op
    }
}
