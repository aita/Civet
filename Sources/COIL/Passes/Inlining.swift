import Tree

/// Function inlining pass — operates on the whole `Program`.
///
/// Inlines small, non-recursive functions at their call sites to eliminate
/// call overhead and expose optimization opportunities for subsequent
/// SCCP/GVN/ADCE passes. Processes functions bottom-up so that callees
/// are already inlined before their callers.
public func inlineFunctions(_ program: Program) -> Program {
    let functionNames = Set(program.functions.map(\.name))
    var functionMap: [String: Function] = [:]
    for f in program.functions { functionMap[f.name] = f }

    // Build call graph: caller → set of direct callees.
    let callGraph = buildCallGraph(program.functions, functionNames: functionNames)

    // Count how many call sites each function has across the whole program.
    var callCounts: [String: Int] = [:]
    for f in program.functions {
        for block in f.blocks {
            for instr in block.instructions {
                if case .call(_, let callee, _) = instr,
                   case .variable(let name, _, _) = callee,
                   functionNames.contains(name) {
                    callCounts[name, default: 0] += 1
                }
            }
        }
    }

    // Bottom-up order: inline leaf functions first.
    let order = bottomUpOrder(callGraph, functionNames: functionNames)

    // Global inline counter for unique label suffixes.
    var inlineCounter = 0

    // Find minimum variable ID across the entire program for fresh IDs.
    var nextId: Int = {
        var minId = 0
        for f in program.functions {
            for block in f.blocks {
                for phi in block.phis { minId = min(minId, phi.dest.id) }
                for instr in block.instructions {
                    if let d = instr.dest { minId = min(minId, d.id) }
                }
            }
        }
        return minId - 1
    }()

    for callerName in order {
        guard var caller = functionMap[callerName] else { continue }
        var blocks = caller.blocks
        var locals = caller.locals
        let originalInstrCount = instrCount(blocks)
        var inlineCount = 0
        var changed = false

        // Scan blocks for call instructions to inline.
        var bi = 0
        while bi < blocks.count {
            var ii = 0
            while ii < blocks[bi].instructions.count {
                guard case .call(let callDest, let callee, let args) = blocks[bi].instructions[ii],
                      case .variable(let calleeName, _, _) = callee,
                      let calleeFunc = functionMap[calleeName] else {
                    ii += 1
                    continue
                }

                // Check eligibility.
                let count = callCounts[calleeName] ?? 0
                guard isInlineCandidate(calleeFunc, callCount: count) else {
                    ii += 1
                    continue
                }

                // Check bloat limit.
                let calleeInstrCount = instrCount(calleeFunc.blocks)
                if instrCount(blocks) + calleeInstrCount > originalInstrCount * 3 {
                    ii += 1
                    continue
                }

                // Max inline sites per function.
                if inlineCount >= 8 {
                    ii += 1
                    continue
                }

                // === Perform inline ===
                let suffix = ".inl.\(inlineCounter)"
                inlineCounter += 1
                inlineCount += 1

                // Build var remap for callee definitions.
                var varRemap: [Int: Int] = [:]
                var labelRemap: [String: String] = [:]

                for block in calleeFunc.blocks {
                    labelRemap[block.label] = block.label + suffix
                    for phi in block.phis {
                        varRemap[phi.dest.id] = nextId; nextId -= 1
                    }
                    for instr in block.instructions {
                        if let d = instr.dest {
                            varRemap[d.id] = nextId; nextId -= 1
                        }
                    }
                }

                // Build param remap: callee param ID → caller arg operand.
                // Detect address-taken params that need stack copies.
                let addressTakenInCallee = collectAddressTaken(in: calleeFunc.blocks)
                var paramRemap: [Int: Operand] = [:]
                var paramSetupInstrs: [Instr] = []

                for (paramIdx, param) in calleeFunc.params.enumerated() {
                    let argOp = paramIdx < args.count ? args[paramIdx] : Operand.intConst(0, type: param.type)

                    // Find the param's variable ID. Params use positive IDs matching their index+1
                    // in the source, but we need to find which ID the callee's SSA uses.
                    // The param ID is the CVar's identity — search callee blocks for uses.
                    let paramId = findParamId(param, in: calleeFunc)

                    if addressTakenInCallee.contains(paramId) {
                        // Param is address-taken: create a local copy.
                        let freshId = nextId; nextId -= 1
                        let freshPlace = Place(name: param.name + suffix, id: freshId, type: param.type)
                        paramSetupInstrs.append(.assign(dest: freshPlace, src: argOp))
                        paramRemap[paramId] = freshPlace.asOperand
                        locals.append(CVar(name: param.name + suffix, type: param.type, storage: .local(id: freshId)))
                    } else {
                        paramRemap[paramId] = argOp
                    }
                }

                // Remap helpers.
                func remapOperand(_ op: Operand) -> Operand {
                    switch op {
                    case .variable(let name, let id, let type):
                        if let argOp = paramRemap[id] { return argOp }
                        if let newId = varRemap[id] {
                            return .variable(name: name + suffix, id: newId, type: type)
                        }
                        return op
                    case .labelAddr(let label, let type):
                        if let newLabel = labelRemap[label] {
                            return .labelAddr(newLabel, type: type)
                        }
                        return op
                    default:
                        return op
                    }
                }

                func remapPlace(_ p: Place) -> Place {
                    if let newId = varRemap[p.id] {
                        return Place(name: p.name + suffix, id: newId, type: p.type)
                    }
                    return p
                }

                func remapInstr(_ instr: Instr) -> Instr {
                    let r = instr.remapOperands(remapOperand)
                    switch r {
                    case .assign(let d, let s):
                        return .assign(dest: remapPlace(d), src: s)
                    case .binary(let d, let op, let l, let rhs):
                        return .binary(dest: remapPlace(d), op: op, lhs: l, rhs: rhs)
                    case .unary(let d, let op, let s):
                        return .unary(dest: remapPlace(d), op: op, src: s)
                    case .call(let d, let c, let callArgs):
                        return .call(dest: d.map(remapPlace), callee: c, args: callArgs)
                    case .addressOf(let d, let s):
                        return .addressOf(dest: remapPlace(d), src: s)
                    case .load(let d, let a):
                        return .load(dest: remapPlace(d), addr: a)
                    case .store(let a, let v):
                        return .store(addr: a, value: v)
                    case .cast(let d, let s, let t):
                        return .cast(dest: remapPlace(d), src: s, to: t)
                    case .cas(let d, let a, let o, let n):
                        return .cas(dest: remapPlace(d), addr: a, old: o, new: n)
                    case .exchange(let d, let a, let v):
                        return .exchange(dest: remapPlace(d), addr: a, value: v)
                    case .member(let d, let b, let name, let off):
                        return .member(dest: remapPlace(d), base: b, name: name, offset: off)
                    case .alloca(let d, let s):
                        return .alloca(dest: remapPlace(d), size: s)
                    case .asm(let s):
                        return .asm(s)
                    case .compare(let l, let rhs):
                        return .compare(lhs: l, rhs: rhs)
                    case .test(let v):
                        return .test(v)
                    }
                }

                // Continuation block label.
                let currentBlock = blocks[bi]
                let contLabel = currentBlock.label + ".cont" + suffix

                // Find all return blocks in callee.
                var returnBlocks: [(blockLabel: String, value: Operand?)] = []
                for block in calleeFunc.blocks {
                    if case .return(let val) = block.terminator {
                        returnBlocks.append((labelRemap[block.label]!, val))
                    }
                }

                // Determine if we need a phi for multiple returns.
                let isStructReturn: Bool = {
                    switch calleeFunc.returnType {
                    case .structType, .unionType: return true
                    default: return false
                    }
                }()

                // For multiple-return with non-struct type, create per-return fresh vars + phi.
                var returnPhis: [Phi] = []
                var returnAssigns: [String: Instr] = [:]  // remapped return block label → assign instr

                if let dest = callDest, returnBlocks.count > 1, !isStructReturn {
                    // Multiple returns: each return block assigns to a fresh var,
                    // continuation block has a phi merging them.
                    var phiArgs: [(label: String, value: Operand)] = []
                    for ret in returnBlocks {
                        let freshId = nextId; nextId -= 1
                        let freshPlace = Place(name: dest.name + ".ret", id: freshId, type: dest.type)
                        if let val = ret.value {
                            returnAssigns[ret.blockLabel] = .assign(dest: freshPlace, src: remapOperand(val))
                        }
                        phiArgs.append((label: ret.blockLabel, value: freshPlace.asOperand))
                    }
                    returnPhis.append(Phi(dest: dest, args: phiArgs))
                }

                // Clone callee blocks with remapping.
                var clonedBlocks: [Block] = []
                for (blockIdx, block) in calleeFunc.blocks.enumerated() {
                    let newLabel = labelRemap[block.label]!

                    // Entry block gets param setup instructions prepended.
                    var newInstrs = block.instructions.map(remapInstr)
                    if blockIdx == 0 && !paramSetupInstrs.isEmpty {
                        newInstrs = paramSetupInstrs + newInstrs
                    }

                    // Remap phis (skip entry block — it shouldn't have phis).
                    let newPhis: [Phi] = blockIdx == 0 ? [] : block.phis.map { phi in
                        Phi(
                            dest: remapPlace(phi.dest),
                            args: phi.args.map { arg in
                                (label: labelRemap[arg.label] ?? arg.label,
                                 value: remapOperand(arg.value))
                            }
                        )
                    }

                    // Transform terminator.
                    var newTerm: Terminator
                    if case .return(let val) = block.terminator {
                        // Replace return with assign + goto continuation.
                        if let dest = callDest {
                            if returnBlocks.count > 1, !isStructReturn {
                                // Multiple returns: use per-block fresh var.
                                if let assignInstr = returnAssigns[newLabel] {
                                    newInstrs.append(assignInstr)
                                }
                            } else {
                                // Single return (or struct): assign directly to callDest.
                                if let val = val {
                                    newInstrs.append(.assign(dest: dest, src: remapOperand(val)))
                                }
                            }
                        }
                        newTerm = .goto(contLabel)
                    } else {
                        newTerm = block.terminator
                            .remapLabels { labelRemap[$0] ?? $0 }
                            .remapOperands(remapOperand)
                    }

                    clonedBlocks.append(Block(
                        label: newLabel, phis: newPhis,
                        instructions: newInstrs, terminator: newTerm))
                }

                // Split caller block: pre-call and continuation.
                let preCallInstrs = Array(currentBlock.instructions[..<ii])
                let postCallInstrs = Array(currentBlock.instructions[(ii + 1)...])

                // Pre-call block: instructions before the call, goto callee entry.
                let calleeEntryLabel = labelRemap[calleeFunc.blocks[0].label]!
                let preCallBlock = Block(
                    label: currentBlock.label,
                    phis: currentBlock.phis,
                    instructions: preCallInstrs,
                    terminator: .goto(calleeEntryLabel)
                )

                // Continuation block: instructions after the call + original terminator.
                let contBlock = Block(
                    label: contLabel,
                    phis: returnPhis,
                    instructions: postCallInstrs,
                    terminator: currentBlock.terminator
                )

                // Update successor blocks' phis: rename references from original block to cont.
                // Only if the continuation block has the same terminator (and thus same successors).
                for succLabel in currentBlock.terminator.successorLabels {
                    if let si = blocks.firstIndex(where: { $0.label == succLabel }) {
                        let succBlock = blocks[si]
                        let updatedPhis = succBlock.phis.map { phi -> Phi in
                            Phi(dest: phi.dest, args: phi.args.map { arg in
                                if arg.label == currentBlock.label {
                                    return (label: contLabel, value: arg.value)
                                }
                                return arg
                            })
                        }
                        blocks[si] = succBlock.with(phis: updatedPhis)
                    }
                }

                // Replace current block and insert cloned + continuation.
                blocks[bi] = preCallBlock
                blocks.insert(contentsOf: clonedBlocks + [contBlock], at: bi + 1)

                // Add callee locals to caller (remapped).
                for local in calleeFunc.locals {
                    let localOrigId = findLocalId(local, in: calleeFunc)
                    let newLocalId = varRemap[localOrigId] ?? (nextId - 1)
                    locals.append(CVar(name: local.name + suffix, type: local.type,
                                       storage: .local(id: newLocalId), stackOffset: nil, align: local.align))
                }

                changed = true

                // Decrement call count for the callee.
                callCounts[calleeName, default: 1] -= 1

                // Don't advance ii — the continuation block starts fresh scanning.
                // But we need to jump to the continuation block to continue scanning.
                // The continuation block is at bi + 1 + clonedBlocks.count.
                bi = bi + 1 + clonedBlocks.count  // points to contBlock
                ii = 0
                break  // restart inner loop on the continuation block
            }
            if ii >= (bi < blocks.count ? blocks[bi].instructions.count : 0) {
                bi += 1
            }
        }

        if changed {
            caller = Function(name: caller.name, returnType: caller.returnType,
                              params: caller.params, locals: locals,
                              blocks: blocks, isStatic: caller.isStatic,
                              isInline: caller.isInline)
            functionMap[callerName] = caller
        }
    }

    // Dead function removal: remove static functions with no remaining references.
    // A function is "referenced" if any other function mentions its name as a variable
    // operand (covers both direct calls and function pointer uses).
    // Also deduplicate functions (forward decls + definitions may share a name).
    var liveFunctions: [Function] = []
    var emittedNames: Set<String> = []
    for f in program.functions {
        // Skip duplicate entries (e.g. forward decl followed by definition).
        guard !emittedNames.contains(f.name) else { continue }

        let latest = functionMap[f.name] ?? f

        if latest.isStatic && latest.name != "main" {
            let stillReferenced = functionMap.values.contains { caller in
                guard caller.name != latest.name else { return false }
                return caller.blocks.contains { block in
                    let inOps = block.instructions.contains { instr in
                        instr.operands.contains { op in
                            if case .variable(let name, _, _) = op, name == latest.name { return true }
                            return false
                        }
                    }
                    if inOps { return true }
                    let inPhis = block.phis.contains { phi in
                        phi.operands.contains { op in
                            if case .variable(let name, _, _) = op, name == latest.name { return true }
                            return false
                        }
                    }
                    if inPhis { return true }
                    return block.terminator.operands.contains { op in
                        if case .variable(let name, _, _) = op, name == latest.name { return true }
                        return false
                    }
                }
            }
            if !stillReferenced { continue }
        }
        liveFunctions.append(latest)
        emittedNames.insert(latest.name)
    }

    return Program(functions: liveFunctions, globals: program.globals)
}

// MARK: - Call Graph

private func buildCallGraph(_ functions: [Function], functionNames: Set<String>) -> [String: Set<String>] {
    var graph: [String: Set<String>] = [:]
    for f in functions {
        var callees: Set<String> = []
        for block in f.blocks {
            for instr in block.instructions {
                if case .call(_, let callee, _) = instr,
                   case .variable(let name, _, _) = callee,
                   functionNames.contains(name) {
                    callees.insert(name)
                }
            }
        }
        graph[f.name] = callees
    }
    return graph
}

// MARK: - Bottom-Up Order

/// Reverse topological order: leaf functions first.
/// Functions in SCCs (recursive) are included but will be skipped by eligibility check.
private func bottomUpOrder(_ callGraph: [String: Set<String>], functionNames: Set<String>) -> [String] {
    var visited: Set<String> = []
    var order: [String] = []

    func visit(_ name: String) {
        guard !visited.contains(name) else { return }
        visited.insert(name)
        for callee in callGraph[name] ?? [] {
            visit(callee)
        }
        order.append(name)
    }

    for name in functionNames {
        visit(name)
    }
    return order  // leaf functions come first
}

// MARK: - Eligibility

private func isInlineCandidate(_ callee: Function, callCount: Int) -> Bool {
    // Must have a body.
    guard !callee.blocks.isEmpty else { return false }
    // Not main.
    guard callee.name != "main" else { return false }

    // No variadic functions (they depend on __va_area__ callee ABI setup).
    if callee.locals.contains(where: { $0.name == "__va_area__" }) { return false }

    // Check for disqualifying features.
    for block in callee.blocks {
        // No computed gotos.
        if case .computedGoto = block.terminator { return false }

        for instr in block.instructions {
            // No self-recursive calls.
            if case .call(_, let c, _) = instr,
               case .variable(let name, _, _) = c,
               name == callee.name { return false }
            // No labelAddr operands.
            for op in instr.operands {
                if case .labelAddr = op { return false }
            }
            // No alloca.
            if case .alloca = instr { return false }
            // No inline asm.
            if case .asm = instr { return false }
        }
    }

    let count = instrCount(callee.blocks)

    // Size thresholds.
    if callee.isInline && count <= 200 { return true }
    if callee.isStatic && callCount == 1 && count <= 200 { return true }
    if count <= 50 { return true }

    return false
}

// MARK: - Param/Local ID lookup

/// Find the variable ID used for a parameter in the callee's SSA form.
/// Parameters are referenced by their original CVar identity. The SSA builder
/// assigns them IDs matching their position or name. We search the callee's
/// blocks for variable references matching the param name.
private func findParamId(_ param: CVar, in function: Function) -> Int {
    // First check if any block references a variable with this param's name.
    // Params in COIL use the same ID as assigned by TreeConverter.
    // The most reliable way is to scan the entry block for the first definition
    // or use of a variable matching the param name.
    for block in function.blocks {
        for phi in block.phis {
            if phi.dest.name == param.name { return phi.dest.id }
            for arg in phi.args {
                if case .variable(let name, let id, _) = arg.value, name == param.name {
                    return id
                }
            }
        }
        for instr in block.instructions {
            if let d = instr.dest, d.name == param.name { return d.id }
            for op in instr.operands {
                if case .variable(let name, let id, _) = op, name == param.name {
                    return id
                }
            }
        }
        for op in block.terminator.operands {
            if case .variable(let name, let id, _) = op, name == param.name {
                return id
            }
        }
    }
    // Fallback: should not happen for well-formed IR.
    return Int.min
}

/// Find the variable ID for a local variable in the function.
private func findLocalId(_ local: CVar, in function: Function) -> Int {
    for block in function.blocks {
        for phi in block.phis {
            if phi.dest.name == local.name { return phi.dest.id }
        }
        for instr in block.instructions {
            if let d = instr.dest, d.name == local.name { return d.id }
        }
    }
    return Int.min
}
