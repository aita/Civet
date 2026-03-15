/// Run all optimization passes in a fixpoint loop (up to 4 iterations).
private func optimizeLoop(_ function: Function) -> Function {
    var f = function
    for _ in 0..<4 {
        let prevBlocks = f.blocks
        f = sccp(in: f)
        f = strengthReduction(in: f)
        f = reassociation(in: f)
        f = gvn(in: f)
        f = aggressiveDCE(in: f)
        f = codeSinking(in: f)
        f = licm(in: f)
        f = deadStoreElimination(in: f)
        f = threadJumps(in: f)
        f = mergeBlocks(in: f)
        if f.blocks.count == prevBlocks.count &&
           instrCount(f.blocks) == instrCount(prevBlocks) { break }
    }
    return f
}

/// Run all optimization passes on a function.
public func optimize(_ function: Function) -> Function {
    var f = optimizeLoop(function)
    // Unroll after optimization stabilizes, then re-optimize.
    let preUnroll = instrCount(f.blocks)
    f = loopUnroll(in: f)
    if instrCount(f.blocks) != preUnroll {
        f = optimizeLoop(f)
    }
    return f
}

/// Run all optimization passes on every function in a program.
public func optimize(_ program: Program) -> Program {
    let inlined = inlineFunctions(program)
    return Program(
        functions: inlined.functions.map { optimize($0) },
        globals: inlined.globals
    )
}
