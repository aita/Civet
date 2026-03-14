import COIL
import Tree

/// Instruction selector using DAG construction + DP tiling.
/// Replaces the switch-based COILConverter for instruction lowering.
public struct InstructionSelector {

    private let patterns: [ISelPattern]

    public init() {
        self.patterns = buildPatternTable()
    }

    // MARK: - Public API

    /// Select instructions for an entire COIL function, producing a Machine function.
    mutating func selectFunction(_ f: COIL.Function,
                                 varMap: [Int: Reg],
                                 stackSlots: [Int: Int32],
                                 mfunc: inout Function,
                                 currentStackOffset: inout Int32,
                                 constLabelCounter: inout Int) -> ([Machine.Block], [GlobalVar]) {
        var allFloatGlobals: [GlobalVar] = []
        var blocks: [Machine.Block] = []
        let coilBlockMap = Dictionary(uniqueKeysWithValues: f.blocks.map { ($0.label, $0) })
        // Side table for building Machine phi nodes: succLabel → phi arg entries.
        var phiArgTable: [String: [(dest: Reg, size: Size, predLabel: String, src: Operand)]] = [:]

        // Check if function returns a MEMORY-class struct (>16 bytes).
        // If so, the caller passes a hidden return buffer pointer in rdi.
        var retBufSlot: Int32? = nil
        let retIsMemoryStruct: Bool
        if isAggregateType(f.returnType) {
            let abi = classifyStruct(f.returnType)
            retIsMemoryStruct = abi.isMemory
        } else {
            retIsMemoryStruct = false
        }

        for (bi, block) in f.blocks.enumerated() {
            var ctx = ISelContext(
                mfunc: mfunc,
                varMap: varMap,
                stackSlots: stackSlots,
                constLabelCounter: constLabelCounter,
                currentStackOffset: currentStackOffset,
                funcName: f.name
            )

            // Insert prologue at entry block
            if bi == 0 {
                ctx.instrs.append(.prologue)

                // If returning MEMORY-class struct, save the hidden return buffer
                // pointer (rdi) to a dedicated stack slot before emitParamMoves
                // consumes the argument registers.
                if retIsMemoryStruct {
                    currentStackOffset = alignUp(currentStackOffset + 8, to: 8)
                    retBufSlot = currentStackOffset
                    ctx.instrs.append(.movRM(.qword,
                        src: .physical(.rdi),
                        dst: .stack(currentStackOffset)))
                }

                emitParamMoves(params: f.params, varMap: varMap,
                               stackSlots: stackSlots, mfunc: &mfunc,
                               currentStackOffset: &currentStackOffset,
                               into: &ctx.instrs,
                               skipFirstIntReg: retIsMemoryStruct)
                // If variadic, save argument registers to __va_area__.
                for local in f.locals {
                    if local.name == "__va_area__",
                       case .local(let id) = local.storage,
                       let vaOff = stackSlots[id] {
                        emitVarArgSetup(params: f.params, vaOff: vaOff,
                                        mfunc: &mfunc, into: &ctx.instrs)
                        break
                    }
                }
                // Sync updated state from prologue/varargs setup into context.
                // emitParamMoves and emitVarArgSetup allocate fresh vregs via
                // mfunc.freshVirtual(), so ctx.mfunc must be updated to avoid
                // vreg ID collisions with the instruction selector.
                ctx.mfunc = mfunc
                ctx.currentStackOffset = currentStackOffset
            }

            // Build DAG from COIL instructions
            var builder = DAGBuilder(varMap: varMap, stackSlots: stackSlots)
            builder.build(instructions: block.instructions)
            builder.markLiveOuts(terminator: block.terminator)

            // Mark phi arguments in successor blocks as live-out.
            for succLabel in block.terminator.successorLabels {
                if let succBlock = coilBlockMap[succLabel] {
                    for phi in succBlock.phis {
                        if let arg = phi.args.first(where: { $0.label == block.label }) {
                            builder.markPhiLiveOuts([arg.value])
                        }
                    }
                }
            }

            // DP tile all nodes bottom-up
            for node in builder.allNodes {
                tile(node)
            }

            // Emit code for all root nodes (maintains side-effect order).
            // Defer compare/test roots so they emit after cross-block
            // materializations, keeping flags live into the terminator.
            var deferredFlagRoots: [DAGNode] = []
            for root in builder.roots {
                switch root.kind {
                case .compare, .test:
                    deferredFlagRoots.append(root)
                default:
                    emitNode(root, ctx: &ctx)
                }
            }

            // Materialize varMap values for cross-block references.
            // DAG aliasing means varMap vregs may not be explicitly written.
            // Only emit copies for variables used in OTHER blocks (not via phi).
            let crossBlockUses = computeCrossBlockUses(block: block, coilFunction: f, varMap: varMap)
            for (vreg, node) in builder.varMapDefs() {
                guard crossBlockUses.contains(where: { $0.vreg == vreg }) else { continue }
                if let emitted = emitNode(node, ctx: &ctx) {
                    if case .reg(let r) = emitted, r == vreg { continue }
                    let sz = crossBlockUses.first(where: { $0.vreg == vreg })?.size ?? .qword
                    ctx.instrs.append(.mov(sz, src: emitted, dst: .reg(vreg)))
                }
            }

            // Now emit deferred compare/test roots right before terminator.
            for root in deferredFlagRoots {
                emitNode(root, ctx: &ctx)
            }

            // Collect phi arg info for Machine phi nodes (deferred until after all blocks).
            collectPhiArgs(block: block, coilFunction: f, builder: builder,
                           ctx: &ctx, phiArgTable: &phiArgTable)

            // Emit terminator
            emitTerminator(block.terminator, f: f, builder: builder, ctx: &ctx,
                           retBufSlot: retBufSlot)

            // Sync mutable state back
            mfunc = ctx.mfunc
            currentStackOffset = ctx.currentStackOffset
            constLabelCounter = ctx.constLabelCounter
            allFloatGlobals.append(contentsOf: ctx.floatGlobals)

            blocks.append(Machine.Block(label: block.label, instructions: ctx.instrs))
        }

        // Append shared epilogue block
        blocks.append(Machine.Block(label: "epilogue", instructions: [.epilogue, .ret]))

        // Build Machine phi nodes from the collected phi arg table.
        let blockLabelToIdx = Dictionary(uniqueKeysWithValues: blocks.enumerated().map { ($1.label, $0) })
        for (succLabel, args) in phiArgTable {
            guard let bi = blockLabelToIdx[succLabel] else { continue }
            var phiByDest: [Reg: MachPhi] = [:]
            for arg in args {
                if phiByDest[arg.dest] == nil {
                    phiByDest[arg.dest] = MachPhi(dest: arg.dest, size: arg.size)
                }
                phiByDest[arg.dest]!.args.append((label: arg.predLabel, src: arg.src))
            }
            blocks[bi].phis = Array(phiByDest.values)
        }

        return (blocks, allFloatGlobals)
    }

    // MARK: - DP Tiling

    /// Bottom-up DP: compute the best pattern and cost for this node.
    private func tile(_ node: DAGNode) {
        // Skip if already tiled
        guard node.bestPattern == nil else { return }

        // Tile children first (bottom-up)
        for child in node.operands {
            tile(child)
        }

        // Try all patterns, pick the lowest total cost
        for pattern in patterns {
            guard pattern.match(node) else { continue }

            // Total cost = pattern cost + cost of children NOT consumed by this pattern
            let consumed = Set(pattern.consumedChildren(node))
            var totalCost = pattern.cost
            for (i, child) in node.operands.enumerated() {
                if !consumed.contains(i) {
                    totalCost += child.bestCost
                }
            }

            if totalCost < node.bestCost {
                node.bestCost = totalCost
                node.bestPattern = pattern
            }
        }

        // Fallback: if no pattern matched, cost remains Int.max
        // This shouldn't happen if patterns are complete
    }

    // MARK: - Code Emission

    /// Emit machine instructions for a node and all its dependencies.
    @discardableResult
    private func emitNode(_ node: DAGNode, ctx: inout ISelContext) -> Operand? {
        // Already emitted (shared DAG node)
        if let cached = node.emittedOperand {
            return cached
        }

        guard let pattern = node.bestPattern else {
            return nil
        }

        // Emit non-consumed children first
        let consumed = Set(pattern.consumedChildren(node))
        for (i, child) in node.operands.enumerated() {
            if !consumed.contains(i) {
                emitNode(child, ctx: &ctx)
            }
        }

        // Emit this node using its pattern
        let result = pattern.emit(node, &ctx)
        node.emittedOperand = result
        return result
    }

    // MARK: - Phi Lowering

    /// Collect phi arg info for Machine phi nodes (deferred until after all blocks).
    /// Instead of emitting parallel copies eagerly, we build MachPhi nodes in successors.
    private func collectPhiArgs(block: COIL.Block, coilFunction: COIL.Function,
                                builder: DAGBuilder, ctx: inout ISelContext,
                                phiArgTable: inout [String: [(dest: Reg, size: Size,
                                                              predLabel: String, src: Operand)]]) {
        let coilBlockMap = Dictionary(uniqueKeysWithValues: coilFunction.blocks.map { ($0.label, $0) })

        for succLabel in block.terminator.successorLabels {
            guard let succBlock = coilBlockMap[succLabel], !succBlock.phis.isEmpty else { continue }

            for phi in succBlock.phis {
                guard let arg = phi.args.first(where: { $0.label == block.label }) else { continue }
                guard let dstReg = ctx.varMap[phi.dest.id] else { continue }
                let sz = Size.from(phi.dest.type)

                // Get the source operand — prefer the DAG's emitted result over the varMap slot.
                let srcOp: Operand
                if case .variable(_, let id, _) = arg.value,
                   let node = builder.lookupDef(id) {
                    if let emitted = node.emittedOperand {
                        srcOp = emitted
                    } else if let emitted = emitNode(node, ctx: &ctx) {
                        srcOp = emitted
                    } else {
                        srcOp = nodeOperandDirect(arg.value, ctx: &ctx)
                    }
                } else {
                    srcOp = nodeOperandDirect(arg.value, ctx: &ctx)
                }
                phiArgTable[succLabel, default: []].append(
                    (dest: dstReg, size: sz, predLabel: block.label, src: srcOp))
            }
        }
    }

    /// Find variables defined in this block that are used in other blocks
    /// via regular instructions or terminator operands (NOT phi args).
    ///
    /// Phi args are excluded here because `emitPhiCopies` handles them
    /// directly using the node's `emittedOperand` (the actual register the
    /// value was computed into). Including phi-arg-only variables here would
    /// generate a redundant copy into the varMap register, producing two
    /// moves per branch and defeating if-conversion.
    ///
    /// Phi arg variables whose node has no `emittedOperand` (inlined constant)
    /// are handled by `emitPhiCopies` falling back to `nodeOperandDirect`,
    /// which reads the varMap register — but those variables are constants and
    /// the varMap register is never needed for non-phi uses anyway.
    private func computeCrossBlockUses(
        block: COIL.Block, coilFunction: COIL.Function,
        varMap: [Int: Reg]
    ) -> [(vreg: Reg, size: Size)] {
        // Collect IDs defined in this block
        var defsInBlock: Set<Int> = []
        for instr in block.instructions {
            if let dest = instr.dest { defsInBlock.insert(dest.id) }
        }

        var result: [(vreg: Reg, size: Size)] = []
        var seen: Set<Int> = []
        for otherBlock in coilFunction.blocks where otherBlock.label != block.label {
            // Check terminator operands
            for op in otherBlock.terminator.operands {
                if case .variable(_, let id, let type) = op,
                   defsInBlock.contains(id),
                   let reg = varMap[id], seen.insert(id).inserted {
                    result.append((vreg: reg, size: Size.from(type)))
                }
            }
            // Check instruction operands (not phi args — emitPhiCopies handles those)
            for instr in otherBlock.instructions {
                for op in instr.operands {
                    if case .variable(_, let id, let type) = op,
                       defsInBlock.contains(id),
                       let reg = varMap[id], seen.insert(id).inserted {
                        result.append((vreg: reg, size: Size.from(type)))
                    }
                }
            }
        }
        return result
    }

    // MARK: - Terminator Emission

    private func emitTerminator(_ term: COIL.Terminator, f: COIL.Function,
                                builder: DAGBuilder, ctx: inout ISelContext,
                                retBufSlot: Int32? = nil) {
        switch term {
        case .goto(let label):
            ctx.instrs.append(.jmp(label))

        case .branch(let cond, let thenLabel, let elseLabel):
            let cc = condCode(from: cond)
            ctx.instrs.append(.jmpIf(cc, thenLabel))
            ctx.instrs.append(.jmp(elseLabel))

        case .return(let value):
            if let value = value {
                // Check for struct return
                if isAggregateType(f.returnType) {
                    let abi = classifyStruct(f.returnType)
                    let structSz = typeSize(f.returnType)

                    // Get struct address (return value is a struct variable → its address)
                    let structOp = resolveOperand(value, builder: builder, ctx: &ctx)

                    if abi.isMemory {
                        // MEMORY class: copy struct to return buffer.
                        // The buffer address was saved at function entry to retBufSlot.
                        guard let bufSlot = retBufSlot else { break }
                        // Get struct source address
                        let srcAddr = structAddrReg(structOp, ctx: &ctx)
                        // Load buffer address
                        let bufAddr = ctx.freshVirtual()
                        ctx.instrs.append(.movMR(.qword, src: .stack(bufSlot), dst: bufAddr))
                        // Copy struct from source to buffer
                        emitBlockTransfer(to: bufAddr, from: srcAddr, size: structSz, ctx: &ctx)
                        // Return the buffer address in rax
                        ctx.instrs.append(.movRR(.qword, src: bufAddr, dst: .physical(.rax)))
                    } else {
                        // Small struct: load eightbytes into return registers.
                        let structAddr = structAddrReg(structOp, ctx: &ctx)

                        var retIntIdx = 0
                        var retSseIdx = 0
                        let intRetRegs: [PhysReg] = [.rax, .rdx]
                        let sseRetRegs: [PhysReg] = [.xmm0, .xmm1]
                        for (ebIdx, cls) in abi.classes.enumerated() {
                            let off = Int32(ebIdx * 8)
                            let remaining = structSz - ebIdx * 8
                            let ldSz: Size = remaining >= 8 ? .qword : .dword
                            let mem = Memory(base: structAddr, displacement: off)
                            if cls == .sse {
                                let reg = sseRetRegs[retSseIdx]; retSseIdx += 1
                                ctx.instrs.append(ldSz == .dword
                                    ? .xmmMovMR(.single, src: mem, dst: .physical(reg))
                                    : .xmmMovMR(.double_, src: mem, dst: .physical(reg)))
                            } else {
                                let reg = intRetRegs[retIntIdx]; retIntIdx += 1
                                ctx.instrs.append(.movMR(ldSz, src: mem, dst: .physical(reg)))
                            }
                        }
                    }
                } else {
                    let sz = Size.from(f.returnType)
                    let op = resolveOperand(value, builder: builder, ctx: &ctx)
                    if isFloat(f.returnType) {
                        ctx.instrs.append(.xmmMov(sz, src: op, dst: .reg(.physical(.xmm0))))
                    } else {
                        ctx.instrs.append(.mov(sz, src: op, dst: .reg(.physical(.rax))))
                    }
                }
            }
            ctx.instrs.append(.jmp("epilogue"))

        case .computedGoto(let value):
            let cgOp = resolveOperand(value, builder: builder, ctx: &ctx)
            if case .reg(let r) = cgOp {
                ctx.instrs.append(.jmpIndirect(r))
            } else {
                let tmp = ctx.freshVirtual()
                ctx.instrs.append(.mov(.qword, src: cgOp, dst: .reg(tmp)))
                ctx.instrs.append(.jmpIndirect(tmp))
            }
        }
    }

    /// Resolve a COIL operand to a machine operand, preferring the DAG's emitted result.
    private func resolveOperand(_ value: COIL.Operand, builder: DAGBuilder,
                                ctx: inout ISelContext) -> Operand {
        if case .variable(_, let id, _) = value, let node = builder.lookupDef(id) {
            return emitNode(node, ctx: &ctx) ?? nodeOperandDirect(value, ctx: &ctx)
        }
        return nodeOperandDirect(value, ctx: &ctx)
    }

    /// Get the address register from a struct operand (which may be .mem or .reg).
    private func structAddrReg(_ structOp: Operand, ctx: inout ISelContext) -> Reg {
        if case .mem(let mem) = structOp {
            let tmp = ctx.freshVirtual()
            ctx.instrs.append(.lea(.qword, src: mem, dst: tmp))
            return tmp
        } else {
            let tmp = ctx.freshVirtual()
            ctx.instrs.append(.mov(.qword, src: structOp, dst: .reg(tmp)))
            return tmp
        }
    }

    // MARK: - Direct operand conversion (for terminator operands)

    private func nodeOperandDirect(_ op: COIL.Operand, ctx: inout ISelContext) -> Operand {
        switch op {
        case .variable(let name, let id, let type):
            if let reg = ctx.varMap[id] {
                return .reg(reg)
            }
            if let offset = ctx.stackSlots[id] {
                return .mem(.stack(offset))
            }
            if case .function = type {
                return .label(name)
            }
            return .mem(.global(name))
        case .intConst(let value, _):
            return .imm(value)
        case .floatConst(let value, let type):
            return materializeFloat(value, type: type, ctx: &ctx)
        case .labelAddr(let label, _):
            let reg = ctx.freshVirtual()
            let asmLabel = ".L\(ctx.funcName).\(label)"
            ctx.instrs.append(.lea(.qword, src: .global(asmLabel), dst: reg))
            return .reg(reg)
        }
    }


    // MARK: - Helpers

    private func condCode(from cond: COIL.Condition) -> CondCode {
        switch cond {
        case .eq:      return .e
        case .ne:      return .ne
        case .lt:      return .l
        case .le:      return .le
        case .zero:    return .z
        case .nonZero: return .nz
        }
    }


    // MARK: - Parameter ABI (reused from COILConverter)

    private func emitParamMoves(params: [CVar], varMap: [Int: Reg],
                                stackSlots: [Int: Int32], mfunc: inout Function,
                                currentStackOffset: inout Int32,
                                into instrs: inout [Instr],
                                skipFirstIntReg: Bool = false) {
        // Two-phase approach to avoid parallel copy conflicts:
        // Phase 1: Spill all physical arg registers to dedicated stack slots.
        // Phase 2: Load from stack to final destinations (virtual regs or stack slots).
        // Struct params are always stored directly to their stack slots.

        struct ParamInfo {
            let id: Int
            let sz: Size
            let isFloat: Bool
            let spillSlot: Int32
        }
        var paramInfos: [ParamInfo] = []
        // If the function returns a MEMORY-class struct, rdi is consumed by the
        // hidden return buffer pointer, so declared parameters start from rsi.
        var intIdx = skipFirstIntReg ? 1 : 0
        var sseIdx = 0
        var stackArgOffset: Int32 = 16

        // Pre-scan: count how many register slots are used (including struct eightbytes)
        var regParamCount = 0
        var preIntIdx = skipFirstIntReg ? 1 : 0
        var preSseIdx = 0
        for p in params {
            guard case .local = p.storage else { continue }
            if isAggregateType(p.type) {
                let abi = classifyStruct(p.type)
                if !abi.isMemory {
                    for cls in abi.classes {
                        if cls == .sse {
                            if preSseIdx < PhysReg.sseArgRegs.count { regParamCount += 1; preSseIdx += 1 }
                        } else {
                            if preIntIdx < PhysReg.intArgRegs.count { regParamCount += 1; preIntIdx += 1 }
                        }
                    }
                }
            } else if isFloat(p.type) {
                if preSseIdx < PhysReg.sseArgRegs.count { regParamCount += 1; preSseIdx += 1 }
                else { preSseIdx += 1 }
            } else {
                if preIntIdx < PhysReg.intArgRegs.count { regParamCount += 1; preIntIdx += 1 }
                else { preIntIdx += 1 }
            }
        }

        let needTwoPhase = regParamCount > 1

        // Process parameters in order. Struct params are stored directly to their stack slot.
        // Scalar params use the two-phase approach when needed.
        for p in params {
            guard case .local(let id) = p.storage else { continue }

            // ── Struct/union/array parameter ──────────────────────────────
            if isAggregateType(p.type) {
                let abi = classifyStruct(p.type)
                let structSz = typeSize(p.type)
                guard let targetSlot = stackSlots[id] else { continue }

                if abi.isMemory {
                    // MEMORY class: struct is on caller's stack. Copy to our stack slot.
                    let qwords = (structSz + 7) / 8
                    let scratch: Reg = .physical(LinearScanAllocator.gpScratch)
                    for qi in 0..<qwords {
                        let off = Int32(qi * 8)
                        let remaining = structSz - qi * 8
                        let ldSz: Size = remaining >= 8 ? .qword : .dword
                        let callerMem = Memory(base: .physical(.rbp), displacement: stackArgOffset + off)
                        let localMem = Memory(base: .physical(.rbp), displacement: -targetSlot + off)
                        instrs.append(.movMR(ldSz, src: callerMem, dst: scratch))
                        instrs.append(.movRM(ldSz, src: scratch, dst: localMem))
                    }
                    stackArgOffset += Int32((structSz + 7) / 8 * 8)
                } else {
                    // Small struct: eightbytes arrive in registers.
                    for (ebIdx, cls) in abi.classes.enumerated() {
                        let off = Int32(ebIdx * 8)
                        let remaining = structSz - ebIdx * 8
                        let stSz: Size = remaining >= 8 ? .qword : .dword
                        let dstMem = Memory(base: .physical(.rbp), displacement: -targetSlot + off)

                        if cls == .sse {
                            if sseIdx < PhysReg.sseArgRegs.count {
                                let src = PhysReg.sseArgRegs[sseIdx]; sseIdx += 1
                                instrs.append(stSz == .dword
                                    ? .xmmMovRM(.single, src: .physical(src), dst: dstMem)
                                    : .xmmMovRM(.double_, src: .physical(src), dst: dstMem))
                            }
                        } else {
                            if intIdx < PhysReg.intArgRegs.count {
                                let src = PhysReg.intArgRegs[intIdx]; intIdx += 1
                                instrs.append(.movRM(stSz, src: .physical(src), dst: dstMem))
                            }
                        }
                    }
                }
                continue
            }

            // ── Scalar parameter ─────────────────────────────────────────
            let sz = Size.from(p.type)

            if !needTwoPhase {
                // Simple case: directly move register to destination
                if isFloat(p.type) {
                    if sseIdx < PhysReg.sseArgRegs.count {
                        let src = PhysReg.sseArgRegs[sseIdx]; sseIdx += 1
                        if let dst = varMap[id] {
                            instrs.append(.xmmMovRR(sz, src: .physical(src), dst: dst))
                        }
                    } else {
                        if let dst = varMap[id] {
                            let mem = Memory(base: .physical(.rbp), displacement: stackArgOffset)
                            instrs.append(.xmmMovMR(sz, src: mem, dst: dst))
                        }
                        stackArgOffset += 8
                    }
                } else {
                    if intIdx < PhysReg.intArgRegs.count {
                        let src = PhysReg.intArgRegs[intIdx]; intIdx += 1
                        if let dst = varMap[id] {
                            instrs.append(.movRR(sz, src: .physical(src), dst: dst))
                        } else if let offset = stackSlots[id] {
                            instrs.append(.movRM(.qword, src: .physical(src),
                                               dst: .stack(offset)))
                        }
                    } else {
                        if let dst = varMap[id] {
                            let mem = Memory(base: .physical(.rbp), displacement: stackArgOffset)
                            instrs.append(.movMR(sz, src: mem, dst: dst))
                        }
                        stackArgOffset += 8
                    }
                }
            } else {
                // Two-phase: spill register to temp slot first
                if isFloat(p.type) {
                    if sseIdx < PhysReg.sseArgRegs.count {
                        let src = PhysReg.sseArgRegs[sseIdx]; sseIdx += 1
                        currentStackOffset = alignUp(currentStackOffset + 8, to: 8)
                        let slot = currentStackOffset
                        instrs.append(.xmmMovRM(sz, src: .physical(src), dst: .stack(slot)))
                        paramInfos.append(ParamInfo(id: id, sz: sz, isFloat: true, spillSlot: slot))
                    } else {
                        let mem = Memory(base: .physical(.rbp), displacement: stackArgOffset)
                        if let dst = varMap[id] {
                            instrs.append(.xmmMovMR(sz, src: mem, dst: dst))
                        }
                        stackArgOffset += 8
                    }
                } else {
                    if intIdx < PhysReg.intArgRegs.count {
                        let src = PhysReg.intArgRegs[intIdx]; intIdx += 1
                        currentStackOffset = alignUp(currentStackOffset + 8, to: 8)
                        let slot = currentStackOffset
                        instrs.append(.movRM(.qword, src: .physical(src),
                                           dst: .stack(slot)))
                        paramInfos.append(ParamInfo(id: id, sz: sz, isFloat: false, spillSlot: slot))
                    } else {
                        let mem = Memory(base: .physical(.rbp), displacement: stackArgOffset)
                        if let dst = varMap[id] {
                            instrs.append(.movMR(sz, src: mem, dst: dst))
                        }
                        stackArgOffset += 8
                    }
                }
            }
        }

        // Phase 2 (only for two-phase scalar params): load from temp slots to final destinations
        for info in paramInfos {
            if let dst = varMap[info.id] {
                if info.isFloat {
                    instrs.append(.xmmMovMR(info.sz, src: .stack(info.spillSlot), dst: dst))
                } else {
                    instrs.append(.movMR(info.sz, src: .stack(info.spillSlot), dst: dst))
                }
            } else if let offset = stackSlots[info.id] {
                let scratch: Reg = .physical(LinearScanAllocator.gpScratch)
                instrs.append(.movMR(.qword, src: .stack(info.spillSlot), dst: scratch))
                instrs.append(.movRM(.qword, src: scratch, dst: .stack(offset)))
            }
        }
    }

    /// Emit the variadic register save area setup for a function with `...`.
    ///
    /// SysV AMD64 ABI: `__va_area__` is a 136-byte local laid out as:
    ///   [0..3]   gp_offset       (int)
    ///   [4..7]   fp_offset       (int)
    ///   [8..15]  overflow_arg_area (pointer)
    ///   [16..23] reg_save_area   (pointer, → vaOff+24)
    ///   [24..71] saved rdi..r9   (6 × 8 bytes)
    ///   [72..135] saved xmm0..xmm7 (8 × 8 bytes, low 64 bits only)
    private func emitVarArgSetup(params: [CVar], vaOff: Int32,
                                  mfunc: inout Function,
                                  into instrs: inout [Machine.Instr]) {
        // Count integer and float regs consumed by named params.
        var gpCount = 0
        var fpCount = 0
        for param in params {
            switch param.type {
            case .float, .double, .longDouble:
                if fpCount < 8 { fpCount += 1 }
            default:
                if gpCount < 6 { gpCount += 1 }
            }
        }

        // vaOff is the lowest address (deepest in stack) of the __va_area__ struct.
        // Field at byte offset N has address rbp - (vaOff - N), i.e. .stack(vaOff - N).

        // Save 6 integer argument registers to va_area[24..71].
        let intArgRegs: [PhysReg] = [.rdi, .rsi, .rdx, .rcx, .r8, .r9]
        for (i, reg) in intArgRegs.enumerated() {
            instrs.append(.movRM(.qword, src: .physical(reg),
                               dst: .stack(vaOff - 24 - Int32(i * 8))))
        }
        // Save 8 XMM argument registers (low 64 bits via movsd) to va_area[72..135].
        for i in 0..<8 {
            let xmm = Reg.physical(PhysReg(rawValue: PhysReg.xmm0.rawValue + UInt8(i))!)
            instrs.append(.xmmMovRM(.double_, src: xmm,
                                   dst: .stack(vaOff - 72 - Int32(i * 8))))
        }

        // gp_offset (field 0): number of bytes consumed by named int params.
        instrs.append(.movIM(.dword, imm: Int64(gpCount * 8), dst: .stack(vaOff)))
        // fp_offset (field 4): 48 + number of bytes consumed by named fp params.
        instrs.append(.movIM(.dword, imm: Int64(48 + fpCount * 16), dst: .stack(vaOff - 4)))

        // overflow_arg_area (field 8): first stacked argument = 16(%rbp).
        let tmp1 = mfunc.freshVirtual()
        instrs.append(.lea(.qword, src: .stack(-16), dst: tmp1))
        instrs.append(.movRM(.qword, src: tmp1, dst: .stack(vaOff - 8)))

        // reg_save_area (field 16): pointer to va_area[24] (int register save area).
        let tmp2 = mfunc.freshVirtual()
        instrs.append(.lea(.qword, src: .stack(vaOff - 24), dst: tmp2))
        instrs.append(.movRM(.qword, src: tmp2, dst: .stack(vaOff - 16)))
    }

    private func isAggregateType(_ type: CType) -> Bool {
        switch type {
        case .structType, .unionType, .array: return true
        default: return false
        }
    }

}
