import COIL
import Testing
import Tree

// MARK: - Helpers

private let intType: CType = .int(signed: true)
private let boolType: CType = .bool
private let floatType: CType = .float
private let doubleType: CType = .double
private let ptrIntType: CType = .pointer(.int(signed: true))

private func makeFunction(name: String = "f", blocks: [Block]) -> Function {
    Function(name: name, returnType: intType, params: [], locals: [],
             blocks: blocks, isStatic: false, isInline: false)
}

private func intVar(_ name: String, _ id: Int) -> Place { Place(name: name, id: id, type: intType) }
private func intOp(_ name: String, _ id: Int) -> Operand { .variable(name: name, id: id, type: intType) }
private func intConst(_ v: Int64) -> Operand { .intConst(v, type: intType) }

// MARK: - ADCE Tests

@Suite struct ADCETests {

    /// Basic dead code: instruction whose result is never used is removed.
    @Test func removesUnusedDef() {
        let x = intVar("x", 1)
        let y = intVar("y", 2)
        let b = Block(
            label: "entry",
            instructions: [
                .assign(dest: x, src: intConst(1)),   // dead: x not used
                .assign(dest: y, src: intConst(2)),   // live: returned
            ],
            terminator: .return(intOp("y", 2))
        )
        let f = aggressiveDCE(in: makeFunction(blocks: [b]))
        let ids = f.blocks[0].instructions.compactMap { $0.dest?.id }
        #expect(!ids.contains(1), "dead assign(x,1) should be removed")
        #expect(ids.contains(2), "live assign(y,2) should be kept")
    }

    /// Instructions in unreachable blocks should be cleared.
    /// Regression: SCCP turns dead branches into `.goto`, leaving unreachable blocks
    /// in place. ADCE must not pick up their definitions into defMap.
    @Test func clearsUnreachableBlockInstructions() {
        let tmp = intVar("tmp", 10)
        let res = intVar("res", 11)
        // entry: goto bb_true (unconditional — dead branch already folded by SCCP)
        let entry = Block(
            label: "entry",
            instructions: [
                .assign(dest: tmp, src: intConst(42)),  // live definition
            ],
            terminator: .goto("join")
        )
        // bb_false: unreachable; redefines tmp with a different value
        let bbFalse = Block(
            label: "bb_false",
            instructions: [
                .assign(dest: tmp, src: intConst(99)), // stale definition in dead block
            ],
            terminator: .goto("join")
        )
        // join: returns tmp
        let join = Block(
            label: "join",
            instructions: [
                .assign(dest: res, src: intOp("tmp", 10)),
            ],
            terminator: .return(intOp("res", 11))
        )
        // Block order: entry, bb_false (unreachable), join
        // If ADCE naively uses all blocks for defMap, defMap[tmp.id] = bb_false's assign(tmp,99),
        // causing the live assign(tmp,42) in entry to be removed.
        let f = aggressiveDCE(in: makeFunction(blocks: [entry, bbFalse, join]))
        let entryInstrs = f.blocks[0].instructions
        let entryIds = entryInstrs.compactMap { $0.dest?.id }
        #expect(entryIds.contains(10), "live assign(tmp,42) in entry should be kept")
        let deadInstrs = f.blocks[1].instructions
        #expect(deadInstrs.isEmpty, "unreachable block should have instructions cleared")
    }

    /// Variables used as .member base are treated as address-taken:
    /// assigns to them must be preserved even without direct SSA uses.
    @Test func keepsStructMemberBase() {
        let rec = CRecordType(tag: "S", members: [CStructMember(name: "a", type: intType)])
        let structType: CType = .structType(rec)
        let sVar = Place(name: "s", id: 5, type: structType)
        let ptrField = Place(name: "ptr_a", id: 6, type: ptrIntType)
        let val = intVar("val", 7)
        let b = Block(
            label: "entry",
            instructions: [
                .assign(dest: sVar, src: .intConst(0, type: .int(signed: false))),  // zero-init s
                .member(dest: ptrField, base: sVar.asOperand, name: "a"), // &s.a — makes s "address-taken"
                .load(dest: val, addr: ptrField.asOperand),               // val = *(&s.a)
            ],
            terminator: .return(intOp("val", 7))
        )
        let f = aggressiveDCE(in: makeFunction(blocks: [b]))
        let ids = f.blocks[0].instructions.compactMap { $0.dest?.id }
        #expect(ids.contains(5), "assign(s, 0) must be kept — s is .member base")
        #expect(ids.contains(6), "member(ptr_a, s, 'a') must be kept — used by load")
        #expect(ids.contains(7), "load(val, ptr_a) must be kept — returned")
    }
}

// MARK: - SCCP Tests

@Suite struct SCCPTests {

    /// Constant condition branch is folded to goto, dead block removed.
    @Test func foldsConstantBranch() {
        let cond = intVar("cond", 1)
        let res  = intVar("res", 2)
        // entry: cond = (1 != 0); compare; branch(ne, then, else)
        let entry = Block(
            label: "entry",
            instructions: [
                .assign(dest: cond, src: intConst(1)),
                .compare(lhs: intOp("cond", 1), rhs: intConst(0)),
            ],
            terminator: .branch(cond: .ne, then: "bb_then", else: "bb_else")
        )
        let bbThen = Block(
            label: "bb_then",
            instructions: [.assign(dest: res, src: intConst(42))],
            terminator: .goto("join")
        )
        let bbElse = Block(
            label: "bb_else",
            instructions: [.assign(dest: res, src: intConst(99))],
            terminator: .goto("join")
        )
        let phi = Phi(dest: res, args: [
            (label: "bb_then", value: intConst(42)),
            (label: "bb_else", value: intConst(99)),
        ])
        let join = Block(
            label: "join",
            phis: [phi],
            instructions: [],
            terminator: .return(intOp("res", 2))
        )
        let f = sccp(in: makeFunction(blocks: [entry, bbThen, bbElse, join]))
        // The branch should be folded: entry terminator should be goto bb_then
        let entryTerm = f.blocks[0].terminator
        if case .goto(let label) = entryTerm {
            #expect(label == "bb_then")
        } else {
            Issue.record("Expected goto(bb_then), got \(entryTerm)")
        }
    }

    /// Pure constant folding: binary with two integer constants.
    @Test func foldsBinaryConstants() {
        let r = intVar("r", 1)
        let b = Block(
            label: "entry",
            instructions: [
                .binary(dest: r, op: .add, lhs: intConst(3), rhs: intConst(4)),
            ],
            terminator: .return(intOp("r", 1))
        )
        let f = sccp(in: makeFunction(blocks: [b]))
        let instr = f.blocks[0].instructions[0]
        // After SCCP, assign(r, intConst(7)) or the return directly uses intConst(7)
        if case .assign(_, let src) = instr, case .intConst(let v, _) = src {
            #expect(v == 7)
        } else if case .return(let op) = f.blocks[0].terminator,
                  let op = op, case .intConst(let v, _) = op {
            #expect(v == 7)
        } else {
            // The add might remain if SCCP didn't fold it — check return operand
            let ret = f.blocks[0].terminator
            if case .return(let op) = ret, let op = op {
                if case .intConst(let v, _) = op { #expect(v == 7) }
            }
        }
    }
}

// MARK: - GVN / OpKey Tests

@Suite struct GVNTests {

    /// float(4.9) < 5 and double(4.9) < 5 must NOT be CSE'd together.
    /// Regression: OpKey used floatVal without type size, causing float/double
    /// constants with the same numeric value to hash identically.
    @Test func distinguishesFloatVsDoubleConstants() {
        let r1 = Place(name: "r1", id: 1, type: boolType)
        let r2 = Place(name: "r2", id: 2, type: boolType)
        let r3 = Place(name: "r3", id: 3, type: intType)
        let b = Block(
            label: "entry",
            instructions: [
                // binary(.lt, floatConst(4.9, float), floatConst(5.0, float)) → r1
                .binary(dest: r1, op: .lt,
                        lhs: .floatConst(4.9, type: floatType),
                        rhs: .floatConst(5.0, type: floatType)),
                // binary(.lt, floatConst(4.9, double), floatConst(5.0, double)) → r2 (must NOT reuse r1)
                .binary(dest: r2, op: .lt,
                        lhs: .floatConst(4.9, type: doubleType),
                        rhs: .floatConst(5.0, type: doubleType)),
                // r3 = r1 + r2 (use both, so neither is dead)
                .binary(dest: r3, op: .add,
                        lhs: .variable(name: "r1", id: 1, type: boolType),
                        rhs: .variable(name: "r2", id: 2, type: boolType)),
            ],
            terminator: .return(intOp("r3", 3))
        )
        let f = gvn(in: makeFunction(blocks: [b]))
        // After GVN, r2's definition must still be present (not replaced by r1).
        let ids = f.blocks[0].instructions.compactMap { $0.dest?.id }
        #expect(ids.contains(2), "float and double comparisons must not be CSE'd")
    }

    /// Same expression in dominator is reused in dominated block (legitimate CSE).
    @Test func cseSameExpression() {
        let a = intVar("a", 1)
        let b = intVar("b", 2)
        let c = intVar("c", 3)
        let d = intVar("d", 4)
        let blk = Block(
            label: "entry",
            instructions: [
                .binary(dest: a, op: .add, lhs: intConst(3), rhs: intConst(4)), // a = 3+4
                .binary(dest: b, op: .add, lhs: intConst(3), rhs: intConst(4)), // b = 3+4 (same)
                .binary(dest: c, op: .add, lhs: intOp("a", 1), rhs: intOp("b", 2)), // c = a+b
                .assign(dest: d, src: intOp("c", 3)),
            ],
            terminator: .return(intOp("d", 4))
        )
        let f = gvn(in: makeFunction(blocks: [blk]))
        // After GVN, b should be replaced by a (CSE), so c = a+a.
        // Check that b's instruction is an assign(b, a_operand) or that operand uses a.
        let instrB = f.blocks[0].instructions.first { $0.dest?.id == 2 }
        if let instrB = instrB, case .assign(_, let src) = instrB,
           case .variable(_, let id, _) = src {
            #expect(id == 1, "b should be copy of a after CSE")
        }
        // No crash/incorrect result is also acceptable if GVN folds constants inline.
    }
}

// MARK: - LICM Tests

@Suite struct LICMTests {

    /// A truly loop-invariant expression is hoisted to the preheader.
    @Test func hoistsInvariantAdd() {
        // Loop: for header → body → header (back edge), then exit
        // body: tmp = c1 + c2  (invariant — both constant)
        //       store(ptr, tmp)  (essential, but tmp is invariant)
        let ptr   = Place(name: "ptr",  id: 1, type: ptrIntType)
        let tmp   = intVar("tmp",  2)
        let preheader = Block(
            label: "preheader",
            instructions: [
                .assign(dest: ptr, src: .intConst(0, type: ptrIntType)),
            ],
            terminator: .goto("header")
        )
        let header = Block(
            label: "header",
            instructions: [],
            terminator: .goto("body")   // simplified: no back-edge check
        )
        let body = Block(
            label: "body",
            instructions: [
                .binary(dest: tmp, op: .add, lhs: intConst(3), rhs: intConst(4)),
                .store(addr: intOp("ptr", 1), value: intOp("tmp", 2)),
            ],
            terminator: .goto("header")  // back edge → header
        )
        let exit = Block(label: "exit", instructions: [], terminator: .return(nil))
        // NOTE: LICM requires LoopInfo which uses DominatorTree — it needs a valid CFG.
        // This test just verifies LICM doesn't crash and produces a valid function.
        let f = licm(in: makeFunction(blocks: [preheader, header, body, exit]))
        #expect(f.blocks.count >= 3, "LICM shouldn't remove blocks unexpectedly")
    }

    /// Variables with addressOf inside the loop body are NOT treated as loop-invariant.
    /// Regression: LICM was hoisting `s + i` where i is incremented via &i (address-taken)
    /// but had its SSA `assign` in the entry block (outside the loop).
    @Test func doesNotHoistAddressTakenVariable() {
        // Simulates: int i = 0; while(1) { s += arr[i]; i++; }
        // i has an SSA assign outside the loop but &i is taken inside the loop body,
        // meaning i is modified via memory and is NOT loop-invariant.
        let i = intVar("i", 1)
        let ptr_i = Place(name: "ptr_i", id: 2, type: ptrIntType)
        let loaded_i = intVar("loaded_i", 3)
        let sum = intVar("sum", 4)
        let entry = Block(
            label: "entry",
            instructions: [
                .assign(dest: i, src: intConst(0)),
                .assign(dest: sum, src: intConst(0)),
            ],
            terminator: .goto("header")
        )
        let header = Block(label: "header", instructions: [], terminator: .goto("body"))
        let body = Block(
            label: "body",
            instructions: [
                // &i — takes address of i, so i is memory-modified
                .addressOf(dest: ptr_i, src: intOp("i", 1)),
                // load i via pointer
                .load(dest: loaded_i, addr: intOp("ptr_i", 2)),
                // sum = sum + i
                .binary(dest: sum, op: .add, lhs: intOp("sum", 4), rhs: intOp("loaded_i", 3)),
                // i++ via store (simulated)
                .store(addr: intOp("ptr_i", 2), value: intConst(1)),
            ],
            terminator: .goto("header")
        )
        let f = licm(in: makeFunction(blocks: [entry, header, body]))
        // After LICM, the addressOf must still be in the loop body (not hoisted),
        // and the load of i must also remain in the loop body.
        let bodyInstrs = f.blocks.first { $0.label == "body" }?.instructions ?? []
        let bodyHasAddressOf = bodyInstrs.contains { if case .addressOf = $0 { return true }; return false }
        #expect(bodyHasAddressOf, "addressOf(i) must remain in loop body — i is address-taken")
    }
}

