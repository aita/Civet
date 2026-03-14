import Machine
import Testing

// MARK: - Peephole / If-Conversion Tests

@Suite struct PeepholeIfConversionTests {

    private func makeMFunc(blocks: [Block]) -> Function {
        Function(name: "f", blocks: blocks)
    }

    private func makeProgram(_ fn: Function) -> Program {
        Program(functions: [fn], globals: [])
    }

    /// Diamond CFG with single mov per branch → should be if-converted to cmov.
    ///
    ///   BB0:  cmp; jmpIf(le, else)        (fallthrough to then)
    ///   then: mov %eax, %edx; jmp join
    ///   else: mov %ecx, %edx            (fallthrough to join)
    ///   join: ret
    @Test func convertsSingleMovDiamond() {
        let rax = Operand.reg(.physical(.rax))
        let rcx = Operand.reg(.physical(.rcx))

        let bb0    = Block(label: "bb0",  instructions: [.cmpRmiR(.cmp, .dword, src: rax, dst: .physical(.rcx)), .jmpIf(.le, "else")])
        let bbThen = Block(label: "then", instructions: [.movRR(.dword, src: .physical(.rax), dst: .physical(.rdx)), .jmp("join")])
        let bbElse = Block(label: "else", instructions: [.movRR(.dword, src: .physical(.rcx), dst: .physical(.rdx))])
        let bbJoin = Block(label: "join", instructions: [.ret])

        let result = peephole(makeProgram(makeMFunc(blocks: [bb0, bbThen, bbElse, bbJoin])))
        let fn = result.functions[0]

        // After if-conversion: then and else blocks removed; bb0 contains cmov.
        let labels = fn.blocks.map { $0.label }
        #expect(!labels.contains("then"), "then block should be removed after if-conversion")
        #expect(!labels.contains("else"), "else block should be removed after if-conversion")
        let bb0Out = fn.blocks.first { $0.label == "bb0" }!
        let hasCmov = bb0Out.instructions.contains { if case .cmove = $0 { return true }; return false }
        #expect(hasCmov, "bb0 should contain a cmove after if-conversion")
    }

    /// Immediate source in jcc-target → must NOT be if-converted (cmovcc has no imm form).
    ///
    ///   BB0:  test; jmpIf(e, else)
    ///   then: mov $1, %rcx; jmp join
    ///   else: mov $-1, %rcx           (immediate source — cannot use cmovcc)
    ///   join: ret
    @Test func doesNotConvertImmediateSource() {
        let rcx = Operand.reg(.physical(.rcx))

        let bb0    = Block(label: "bb0",  instructions: [.cmpRmiR(.test, .dword, src: rcx, dst: .physical(.rcx)), .jmpIf(.e, "else")])
        let bbThen = Block(label: "then", instructions: [.movIR(.qword, imm: 1,  dst: .physical(.rcx)), .jmp("join")])
        let bbElse = Block(label: "else", instructions: [.movIR(.qword, imm: -1, dst: .physical(.rcx))])
        let bbJoin = Block(label: "join", instructions: [.ret])

        let result = peephole(makeProgram(makeMFunc(blocks: [bb0, bbThen, bbElse, bbJoin])))
        let fn = result.functions[0]

        // then and else blocks should still be present (no if-conversion).
        let labels = fn.blocks.map { $0.label }
        #expect(labels.contains("then") || labels.contains("else"),
                "blocks should not be removed when jcc-target has immediate source")
    }

    /// Standalone jmp to next block is removed (fallthrough optimization).
    @Test func removesFallthroughJmp() {
        let bb0 = Block(label: "bb0", instructions: [
            .movRR(.dword, src: .physical(.rax), dst: .physical(.rcx)),
            .jmp("bb1"),
        ])
        let bb1 = Block(label: "bb1", instructions: [.ret])

        let result = peephole(makeProgram(makeMFunc(blocks: [bb0, bb1])))
        let fn = result.functions[0]
        let bb0Out = fn.blocks.first { $0.label == "bb0" }!
        let hasJmp = bb0Out.instructions.contains { if case .jmp = $0 { return true }; return false }
        #expect(!hasJmp, "fallthrough jmp to next block should be removed")
    }

    /// cmpRmiR(.cmp, ..., src: $0) → cmpRmiR(.test, ...) peephole.
    @Test func foldsCmpZeroToTest() {
        let rax = Operand.reg(.physical(.rax))
        let bb0 = Block(label: "bb0", instructions: [
            .cmpRmiR(.cmp, .dword, src: .imm(0), dst: .physical(.rax)),
            .ret,
        ])

        let result = peephole(makeProgram(makeMFunc(blocks: [bb0])))
        let fn = result.functions[0]
        let instrs = fn.blocks[0].instructions
        // cmp $0, %rax → test %rax, %rax
        let hasTest = instrs.contains { if case .cmpRmiR(.test, _, _, _) = $0 { return true }; return false }
        let hasCmp  = instrs.contains { if case .cmpRmiR(.cmp, _, _, _)  = $0 { return true }; return false }
        #expect(hasTest, "cmp $0, %reg should be replaced by test %reg, %reg")
        #expect(!hasCmp, "original cmp $0 should be removed")
    }
}
