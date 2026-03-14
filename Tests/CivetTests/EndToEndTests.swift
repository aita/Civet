import COIL
import Foundation
import Machine
import SyntaxMapper
import Testing
import Tree

@Suite(.serialized) struct EndToEndTests {

    // MARK: - Test infrastructure

    /// Compile C code through the full Civet pipeline and return assembly.
    private func compile(_ code: String) throws -> String {
        let tmp = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tmp, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tmp) }

        let srcPath = tmp.appendingPathComponent("test.c").path
        try code.write(toFile: srcPath, atomically: true, encoding: .utf8)
        return try compileFile(srcPath)
    }

    /// Compile a C file through the full Civet pipeline and return assembly.
    private func compileFile(_ path: String, includePaths: [String] = []) throws -> String {
        let dirParts = path.components(separatedBy: "/")
        let dir = dirParts.count > 1 ? dirParts.dropLast(1).joined(separator: "/") : "."

        let builtinsPath = projectRoot + "/Resources/chibicc-builtins"
        let allIncludes = [dir, builtinsPath,
                           "/usr/local/include",
                           "/usr/include/x86_64-linux-gnu",
                           "/usr/include"] + includePaths

        let syntaxUnit = try SyntaxMapper().parseFile(path, includePaths: allIncludes)
        let treeUnit = SyntaxConverter().convert(syntaxUnit)
        let coil = TreeConverter().convert(treeUnit)
        let ssa = SSABuilder().build(coil)
        let program = optimize(ssa)
        var converter = COILConverter()
        let machProg = converter.convert(program)
        let resolved = resolveConstraints(machProg)
        let allocated = allocateRegisters(resolved)
        let expanded = expandParallelCopies(allocated)
        let optimized = peephole(expanded)
        let legalized = fixIllegalInstructions(optimized)
        let scheduled = schedule(legalized)
        return AsmPrinter().emit(scheduled)
    }

    /// Compile C code, assemble, link, run, and return the exit code.
    private func compileAndRun(_ code: String) throws -> Int32 {
        let asm = try compile(code)
        return try assembleAndRun(asm)
    }

    /// Assemble, link and run assembly code, returning exit code.
    private func assembleAndRun(_ asm: String, extraObjects: [String] = []) throws -> Int32 {
        let tmp = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tmp, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tmp) }

        let asmPath = tmp.appendingPathComponent("test.s").path
        try asm.write(toFile: asmPath, atomically: true, encoding: .utf8)

        let binPath = tmp.appendingPathComponent("test").path
        var gccArgs = ["-o", binPath, asmPath, "-z", "noexecstack"]
        gccArgs.append(contentsOf: extraObjects)

        let gcc = Process()
        gcc.executableURL = URL(fileURLWithPath: "/usr/bin/gcc")
        gcc.arguments = gccArgs
        let errPipe = Pipe()
        gcc.standardError = errPipe
        try gcc.run()
        gcc.waitUntilExit()
        guard gcc.terminationStatus == 0 else {
            let errData = errPipe.fileHandleForReading.readDataToEndOfFile()
            let errMsg = String(data: errData, encoding: .utf8) ?? ""
            throw TestError.compileError("gcc link failed (\(gcc.terminationStatus)): \(errMsg)")
        }

        let run = Process()
        run.executableURL = URL(fileURLWithPath: binPath)
        try run.run()
        run.waitUntilExit()
        return run.terminationStatus
    }

    /// Project root directory.
    private var projectRoot: String {
        // Walk up from the test source file location
        let file = #filePath
        let parts = file.components(separatedBy: "/")
        // .../Tests/CivetTests/EndToEndTests.swift → drop last 3
        return parts.dropLast(3).joined(separator: "/")
    }

    private enum TestError: Error {
        case assembleError
        case compileError(String)
    }

    // MARK: - Return values

    @Test func returnZero() throws {
        #expect(try compileAndRun("int main() { return 0; }") == 0)
    }

    @Test func returnLiteral() throws {
        #expect(try compileAndRun("int main() { return 42; }") == 42)
    }

    @Test func returnMaxByte() throws {
        #expect(try compileAndRun("int main() { return 255; }") == 255)
    }

    // MARK: - Arithmetic

    @Test func addSub() throws {
        #expect(try compileAndRun("int main() { return 5+20-4; }") == 21)
    }

    @Test func precedence() throws {
        #expect(try compileAndRun("int main() { return 5+6*7; }") == 47)
    }

    @Test func parens() throws {
        #expect(try compileAndRun("int main() { return 5*(9-6); }") == 15)
    }

    @Test func div() throws {
        #expect(try compileAndRun("int main() { return (3+5)/2; }") == 4)
    }

    @Test func neg() throws {
        #expect(try compileAndRun("int main() { return -10+20; }") == 10)
    }

    @Test func doubleNeg() throws {
        #expect(try compileAndRun("int main() { return - -10; }") == 10)
    }

    @Test func mixedUnary() throws {
        #expect(try compileAndRun("int main() { return - - +10; }") == 10)
    }

    @Test func mod() throws {
        #expect(try compileAndRun("int main() { return 17%6; }") == 5)
    }

    // MARK: - Comparisons

    @Test func eqTrue() throws {
        #expect(try compileAndRun("int main() { return 42==42; }") == 1)
    }

    @Test func eqFalse() throws {
        #expect(try compileAndRun("int main() { return 0==1; }") == 0)
    }

    @Test func neTrue() throws {
        #expect(try compileAndRun("int main() { return 0!=1; }") == 1)
    }

    @Test func neFalse() throws {
        #expect(try compileAndRun("int main() { return 42!=42; }") == 0)
    }

    @Test func ltTrue() throws {
        #expect(try compileAndRun("int main() { return 0<1; }") == 1)
    }

    @Test func ltEq() throws {
        #expect(try compileAndRun("int main() { return 1<1; }") == 0)
    }

    @Test func ltFalse() throws {
        #expect(try compileAndRun("int main() { return 2<1; }") == 0)
    }

    @Test func leLess() throws {
        #expect(try compileAndRun("int main() { return 0<=1; }") == 1)
    }

    @Test func leEq() throws {
        #expect(try compileAndRun("int main() { return 1<=1; }") == 1)
    }

    @Test func leFalse() throws {
        #expect(try compileAndRun("int main() { return 2<=1; }") == 0)
    }

    // MARK: - Bitwise

    @Test func bitAnd() throws {
        #expect(try compileAndRun("int main() { return 3&1; }") == 1)
    }

    @Test func bitOr() throws {
        #expect(try compileAndRun("int main() { return 16|3; }") == 19)
    }

    @Test func bitXor() throws {
        #expect(try compileAndRun("int main() { return 56^12; }") == 52)
    }

    @Test func shl() throws {
        #expect(try compileAndRun("int main() { return 1<<3; }") == 8)
    }

    @Test func shr() throws {
        #expect(try compileAndRun("int main() { return 5>>1; }") == 2)
    }

    // MARK: - Logical / bitwise not

    @Test func logNot1() throws {
        #expect(try compileAndRun("int main() { return !1; }") == 0)
    }

    @Test func logNot2() throws {
        #expect(try compileAndRun("int main() { return !2; }") == 0)
    }

    @Test func logNot0() throws {
        #expect(try compileAndRun("int main() { return !0; }") == 1)
    }

    @Test func bitNot() throws {
        #expect(try compileAndRun("int main() { return ~-1; }") == 0)
    }

    // MARK: - Variables

    @Test func varInit() throws {
        #expect(try compileAndRun("int main() { int a=3; return a; }") == 3)
    }

    @Test func twoVars() throws {
        #expect(try compileAndRun("int main() { int a=3; int z=5; return a+z; }") == 8)
    }

    @Test func reassign() throws {
        #expect(try compileAndRun("int main() { int a=3; a=10; return a; }") == 10)
    }

    @Test func computedVar() throws {
        #expect(try compileAndRun("int main() { int a=3; int b=5; int c=a*b; return c; }") == 15)
    }

    @Test func chainAssign() throws {
        #expect(try compileAndRun("int main() { int a; int b; a=b=3; return a+b; }") == 6)
    }

    // MARK: - If/else

    @Test func ifTrue() throws {
        #expect(try compileAndRun("int main() { int x; if (1) x=2; else x=3; return x; }") == 2)
    }

    @Test func ifFalse() throws {
        #expect(try compileAndRun("int main() { int x; if (0) x=2; else x=3; return x; }") == 3)
    }

    @Test func ifExprFalse() throws {
        #expect(try compileAndRun("int main() { int x; if (1-1) x=2; else x=3; return x; }") == 3)
    }

    @Test func ifExprTrue() throws {
        #expect(try compileAndRun("int main() { int x; if (2-1) x=2; else x=3; return x; }") == 2)
    }

    // MARK: - Logical operators (short-circuit)

    @Test func logAndTT() throws {
        #expect(try compileAndRun("int main() { return 1&&5; }") == 1)
    }

    @Test func logAndFT() throws {
        #expect(try compileAndRun("int main() { return 0&&1; }") == 0)
    }

    @Test func logAndFF() throws {
        #expect(try compileAndRun("int main() { return 0&&0; }") == 0)
    }

    @Test func logOrFT() throws {
        #expect(try compileAndRun("int main() { return 0||1; }") == 1)
    }

    @Test func logOrTF() throws {
        #expect(try compileAndRun("int main() { return 1||0; }") == 1)
    }

    @Test func logOrFF() throws {
        #expect(try compileAndRun("int main() { return 0||0; }") == 0)
    }

    @Test func logOrChain() throws {
        #expect(try compileAndRun("int main() { return 0||(2-2)||5; }") == 1)
    }

    // MARK: - Ternary

    @Test func ternaryFalse() throws {
        #expect(try compileAndRun("int main() { return 0?1:2; }") == 2)
    }

    @Test func ternaryTrue() throws {
        #expect(try compileAndRun("int main() { return 1?1:2; }") == 1)
    }

    // MARK: - Comma

    @Test func comma() throws {
        #expect(try compileAndRun("int main() { return (1,2,3); }") == 3)
    }

    // MARK: - Function calls

    @Test func funcNoArgs() throws {
        #expect(try compileAndRun("int ret3(void) { return 3; } int main() { return ret3(); }") == 3)
    }

    @Test func funcTwoArgs() throws {
        #expect(try compileAndRun("int add(int x, int y) { return x+y; } int main() { return add(3,5); }") == 8)
    }

    @Test func funcSub() throws {
        #expect(try compileAndRun("int sub(int x, int y) { return x-y; } int main() { return sub(5,3); }") == 2)
    }

    @Test func funcRecursion() throws {
        #expect(try compileAndRun("int fib(int x) { if (x<=1) return 1; return fib(x-1)+fib(x-2); } int main() { return fib(9); }") == 55)
    }

    @Test func funcCharParams() throws {
        #expect(try compileAndRun("int sub_char(char a, char b, char c) { return a-b-c; } int main() { return sub_char(7,3,3); }") == 1)
    }

    // MARK: - Pointers

    @Test func ptrDeref() throws {
        #expect(try compileAndRun("int main() { int x=3; int *y=&x; return *y; }") == 3)
    }

    @Test func ptrWrite() throws {
        #expect(try compileAndRun("int main() { int x=3; int *y=&x; *y=5; return x; }") == 5)
    }

    @Test func ptrByRef() throws {
        #expect(try compileAndRun("void inc(int *p) { *p = *p + 1; } int main() { int x=41; inc(&x); return x; }") == 42)
    }

    // MARK: - Globals

    @Test func globalInt() throws {
        #expect(try compileAndRun("int g; int main() { g=3; return g; }") == 3)
    }

    @Test func globalInit() throws {
        #expect(try compileAndRun("int g=7; int main() { return g; }") == 7)
    }

    // MARK: - Goto

    @Test func gotoForward() throws {
        #expect(try compileAndRun("int main() { goto end; return 1; end: return 42; }") == 42)
    }

    @Test func gotoSkip() throws {
        #expect(try compileAndRun("int main() { int x=1; goto skip; x=2; skip: return x; }") == 1)
    }

    // MARK: - Sizeof

    @Test func sizeofInt() throws {
        #expect(try compileAndRun("int main() { int x; return sizeof(x); }") == 4)
    }

    @Test func sizeofPtr() throws {
        #expect(try compileAndRun("int main() { int *x; return sizeof(x); }") == 8)
    }

    @Test func sizeofChar() throws {
        #expect(try compileAndRun("int main() { char x; return sizeof(x); }") == 1)
    }

    @Test func sizeofLong() throws {
        #expect(try compileAndRun("int main() { long x; return sizeof(x); }") == 8)
    }

    @Test func sizeofShort() throws {
        #expect(try compileAndRun("int main() { short x; return sizeof(x); }") == 2)
    }

    // MARK: - Loops

    @Test func whileLoop() throws {
        #expect(try compileAndRun("int main() { int i=0; int s=0; while (i<10) { s=s+i; i=i+1; } return s; }") == 45)
    }

    @Test func whileNever() throws {
        #expect(try compileAndRun("int main() { int x=1; while (0) { x=2; } return x; }") == 1)
    }

    @Test func forLoop() throws {
        #expect(try compileAndRun("int main() { int s=0; for (int i=0; i<5; i=i+1) s=s+i; return s; }") == 10)
    }

    @Test func forNested() throws {
        #expect(try compileAndRun("int main() { int s=0; for (int i=0; i<3; i=i+1) for (int j=0; j<3; j=j+1) s=s+1; return s; }") == 9)
    }

    @Test func doWhile() throws {
        #expect(try compileAndRun("int main() { int x=0; do { x=x+1; } while (x<5); return x; }") == 5)
    }

    @Test func doWhileOnce() throws {
        #expect(try compileAndRun("int main() { int x=0; do { x=x+1; } while (0); return x; }") == 1)
    }

    @Test func breakInWhile() throws {
        #expect(try compileAndRun("int main() { int i=0; while (1) { if (i==5) break; i=i+1; } return i; }") == 5)
    }

    @Test func continueInFor() throws {
        #expect(try compileAndRun("int main() { int s=0; for (int i=0; i<10; i=i+1) { if (i%2==0) continue; s=s+i; } return s; }") == 25)
    }

    // MARK: - Switch

    @Test func switchCase() throws {
        #expect(try compileAndRun("int main() { int x=2; switch (x) { case 1: return 10; case 2: return 20; case 3: return 30; } return 0; }") == 20)
    }

    @Test func switchDefault() throws {
        #expect(try compileAndRun("int main() { int x=9; switch (x) { case 1: return 10; default: return 99; } return 0; }") == 99)
    }

    @Test func switchBreak() throws {
        #expect(try compileAndRun("int main() { int x=1; int y=0; switch (x) { case 1: y=10; break; case 2: y=20; break; } return y; }") == 10)
    }

    @Test func switchFallthrough() throws {
        #expect(try compileAndRun("int main() { int x=1; int y=0; switch (x) { case 1: y=y+1; case 2: y=y+2; break; case 3: y=y+4; } return y; }") == 3)
    }

    // MARK: - Compound assignment

    @Test func addAssign() throws {
        #expect(try compileAndRun("int main() { int x=3; x+=7; return x; }") == 10)
    }

    @Test func subAssign() throws {
        #expect(try compileAndRun("int main() { int x=10; x-=3; return x; }") == 7)
    }

    @Test func mulAssign() throws {
        #expect(try compileAndRun("int main() { int x=5; x*=3; return x; }") == 15)
    }

    @Test func divAssign() throws {
        #expect(try compileAndRun("int main() { int x=20; x/=4; return x; }") == 5)
    }

    @Test func modAssign() throws {
        #expect(try compileAndRun("int main() { int x=17; x%=5; return x; }") == 2)
    }

    @Test func andAssign() throws {
        #expect(try compileAndRun("int main() { int x=7; x&=3; return x; }") == 3)
    }

    @Test func orAssign() throws {
        #expect(try compileAndRun("int main() { int x=5; x|=2; return x; }") == 7)
    }

    @Test func xorAssign() throws {
        #expect(try compileAndRun("int main() { int x=15; x^=9; return x; }") == 6)
    }

    @Test func shlAssign() throws {
        #expect(try compileAndRun("int main() { int x=1; x<<=4; return x; }") == 16)
    }

    @Test func shrAssign() throws {
        #expect(try compileAndRun("int main() { int x=32; x>>=3; return x; }") == 4)
    }

    // MARK: - Increment / decrement

    @Test func preIncrement() throws {
        #expect(try compileAndRun("int main() { int x=5; return ++x; }") == 6)
    }

    @Test func postIncrement() throws {
        #expect(try compileAndRun("int main() { int x=5; return x++; }") == 5)
    }

    @Test func preDecrement() throws {
        #expect(try compileAndRun("int main() { int x=5; return --x; }") == 4)
    }

    @Test func postDecrement() throws {
        #expect(try compileAndRun("int main() { int x=5; return x--; }") == 5)
    }

    @Test func incrementEffect() throws {
        #expect(try compileAndRun("int main() { int x=5; x++; return x; }") == 6)
    }

    // MARK: - Arrays

    @Test func arrayBasic() throws {
        #expect(try compileAndRun("int main() { int a[3]; a[0]=1; a[1]=2; a[2]=3; return a[0]+a[1]+a[2]; }") == 6)
    }

    @Test func arrayInit() throws {
        #expect(try compileAndRun("int main() { int a[3]={10,20,30}; return a[1]; }") == 20)
    }

    @Test func arrayPtrArith() throws {
        #expect(try compileAndRun("int main() { int a[3]={10,20,30}; int *p=a; return *(p+2); }") == 30)
    }

    @Test func arraySizeof() throws {
        #expect(try compileAndRun("int main() { int a[5]; return sizeof(a); }") == 20)
    }

    @Test func charArray() throws {
        #expect(try compileAndRun("int main() { char s[4]={72,101,108,0}; return s[0]; }") == 72)
    }

    // MARK: - Structs

    @Test func structBasic() throws {
        #expect(try compileAndRun("int main() { struct { int a; int b; } s; s.a=3; s.b=5; return s.a+s.b; }") == 8)
    }

    @Test func structNested() throws {
        #expect(try compileAndRun("struct P { int x; int y; }; int main() { struct P p; p.x=10; p.y=20; return p.x+p.y; }") == 30)
    }

    @Test func structPtr() throws {
        #expect(try compileAndRun("struct S { int v; }; int main() { struct S s; s.v=42; struct S *p=&s; return p->v; }") == 42)
    }

    @Test func structSizeof() throws {
        #expect(try compileAndRun("struct S { int a; char b; int c; }; int main() { return sizeof(struct S); }") == 12)
    }

    // MARK: - Unions

    @Test func unionBasic() throws {
        #expect(try compileAndRun("int main() { union { int i; char c; } u; u.i=65; return u.c; }") == 65)
    }

    @Test func unionSizeof() throws {
        #expect(try compileAndRun("union U { int a; long b; char c; }; int main() { return sizeof(union U); }") == 8)
    }

    // MARK: - Enums

    @Test func enumBasic() throws {
        #expect(try compileAndRun("enum { A, B, C }; int main() { return C; }") == 2)
    }

    @Test func enumExplicit() throws {
        #expect(try compileAndRun("enum { X=10, Y, Z=20 }; int main() { return Y; }") == 11)
    }

    // MARK: - Casts

    @Test func castIntToChar() throws {
        #expect(try compileAndRun("int main() { int x=256+42; return (char)x; }") == 42)
    }

    @Test func castCharToInt() throws {
        #expect(try compileAndRun("int main() { char c=100; int x=(int)c; return x; }") == 100)
    }

    // MARK: - String literals

    @Test func stringLiteral() throws {
        #expect(try compileAndRun("int main() { char *s=\"Hello\"; return s[0]; }") == 72)
    }

    @Test func stringLength() throws {
        #expect(try compileAndRun("int main() { char *s=\"abcde\"; int i=0; while(s[i]) i++; return i; }") == 5)
    }

    // MARK: - Typedef

    @Test func typedefBasic() throws {
        #expect(try compileAndRun("typedef int myint; int main() { myint x=42; return x; }") == 42)
    }

    @Test func typedefPtr() throws {
        #expect(try compileAndRun("typedef int* intptr; int main() { int x=7; intptr p=&x; return *p; }") == 7)
    }

    // MARK: - Void function

    @Test func voidFunc() throws {
        #expect(try compileAndRun("int g; void set(int v) { g=v; } int main() { set(42); return g; }") == 42)
    }

    // MARK: - Multiple functions / forward decl

    @Test func mutualCall() throws {
        #expect(try compileAndRun("int double_it(int x); int apply(int x) { return double_it(x); } int double_it(int x) { return x*2; } int main() { return apply(21); }") == 42)
    }

    // MARK: - Long type

    @Test func longArith() throws {
        // Use values that fit in exit code range (0-255)
        #expect(try compileAndRun("int main() { long a=100; long b=50; return (int)(a+b); }") == 150)
    }

    // MARK: - Compound literals

    @Test func compoundLiteral() throws {
        #expect(try compileAndRun("struct P { int x; int y; }; int main() { struct P p = (struct P){3, 7}; return p.x+p.y; }") == 10)
    }

    // MARK: - Fixture file tests

    @Test func fixtureTestSimple() throws {
        let asm = try compileFile(fixturePath("test_simple.c"))
        #expect(try assembleAndRun(asm) == 42)
    }

    @Test func fixtureDemo() throws {
        // fib(10)=55, abs(-5)=5, return 55+5=60
        let asm = try compileFile(fixturePath("demo.c"))
        #expect(try assembleAndRun(asm) == 60)
    }

    @Test func fixtureTestSSA() throws {
        // x=1, if(x) x=2 else x=3 → return 2
        let asm = try compileFile(fixturePath("test_ssa.c"))
        #expect(try assembleAndRun(asm) == 2)
    }

    @Test func fixtureTestSSA2() throws {
        // test(1)=10, test(0)=20 → return 30
        let asm = try compileFile(fixturePath("test_ssa2.c"))
        #expect(try assembleAndRun(asm) == 30)
    }

    @Test func fixtureOptTest() throws {
        // mul3(7)=21, mul8(2)=16, udiv4(100)=25, umod8(15)=7 → 69
        let asm = try compileFile(fixturePath("opt_test.c"))
        #expect(try assembleAndRun(asm) == 69)
    }

    // MARK: - Chibicc test suite

    /// Compile a chibicc test `.c` file through Civet, compile `common` with gcc,
    /// link both, run, and return the exit code (0 = all ASSERT()s passed).
    private func compileAndRunChibiccTest(_ name: String) throws -> Int32 {
        let chibiccDir = projectRoot + "/Tests/CivetTests/Fixtures/chibicc"
        let testPath = chibiccDir + "/" + name
        let commonPath = chibiccDir + "/common"

        let tmp = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tmp, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tmp) }

        // Compile common with gcc (it uses libc: stdio, stdlib, stdarg)
        let commonObj = tmp.appendingPathComponent("common.o").path
        let gccCommon = Process()
        gccCommon.executableURL = URL(fileURLWithPath: "/usr/bin/gcc")
        gccCommon.arguments = ["-c", "-o", commonObj, "-xc", commonPath]
        gccCommon.standardError = FileHandle.nullDevice
        try gccCommon.run()
        gccCommon.waitUntilExit()
        guard gccCommon.terminationStatus == 0 else {
            throw TestError.compileError("gcc failed to compile common")
        }

        // Compile test file through Civet pipeline
        let asm = try compileFile(testPath, includePaths: [chibiccDir])

        // Assemble, link with common (-pthread as in chibicc Makefile), and run
        return try assembleAndRun(asm, extraObjects: [commonObj, "-pthread"])
    }

    // Passing chibicc tests
    @Test func chibiccUnion() throws {
        #expect(try compileAndRunChibiccTest("union.c") == 0)
    }

    @Test func chibiccEnum() throws {
        #expect(try compileAndRunChibiccTest("enum.c") == 0)
    }

    @Test func chibiccSizeof() throws {
        #expect(try compileAndRunChibiccTest("sizeof.c") == 0)
    }

    @Test func chibiccString() throws {
        #expect(try compileAndRunChibiccTest("string.c") == 0)
    }

    @Test func chibiccTypedef() throws {
        #expect(try compileAndRunChibiccTest("typedef.c") == 0)
    }

    @Test func chibiccDecl() throws {
        #expect(try compileAndRunChibiccTest("decl.c") == 0)
    }

    @Test func chibiccConst() throws {
        #expect(try compileAndRunChibiccTest("const.c") == 0)
    }

    @Test func chibiccUsualconv() throws {
        #expect(try compileAndRunChibiccTest("usualconv.c") == 0)
    }

    @Test func chibiccCompat() throws {
        #expect(try compileAndRunChibiccTest("compat.c") == 0)
    }

    @Test func chibiccGeneric() throws {
        #expect(try compileAndRunChibiccTest("generic.c") == 0)
    }

    @Test func chibiccTypeof() throws {
        #expect(try compileAndRunChibiccTest("typeof.c") == 0)
    }

    @Test func chibiccExtern() throws {
        #expect(try compileAndRunChibiccTest("extern.c") == 0)
    }

    @Test func chibiccLine() throws {
        #expect(try compileAndRunChibiccTest("line.c") == 0)
    }

    @Test func chibiccAsm() throws {
        #expect(try compileAndRunChibiccTest("asm.c") == 0)
    }

    @Test func chibiccBuiltin() throws {
        #expect(try compileAndRunChibiccTest("builtin.c") == 0)
    }

    @Test func chibiccStdhdr() throws {
        #expect(try compileAndRunChibiccTest("stdhdr.c") == 0)
    }

    // Previously failing chibicc tests — now passing with workarounds
    @Test func chibiccArith() throws {
        #expect(try compileAndRunChibiccTest("arith.c") == 0)
    }

    @Test func chibiccVariable() throws {
        #expect(try compileAndRunChibiccTest("variable.c") == 0)
    }

    @Test func chibiccControl() throws {
        #expect(try compileAndRunChibiccTest("control.c") == 0)
    }

    @Test(.disabled("codegen: long double (x87)"))
    func chibiccFunction() throws {
        #expect(try compileAndRunChibiccTest("function.c") == 0)
    }

    @Test func chibiccPointer() throws {
        #expect(try compileAndRunChibiccTest("pointer.c") == 0)
    }

    @Test func chibiccStruct() throws {
        #expect(try compileAndRunChibiccTest("struct.c") == 0)
    }

    @Test func chibiccCast() throws {
        #expect(try compileAndRunChibiccTest("cast.c") == 0)
    }

    @Test(.disabled("codegen: anonymous struct designated initializer"))
    func chibiccInitializer() throws {
        #expect(try compileAndRunChibiccTest("initializer.c") == 0)
    }

    @Test func chibiccLiteral() throws {
        #expect(try compileAndRunChibiccTest("literal.c") == 0)
    }

    @Test func chibiccComplit() throws {
        #expect(try compileAndRunChibiccTest("complit.c") == 0)
    }

    @Test func chibiccCommonsym() throws {
        #expect(try compileAndRunChibiccTest("commonsym.c") == 0)
    }

    @Test func chibiccConstexpr() throws {
        #expect(try compileAndRunChibiccTest("constexpr.c") == 0)
    }

    @Test(.disabled("codegen: alignment"))
    func chibiccAlignof() throws {
        #expect(try compileAndRunChibiccTest("alignof.c") == 0)
    }

    @Test func chibiccAttribute() throws {
        #expect(try compileAndRunChibiccTest("attribute.c") == 0)
    }

    @Test func chibiccBitfield() throws {
        #expect(try compileAndRunChibiccTest("bitfield.c") == 0)
    }

    @Test func chibiccOffsetof() throws {
        #expect(try compileAndRunChibiccTest("offsetof.c") == 0)
    }

    @Test(.disabled("codegen: macro edge cases"))
    func chibiccMacro() throws {
        #expect(try compileAndRunChibiccTest("macro.c") == 0)
    }

    @Test(.disabled("codegen: pragma once"))
    func chibiccPragmaOnce() throws {
        #expect(try compileAndRunChibiccTest("pragma-once.c") == 0)
    }

    @Test func chibiccFloat() throws {
        #expect(try compileAndRunChibiccTest("float.c") == 0)
    }

    @Test(.disabled("codegen: 2D VLA element access"))
    func chibiccVla() throws {
        #expect(try compileAndRunChibiccTest("vla.c") == 0)
    }

    @Test func chibiccAlloca() throws {
        #expect(try compileAndRunChibiccTest("alloca.c") == 0)
    }

    @Test(.disabled("codegen: varargs"))
    func chibiccVarargs() throws {
        #expect(try compileAndRunChibiccTest("varargs.c") == 0)
    }

    @Test func chibiccUnicode() throws {
        #expect(try compileAndRunChibiccTest("unicode.c") == 0)
    }

    // MARK: - Memory / arena reset

    private func fixturePath(_ name: String) -> String {
        return projectRoot + "/Tests/CivetTests/Fixtures/" + name
    }

    private var defaultIncludePaths: [String] {
        [
            projectRoot + "/Tests/CivetTests/Fixtures",
            projectRoot + "/Resources/chibicc-builtins",
            "/usr/local/include",
            "/usr/include/x86_64-linux-gnu",
            "/usr/include",
        ]
    }

    @Test func repeatedParseDoesNotLeak() throws {
        let path = fixturePath("demo.c")
        for _ in 0..<50 {
            let mapper = SyntaxMapper()
            _ = try mapper.parseFile(path, includePaths: defaultIncludePaths)
        }
    }

    @Test func parseDifferentFilesSequentially() throws {
        let files = ["demo.c", "test_simple.c"]
        for file in files {
            let path = fixturePath(file)
            guard FileManager.default.fileExists(atPath: path) else { continue }
            let mapper = SyntaxMapper()
            let result = try mapper.parseFile(path, includePaths: defaultIncludePaths)
            #expect(!result.declarations.isEmpty)
        }
    }
}
