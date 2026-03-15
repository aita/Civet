import COIL
import Foundation
import Machine
import Parser
import Tree

final class StderrOutputStream: TextOutputStream {
    nonisolated(unsafe) static var shared = StderrOutputStream()
    func write(_ string: String) {
        FileHandle.standardError.write(Data(string.utf8))
    }
}

@main
struct Civet {
    static func main() {
        let args = CommandLine.arguments
        guard args.count >= 2 else {
            print("Usage: civet <file.c>")
            return
        }
        let path = args[1]

        let dirParts = path.components(separatedBy: "/")
        let dir = dirParts.count > 1 ? dirParts.dropLast(1).joined(separator: "/") : "."
        let parent = dirParts.count > 2 ? dirParts.dropLast(2).joined(separator: "/") : "."

        let exeParts = CommandLine.arguments[0].components(separatedBy: "/")
        let projectDir = exeParts.dropLast(3).joined(separator: "/")
        let chibiccBuiltins = (projectDir.isEmpty ? "." : projectDir) + "/Resources/chibicc-builtins"

        let includePaths = [
            dir, parent, chibiccBuiltins,
            "/usr/local/include",
            "/usr/include/x86_64-linux-gnu",
            "/usr/include",
        ]

        do {
            let syntaxUnit = try parseFile(path, includePaths: includePaths)
            let treeUnit = SyntaxConverter().convert(syntaxUnit)
            let coil = TreeConverter().convert(treeUnit)
            if CommandLine.arguments.contains("--dump-coil") {
                print(coil.dotRepresentation(), to: &StderrOutputStream.shared)
            }
            let ssa = SSABuilder().build(coil)
            if CommandLine.arguments.contains("--dump-ssa") {
                print(ssa.dotRepresentation(), to: &StderrOutputStream.shared)
            }
            let program = optimize(ssa)
            if CommandLine.arguments.contains("--dump-opt") {
                print(program.dotRepresentation(), to: &StderrOutputStream.shared)
            }
            var converter = COILConverter()
            let machProg = converter.convert(program)
            let resolved = resolveConstraints(machProg)
            let allocated = allocateRegisters(resolved)
            let expanded = expandParallelCopies(allocated)
            let optimized = peephole(expanded)
            let legalized = fixIllegalInstructions(optimized)
            let scheduled = schedule(legalized)
            print(AsmPrinter().emit(scheduled))
        } catch {
            print("Error: \(error) — \(path)")
        }
    }
}
