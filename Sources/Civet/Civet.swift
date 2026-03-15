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

// MARK: - Toolchain Discovery

struct Toolchain {
    let assembler: String  // path to `as`
    let linker: String     // path to `ld`
    let crtDir: String     // directory containing crt1.o, crti.o, crtn.o
    let dynamicLinker: String  // e.g. /lib64/ld-linux-x86-64.so.2
}

func findToolchain() -> Toolchain? {
    let fm = FileManager.default

    // Find assembler
    let asCandidates = ["/usr/bin/as"]
    guard let asPath = asCandidates.first(where: { fm.isExecutableFile(atPath: $0) })
        ?? findInPath("as")
    else {
        printError("error: cannot find assembler (as)")
        return nil
    }

    // Find linker
    let ldCandidates = ["/usr/bin/ld"]
    guard let ldPath = ldCandidates.first(where: { fm.isExecutableFile(atPath: $0) })
        ?? findInPath("ld")
    else {
        printError("error: cannot find linker (ld)")
        return nil
    }

    // Find CRT directory
    let crtDirs = [
        "/usr/lib/x86_64-linux-gnu",  // Debian/Ubuntu
        "/usr/lib64",                   // RHEL/Fedora
        "/usr/lib",                     // Arch
    ]
    let crtFiles = ["crt1.o", "crti.o", "crtn.o"]
    guard let crtDir = crtDirs.first(where: { dir in
        crtFiles.allSatisfy { fm.fileExists(atPath: dir + "/" + $0) }
    }) else {
        printError("error: cannot find CRT files (crt1.o, crti.o, crtn.o)")
        return nil
    }

    // Find dynamic linker
    let dynLinkers = [
        "/lib64/ld-linux-x86-64.so.2",
        "/lib/ld-linux-x86-64.so.2",
    ]
    guard let dynLinker = dynLinkers.first(where: { fm.fileExists(atPath: $0) }) else {
        printError("error: cannot find dynamic linker (ld-linux-x86-64.so.2)")
        return nil
    }

    return Toolchain(assembler: asPath, linker: ldPath, crtDir: crtDir, dynamicLinker: dynLinker)
}

private func findInPath(_ tool: String) -> String? {
    guard let path = ProcessInfo.processInfo.environment["PATH"] else { return nil }
    let fm = FileManager.default
    for dir in path.split(separator: ":") {
        let candidate = "\(dir)/\(tool)"
        if fm.isExecutableFile(atPath: candidate) { return candidate }
    }
    return nil
}

private func printError(_ message: String) {
    print(message, to: &StderrOutputStream.shared)
}

// MARK: - Subprocess Execution

@discardableResult
func run(_ executable: String, _ arguments: [String]) -> Int32 {
    let process = Process()
    process.executableURL = URL(fileURLWithPath: executable)
    process.arguments = arguments
    let stderrPipe = Pipe()
    process.standardError = stderrPipe
    do {
        try process.run()
        process.waitUntilExit()
        if process.terminationStatus != 0 {
            let errData = stderrPipe.fileHandleForReading.readDataToEndOfFile()
            if let errStr = String(data: errData, encoding: .utf8), !errStr.isEmpty {
                printError(errStr)
            }
        }
        return process.terminationStatus
    } catch {
        printError("error: failed to run \(executable): \(error)")
        return 1
    }
}

// MARK: - CLI Argument Parsing

struct CLIOptions {
    var inputFile: String?
    var outputFile: String?
    var emitAssembly = false   // -S
    var compileOnly = false    // -c
    var extraLinkerFlags: [String] = []
    var dumpFlags: [String] = []  // --dump-coil, --dump-ssa, etc.
}

func parseArguments(_ args: [String]) -> CLIOptions {
    var opts = CLIOptions()
    var i = 1  // skip argv[0]
    while i < args.count {
        let arg = args[i]
        switch arg {
        case "-o":
            i += 1
            if i < args.count { opts.outputFile = args[i] }
        case "-S":
            opts.emitAssembly = true
        case "-c":
            opts.compileOnly = true
        case _ where arg.hasPrefix("-l"):
            opts.extraLinkerFlags.append(arg)
        case _ where arg.hasPrefix("--dump-"):
            opts.dumpFlags.append(arg)
        default:
            if opts.inputFile == nil { opts.inputFile = arg }
        }
        i += 1
    }
    return opts
}

// MARK: - Main

@main
struct Civet {
    static func main() {
        let args = CommandLine.arguments
        let opts = parseArguments(args)

        guard let path = opts.inputFile else {
            print("Usage: civet <file.c> [-o output] [-S] [-c] [-lLIB...]")
            return
        }

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
            if opts.dumpFlags.contains("--dump-coil") {
                print(coil.dotRepresentation(), to: &StderrOutputStream.shared)
            }
            let sroa = scalarReplacement(coil)
            if opts.dumpFlags.contains("--dump-sroa") {
                print(sroa.dotRepresentation(), to: &StderrOutputStream.shared)
            }
            let ssa = SSABuilder().build(sroa)
            if opts.dumpFlags.contains("--dump-ssa") {
                print(ssa.dotRepresentation(), to: &StderrOutputStream.shared)
            }
            let program = optimize(ssa)
            if opts.dumpFlags.contains("--dump-opt") {
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
            let assembly = AsmPrinter().emit(scheduled)

            // Determine output mode
            if opts.outputFile == nil && !opts.compileOnly {
                // No -o: emit assembly to stdout (original behavior)
                print(assembly)
                return
            }

            if opts.emitAssembly {
                // -S -o file.s: write assembly to file
                if let outPath = opts.outputFile {
                    try assembly.write(toFile: outPath, atomically: true, encoding: String.Encoding.utf8)
                } else {
                    print(assembly)
                }
                return
            }

            // Need toolchain for assembly/linking
            guard let tc = findToolchain() else {
                Foundation.exit(1)
            }

            // Write assembly to temp file
            let tmpDir = NSTemporaryDirectory()
            let asmPath = tmpDir + "civet_\(ProcessInfo.processInfo.processIdentifier).s"
            let objPath = tmpDir + "civet_\(ProcessInfo.processInfo.processIdentifier).o"
            defer {
                try? FileManager.default.removeItem(atPath: asmPath)
                try? FileManager.default.removeItem(atPath: objPath)
            }
            try assembly.write(toFile: asmPath, atomically: true, encoding: String.Encoding.utf8)

            // Assemble
            let asStatus = run(tc.assembler, ["--noexecstack", "-o", objPath, asmPath])
            guard asStatus == 0 else {
                printError("error: assembler failed")
                Foundation.exit(1)
            }

            if opts.compileOnly {
                // -c -o file.o: just produce object file
                let outPath = opts.outputFile ?? path.replacingOccurrences(of: ".c", with: ".o")
                try FileManager.default.moveItem(atPath: objPath, toPath: outPath)
                return
            }

            // Link
            let outPath = opts.outputFile ?? "a.out"
            var ldArgs = [
                "-o", outPath,
                "-dynamic-linker", tc.dynamicLinker,
                tc.crtDir + "/crt1.o",
                tc.crtDir + "/crti.o",
                objPath,
                "-lc",
            ]
            ldArgs.append(contentsOf: opts.extraLinkerFlags)
            ldArgs.append(tc.crtDir + "/crtn.o")

            let ldStatus = run(tc.linker, ldArgs)
            guard ldStatus == 0 else {
                printError("error: linker failed")
                Foundation.exit(1)
            }

        } catch {
            printError("Error: \(error) — \(path)")
            Foundation.exit(1)
        }
    }
}
