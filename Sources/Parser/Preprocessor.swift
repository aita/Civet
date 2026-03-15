// C preprocessor.
// Ported from chibicc's preprocess.c.

import Foundation
import Common
import Syntax

// MARK: - Macro

struct Macro {
    var name: String
    var isObjlike: Bool
    var params: [String]
    var vaArgsName: String?
    var body: [Token]
    var handler: ((Token, Preprocessor) throws -> [Token])?
}

// MARK: - Conditional inclusion

private enum CondContext { case inThen, inElif, inElse }
private struct CondIncl {
    var ctx: CondContext
    var included: Bool    // is the current branch active?
    var branchTaken: Bool // has any prior branch been taken?
    var loc: SourceLocation
}

// MARK: - Preprocessor

public class Preprocessor {
    public var includePaths: [String] = []
    public var baseFile: String = ""

    var macros: [String: Macro] = [:]
    private var processDepth: Int = 0
    private var condStack: [CondIncl] = []
    private var pragmaOnceFiles: Set<String> = []
    private var counterValue: Int = 0
    private var fileNo: Int = 2  // 1 reserved for the main file

    private var isSkipping: Bool {
        condStack.contains { !$0.included }
    }

    /// Per-file #line adjustment: maps fileName → (delta, overrideName)
    /// delta is added to token's real lineNo. overrideName replaces fileName.
    private var lineAdjust: [String: (delta: Int, file: String?)] = [:]
    private let dateStr: String
    private let timeStr: String
    private let timestampStr: String

    public init() {
        let now = Date()
        let df = DateFormatter()
        df.locale = Locale(identifier: "en_US_POSIX")
        df.dateFormat = "MMM dd yyyy"
        dateStr = "\"\(df.string(from: now))\""
        df.dateFormat = "HH:mm:ss"
        timeStr = "\"\(df.string(from: now))\""
        // __TIMESTAMP__: asctime format "Day Mon DD HH:MM:SS YYYY"
        df.dateFormat = "EEE MMM dd HH:mm:ss yyyy"
        timestampStr = "\"\(df.string(from: now))\""
        initMacros()
    }

    // MARK: - Public API

    public func preprocess(_ tokens: [Token]) throws -> [Token] {
        var result = try process(tokens)
        result = concatenateStringLiterals(result)
        convertPPTokens(&result)
        return result
    }

    // MARK: - Main processing loop

    private func process(_ tokens: [Token]) throws -> [Token] {
        processDepth += 1
        defer { processDepth -= 1 }
        if processDepth > 200 {
            throw ParseError("macro expansion depth exceeded", tokens.first?.loc ?? SourceLocation(fileName: "", line: 0, column: 0))
        }
        var out: [Token] = []
        // Use a mutable cursor into a contiguous token array.
        // When a macro is expanded, splice the result in-place
        // so we loop rather than recurse for each top-level expansion.
        var buf = tokens
        var i = 0
        while i < buf.count {
            let tok = buf[i]

            if tok.kind == .eof { out.append(tok); break }

            // Directive: '#' at beginning of line
            if tok.atBOL && tok.text == "#" {
                i = try processDirective(buf, i: i + 1, out: &out)
                continue
            }

            // Skip non-directive tokens inside false conditional blocks
            if isSkipping {
                i += 1
                continue
            }

            // Macro expansion — iterative splice instead of recursive process()
            if tok.kind == .ident, let macro = macros[tok.text], !tok.hideset.contains(tok.text) {
                let (expanded, next) = try expandMacro(buf, at: i, macro: macro)
                // Splice: replace buf[i..<next] with expanded tokens
                buf.replaceSubrange(i..<next, with: expanded)
                // Don't advance i — re-examine from the same position
                // (the expanded tokens may contain more macros to expand)
                continue
            }

            out.append(adjustLine(tok))
            i += 1
        }
        return out
    }

    /// Apply #line adjustments to a token.
    private func adjustLine(_ tok: Token) -> Token {
        guard let adj = lineAdjust[tok.fileName] else { return tok }
        var t = tok
        t.lineNo += adj.delta
        if let f = adj.file { t.fileName = f }
        return t
    }

    // MARK: - Directive dispatch

    private func processDirective(_ tokens: [Token], i startI: Int, out: inout [Token]) throws -> Int {
        let i = startI
        guard i < tokens.count else { return i }

        let dir = tokens[i]

        // Null directive
        if dir.atBOL || dir.kind == .eof { return i }

        // Check if inside a skipped conditional block
        let topSkipping = condStack.last.map({ !$0.included }) ?? false
        let outerSkipping = condStack.dropLast().contains { !$0.included }
        if topSkipping || outerSkipping {
            // Only process conditional directives when skipping
            if dir.kind == .ident {
                switch dir.text {
                case "if", "ifdef", "ifndef":
                    // Push a nested cond that stays skipped
                    condStack.append(CondIncl(ctx: .inThen, included: true, branchTaken: true, loc: dir.loc))
                    return skipLine(tokens, from: i + 1)
                case "elif":
                    if !outerSkipping {
                        return try handleElif(tokens, i: i + 1)
                    }
                    return skipLine(tokens, from: i + 1)
                case "else":
                    if !outerSkipping {
                        return try handleElse(tokens, i: i + 1)
                    }
                    return skipLine(tokens, from: i + 1)
                case "endif":
                    condStack.removeLast()
                    return skipLine(tokens, from: i + 1)
                default:
                    return skipLine(tokens, from: i)
                }
            }
            return skipLine(tokens, from: i)
        }

        guard dir.kind == .ident else {
            // GNU line marker: `# NNN "file" [flags]`
            if dir.kind == .ppNum || dir.kind == .num {
                return handleGNULineMarker(tokens, i: i)
            }
            // Single '#' on a line with non-ident — skip
            return skipLine(tokens, from: i)
        }

        switch dir.text {
        case "include":
            return try handleInclude(tokens, i: i + 1, out: &out)
        case "include_next":
            return try handleIncludeNext(tokens, i: i + 1, out: &out)
        case "define":
            return try handleDefine(tokens, i: i + 1)
        case "undef":
            return handleUndef(tokens, i: i + 1)
        case "if":
            return try handleIf(tokens, i: i + 1)
        case "ifdef":
            return try handleIfdef(tokens, i: i + 1, negate: false)
        case "ifndef":
            return try handleIfdef(tokens, i: i + 1, negate: true)
        case "elif":
            return try handleElif(tokens, i: i + 1)
        case "else":
            return try handleElse(tokens, i: i + 1)
        case "endif":
            return try handleEndif(tokens, i: i + 1)
        case "line":
            return try handleLine(tokens, i: i + 1)
        case "error":
            throw ParseError("#error \(collectLineText(tokens, from: i + 1))", dir.loc)
        case "pragma":
            return handlePragma(tokens, i: i + 1)
        default:
            // Unknown directive — skip
            return skipLine(tokens, from: i + 1)
        }
    }

    // MARK: - #include / #include_next

    private func handleInclude(_ tokens: [Token], i: Int, out: inout [Token]) throws -> Int {
        // Expand macros in the include line first
        let (lineTokens, next) = collectLine(tokens, from: i)
        let expanded = try process(lineTokens)
        let included = try resolveInclude(expanded, searchCurrent: true, loc: tokens[i > 0 ? i - 1 : i].loc)
        out.append(contentsOf: included)
        return next
    }

    private func handleIncludeNext(_ tokens: [Token], i: Int, out: inout [Token]) throws -> Int {
        let (lineTokens, next) = collectLine(tokens, from: i)
        let expanded = try process(lineTokens)
        let included = try resolveInclude(expanded, searchCurrent: false, loc: tokens[i > 0 ? i - 1 : i].loc)
        out.append(contentsOf: included)
        return next
    }

    private func resolveInclude(_ tokens: [Token], searchCurrent: Bool, loc: SourceLocation) throws -> [Token] {
        guard !tokens.isEmpty else { throw ParseError("expected filename", loc) }

        var path: String
        var searchFromCurrent: Bool

        if tokens[0].kind == .str {
            // #include "foo.h"
            path = String(tokens[0].text.dropFirst().dropLast())
            searchFromCurrent = searchCurrent
        } else if tokens[0].text == "<" {
            // #include <foo.h>
            var parts: [String] = []
            var j = 1
            while j < tokens.count && tokens[j].text != ">" {
                if tokens[j].hasSpace && !parts.isEmpty { parts.append(" ") }
                parts.append(tokens[j].text)
                j += 1
            }
            path = parts.joined()
            searchFromCurrent = false
        } else {
            throw ParseError("expected filename", loc)
        }

        let resolved = try findIncludeFile(path, from: loc.fileName, searchCurrent: searchFromCurrent)

        // Pragma once check
        let canonical = resolveCanonicalPath(resolved)
        if pragmaOnceFiles.contains(canonical) {
            return []
        }

        let source = try String(contentsOfFile: resolved, encoding: .utf8)
        let fno = fileNo
        fileNo += 1
        var lexer = Lexer(source: source, fileName: resolved, fileNo: fno)
        let fileTokens = try lexer.tokenize()
        // Remove the EOF token so we can splice
        var toks = fileTokens
        if let last = toks.last, last.kind == .eof { toks.removeLast() }
        return try process(toks)
    }

    private func findIncludeFile(_ path: String, from currentFile: String, searchCurrent: Bool) throws -> String {
        let fm = FileManager.default

        if searchCurrent {
            // Search relative to current file
            let dir = (currentFile as NSString).deletingLastPathComponent
            let candidate = (dir as NSString).appendingPathComponent(path)
            if fm.fileExists(atPath: candidate) { return candidate }
        }

        for dir in includePaths {
            let candidate = (dir as NSString).appendingPathComponent(path)
            if fm.fileExists(atPath: candidate) { return candidate }
        }

        throw ParseError("'\(path)': file not found", SourceLocation(fileName: currentFile, line: 0, column: 0))
    }

    private func resolveCanonicalPath(_ path: String) -> String {
        (path as NSString).standardizingPath
    }

    // MARK: - #define

    private func handleDefine(_ tokens: [Token], i: Int) throws -> Int {
        guard i < tokens.count, tokens[i].kind == .ident else {
            throw ParseError("macro name must be an identifier", tokens[max(0, i - 1)].loc)
        }
        let name = tokens[i].text
        var j = i + 1

        // Function-like macro: name immediately followed by '(' (no space)
        if j < tokens.count && tokens[j].text == "(" && !tokens[j].hasSpace {
            j += 1
            var params: [String] = []
            var vaArgsName: String? = nil

            if j < tokens.count && tokens[j].text != ")" {
                while true {
                    if tokens[j].text == "..." {
                        vaArgsName = "__VA_ARGS__"
                        j += 1
                        break
                    }
                    guard tokens[j].kind == .ident else {
                        throw ParseError("expected parameter name", tokens[j].loc)
                    }
                    let pname = tokens[j].text
                    j += 1

                    if j < tokens.count && tokens[j].text == "..." {
                        vaArgsName = pname
                        j += 1
                        break
                    }
                    params.append(pname)
                    if j < tokens.count && tokens[j].text == "," {
                        j += 1
                    } else {
                        break
                    }
                }
            }
            guard j < tokens.count && tokens[j].text == ")" else {
                throw ParseError("expected ')' in macro parameter list", tokens[j < tokens.count ? j : i].loc)
            }
            j += 1

            let (body, next) = collectLine(tokens, from: j)
            macros[name] = Macro(name: name, isObjlike: false, params: params, vaArgsName: vaArgsName, body: body)
            return next
        }

        // Object-like macro
        let (body, next) = collectLine(tokens, from: j)
        macros[name] = Macro(name: name, isObjlike: true, params: [], vaArgsName: nil, body: body)
        return next
    }

    // MARK: - #undef

    private func handleUndef(_ tokens: [Token], i: Int) -> Int {
        if i < tokens.count && tokens[i].kind == .ident {
            macros.removeValue(forKey: tokens[i].text)
        }
        return skipLine(tokens, from: i + 1)
    }

    // MARK: - Conditionals

    private func handleIf(_ tokens: [Token], i: Int) throws -> Int {
        let (lineTokens, next) = collectLine(tokens, from: i)
        let val = try evalConstExpr(lineTokens)
        condStack.append(CondIncl(ctx: .inThen, included: val != 0, branchTaken: val != 0, loc: tokens[i > 0 ? i - 1 : 0].loc))
        return next
    }

    private func handleIfdef(_ tokens: [Token], i: Int, negate: Bool) throws -> Int {
        guard i < tokens.count, tokens[i].kind == .ident else {
            throw ParseError("expected identifier", tokens[max(0, i - 1)].loc)
        }
        var defined = macros[tokens[i].text] != nil
        if negate { defined = !defined }
        condStack.append(CondIncl(ctx: .inThen, included: defined, branchTaken: defined, loc: tokens[i].loc))
        return skipLine(tokens, from: i + 1)
    }

    private func handleElif(_ tokens: [Token], i: Int) throws -> Int {
        guard !condStack.isEmpty else {
            throw ParseError("stray #elif", tokens[max(0, i - 1)].loc)
        }
        let top = condStack.removeLast()
        if top.ctx == .inElse {
            throw ParseError("#elif after #else", tokens[max(0, i - 1)].loc)
        }

        if top.branchTaken {
            // A previous branch was taken; skip this one
            condStack.append(CondIncl(ctx: .inElif, included: false, branchTaken: true, loc: top.loc))
            return skipLine(tokens, from: i)
        }

        let (lineTokens, next) = collectLine(tokens, from: i)
        let val = try evalConstExpr(lineTokens)
        let taken = val != 0
        condStack.append(CondIncl(ctx: .inElif, included: taken, branchTaken: top.branchTaken || taken, loc: top.loc))
        return next
    }

    private func handleElse(_ tokens: [Token], i: Int) throws -> Int {
        guard !condStack.isEmpty else {
            throw ParseError("stray #else", tokens[max(0, i - 1)].loc)
        }
        let top = condStack.removeLast()
        if top.ctx == .inElse {
            throw ParseError("#else after #else", tokens[max(0, i - 1)].loc)
        }
        condStack.append(CondIncl(ctx: .inElse, included: !top.branchTaken, branchTaken: true, loc: top.loc))
        return skipLine(tokens, from: i)
    }

    private func handleEndif(_ tokens: [Token], i: Int) throws -> Int {
        guard !condStack.isEmpty else {
            throw ParseError("stray #endif", tokens[max(0, i - 1)].loc)
        }
        condStack.removeLast()
        return skipLine(tokens, from: i)
    }

    // MARK: - #line

    private func handleLine(_ tokens: [Token], i: Int) throws -> Int {
        // Expand macros in the #line arguments
        let (lineTokens, next) = collectLine(tokens, from: i)
        let expanded = try process(lineTokens)
        return applyLineDirective(expanded, sourceFile: tokens[i > 0 ? i - 1 : 0].fileName,
                                  sourceLine: tokens[i > 0 ? i - 1 : 0].lineNo, next: next)
    }

    /// Handle GNU line marker: `# NNN "file" [flags]`
    private func handleGNULineMarker(_ tokens: [Token], i: Int) -> Int {
        return applyLineDirective(Array(tokens[i...]), sourceFile: tokens[i].fileName,
                                  sourceLine: tokens[i].lineNo, next: skipLine(tokens, from: i))
    }

    private func applyLineDirective(_ args: [Token], sourceFile: String, sourceLine: Int, next: Int) -> Int {
        guard let first = args.first, first.kind == .ppNum || first.kind == .num,
              let lineNum = Int(first.text) else {
            return next
        }
        // delta = desired lineNo - real lineNo of the token that will follow
        // The token after the directive is on the next physical line from the directive
        let delta = lineNum - sourceLine
        var fileOverride: String? = nil
        if args.count >= 2 && args[1].kind == .str {
            var fname = args[1].text
            // Strip quotes
            if fname.hasPrefix("\"") && fname.hasSuffix("\"") {
                fname = String(fname.dropFirst().dropLast())
            }
            fileOverride = fname
        }
        lineAdjust[sourceFile] = (delta: delta, file: fileOverride)
        return next
    }

    // MARK: - #pragma

    private func handlePragma(_ tokens: [Token], i: Int) -> Int {
        if i < tokens.count && tokens[i].kind == .ident && tokens[i].text == "once" {
            let file = tokens[i].fileName
            let canonical = resolveCanonicalPath(file)
            pragmaOnceFiles.insert(canonical)
        }
        return skipLine(tokens, from: i)
    }

    // MARK: - Macro expansion

    private func expandMacro(_ tokens: [Token], at pos: Int, macro: Macro) throws -> ([Token], Int) {
        let invocation = tokens[pos]

        // Built-in handler
        if let handler = macro.handler {
            let result = try handler(adjustLine(invocation), self)
            return (result, pos + 1)
        }

        // Object-like
        if macro.isObjlike {
            var body = macro.body
            let hs = invocation.hideset.union([macro.name])
            for k in body.indices {
                body[k].hideset = body[k].hideset.union(hs)
                body[k].fileName = invocation.fileName
                body[k].lineNo = invocation.lineNo
            }
            // First token inherits hasSpace from invocation
            if !body.isEmpty { body[0].hasSpace = invocation.hasSpace }
            return (body, pos + 1)
        }

        // Function-like: need '(' after macro name
        var j = pos + 1
        // Skip non-newline tokens? No — just check if next is '('
        if j >= tokens.count || tokens[j].text != "(" {
            // Not a macro invocation — add macro name to hideset to prevent infinite loop
            var tok = invocation
            tok.hideset = tok.hideset.union([macro.name])
            return ([tok], pos + 1)
        }
        j += 1 // skip '('

        // Collect arguments
        let (args, rparen) = try collectArgs(tokens, from: j, macro: macro)
        let next = rparen + 1

        // Pre-expand arguments (Prosser algorithm: expand args before substitution,
        // except for # and ## operands which use raw args)
        var expandedArgs: [[Token]] = []
        for arg in args {
            let expanded = try process(arg)
            expandedArgs.append(expanded)
        }

        // Compute hideset: intersection of macro token and rparen hidesets, plus macro name
        let hs = invocation.hideset.intersection(tokens[rparen].hideset).union([macro.name])

        // Substitute (uses expandedArgs for normal substitution, raw args for #/##)
        let result = try substitute(macro: macro, args: expandedArgs, rawArgs: args, hs: hs, loc: invocation)
        return (result, next)
    }

    private func collectArgs(_ tokens: [Token], from start: Int, macro: Macro) throws -> ([[Token]], Int) {
        var args: [[Token]] = []
        var current: [Token] = []
        var depth = 0
        var i = start
        let paramCount = macro.params.count
        let hasVaArgs = macro.vaArgsName != nil

        if i < tokens.count && tokens[i].text == ")" {
            // No arguments
            return (args, i)
        }

        while i < tokens.count {
            let tok = tokens[i]
            if tok.kind == .eof {
                throw ParseError("unterminated macro argument list", tok.loc)
            }

            if depth == 0 && tok.text == ")" {
                args.append(current)
                return (args, i)
            }

            if depth == 0 && tok.text == "," && (!hasVaArgs || args.count < paramCount) {
                args.append(current)
                current = []
                i += 1
                continue
            }

            if tok.text == "(" { depth += 1 }
            else if tok.text == ")" { depth -= 1 }

            current.append(tok)
            i += 1
        }

        throw ParseError("unterminated macro argument list", tokens[start].loc)
    }

    private func substitute(macro: Macro, args: [[Token]], rawArgs: [[Token]]? = nil, hs: Set<String>, loc: Token) throws -> [Token] {
        let body = macro.body
        var result: [Token] = []
        var i = 0

        while i < body.count {
            let tok = body[i]

            // ## (token pasting) — handle chains: x##y##z → (x##y)##z
            if i + 1 < body.count && body[i + 1].text == "##" {
                let pasteArgs = rawArgs ?? args
                var accumulated = resolveParamText(tok, macro: macro, args: pasteArgs) ?? tok.text
                i += 1 // skip lhs

                while i + 1 < body.count && body[i].text == "##" {
                    i += 1 // skip ##
                    let rhs = body[i]
                    let rhsText = resolveParamText(rhs, macro: macro, args: pasteArgs) ?? rhs.text

                    // GNU extension: `, ## __VA_ARGS__` — delete comma when VA_ARGS is empty
                    if rhsText.isEmpty && accumulated == "," &&
                       (rhs.text == "__VA_ARGS__" || (macro.vaArgsName != nil && rhs.text == macro.vaArgsName!)) {
                        accumulated = ""
                    } else {
                        accumulated += rhsText
                    }
                    i += 1
                }

                if accumulated.isEmpty { continue }

                var lexer = Lexer(source: accumulated, fileName: loc.fileName, fileNo: 1)
                var pToks = try lexer.tokenize()
                if let last = pToks.last, last.kind == .eof { pToks.removeLast() }
                for var pt in pToks {
                    pt.hideset = pt.hideset.union(hs)
                    pt.fileName = loc.fileName
                    pt.lineNo = loc.lineNo
                    result.append(pt)
                }
                continue
            }

            // # (stringification)
            if tok.text == "#" && i + 1 < body.count {
                let next = body[i + 1]
                if let paramIdx = paramIndex(next.text, macro: macro) {
                    let strArgs = rawArgs ?? args
                    let stringified = stringifyTokens(strArgs.indices.contains(paramIdx) ? strArgs[paramIdx] : [])
                    var st = Token(kind: .str, text: stringified, fileName: loc.fileName, lineNo: loc.lineNo)
                    st.hideset = hs
                    // Re-tokenize to get proper strData
                    if let retok = try? tokenizeStringLiteral(st, baseType: SyntaxType(kind: .char(isUnsigned: false), size: 1, align: 1)) {
                        var r = retok
                        r.hideset = hs
                        result.append(r)
                    } else {
                        result.append(st)
                    }
                    i += 2
                    continue
                }
            }

            // Parameter substitution
            if let paramIdx = paramIndex(tok.text, macro: macro) {
                let argTokens = args.indices.contains(paramIdx) ? args[paramIdx] : []
                for (j, var at) in argTokens.enumerated() {
                    // First arg token inherits hasSpace from the body placeholder
                    if j == 0 { at.hasSpace = tok.hasSpace }
                    at.hideset = at.hideset.union(hs)
                    at.fileName = loc.fileName
                    at.lineNo = loc.lineNo
                    result.append(at)
                }
                i += 1
                continue
            }

            // __VA_ARGS__
            if tok.text == "__VA_ARGS__" || (macro.vaArgsName != nil && tok.text == macro.vaArgsName!) {
                let vaIdx = macro.params.count
                let argTokens = args.indices.contains(vaIdx) ? args[vaIdx] : []
                for (j, var at) in argTokens.enumerated() {
                    if j == 0 { at.hasSpace = tok.hasSpace }
                    at.hideset = at.hideset.union(hs)
                    at.fileName = loc.fileName
                    at.lineNo = loc.lineNo
                    result.append(at)
                }
                i += 1
                continue
            }

            // __VA_OPT__
            if tok.text == "__VA_OPT__" && i + 1 < body.count && body[i + 1].text == "(" {
                let vaIdx = macro.params.count
                let vaArgs = args.indices.contains(vaIdx) ? args[vaIdx] : []
                let hasVaArgs = !vaArgs.isEmpty

                // Find matching ')'
                var depth = 0
                var j = i + 1 // the '('
                var optBody: [Token] = []
                j += 1 // skip '('
                while j < body.count {
                    if body[j].text == "(" { depth += 1 }
                    if body[j].text == ")" {
                        if depth == 0 { break }
                        depth -= 1
                    }
                    optBody.append(body[j])
                    j += 1
                }
                i = j + 1 // skip ')'

                if hasVaArgs {
                    for var bt in optBody {
                        bt.hideset = bt.hideset.union(hs)
                        bt.fileName = loc.fileName
                        bt.lineNo = loc.lineNo
                        result.append(bt)
                    }
                }
                continue
            }

            // Normal token
            var t = tok
            t.hideset = t.hideset.union(hs)
            t.fileName = loc.fileName
            t.lineNo = loc.lineNo
            result.append(t)
            i += 1
        }

        return result
    }

    private func paramIndex(_ name: String, macro: Macro) -> Int? {
        macro.params.firstIndex(of: name)
    }

    private func resolveParamText(_ tok: Token, macro: Macro, args: [[Token]]) -> String? {
        // Check named params
        if let idx = paramIndex(tok.text, macro: macro) {
            let argTokens = args.indices.contains(idx) ? args[idx] : []
            return argTokens.map { $0.text }.joined(separator: " ")
        }
        // Check VA_ARGS
        if tok.text == "__VA_ARGS__" || (macro.vaArgsName != nil && tok.text == macro.vaArgsName!) {
            let vaIdx = macro.params.count
            let argTokens = args.indices.contains(vaIdx) ? args[vaIdx] : []
            return argTokens.map { $0.text }.joined(separator: " ")
        }
        return nil
    }

    private func stringifyTokens(_ tokens: [Token]) -> String {
        var parts: [String] = []
        for (i, tok) in tokens.enumerated() {
            if i > 0 && tok.hasSpace { parts.append(" ") }
            if tok.kind == .str {
                // Escape quotes and backslashes within string literals
                var escaped = tok.text
                escaped = escaped.replacingOccurrences(of: "\\", with: "\\\\")
                escaped = escaped.replacingOccurrences(of: "\"", with: "\\\"")
                parts.append(escaped)
            } else {
                parts.append(tok.text)
            }
        }
        return "\"" + parts.joined() + "\""
    }

    // MARK: - Constant expression evaluation for #if

    private func evalConstExpr(_ tokens: [Token]) throws -> Int64 {
        // First macro-expand, then handle 'defined'
        var expanded = try expandForCondition(tokens)
        // Replace remaining identifiers with 0
        for k in expanded.indices {
            if expanded[k].kind == .ident {
                expanded[k] = Token(kind: .ppNum, text: "0", fileName: expanded[k].fileName, lineNo: expanded[k].lineNo)
            }
        }
        convertPPTokens(&expanded)
        // Add EOF
        if expanded.last?.kind != .eof {
            expanded.append(Token(kind: .eof, text: ""))
        }
        var cursor = 0
        let val = try evalTernary(expanded, &cursor)
        return val
    }

    private func expandForCondition(_ tokens: [Token]) throws -> [Token] {
        var result: [Token] = []
        var i = 0
        while i < tokens.count {
            let tok = tokens[i]
            if tok.kind == .eof { break }

            // defined(X) or defined X
            if tok.kind == .ident && tok.text == "defined" {
                i += 1
                var name: String
                if i < tokens.count && tokens[i].text == "(" {
                    i += 1
                    guard i < tokens.count && tokens[i].kind == .ident else {
                        throw ParseError("expected identifier after 'defined('", tok.loc)
                    }
                    name = tokens[i].text
                    i += 1
                    if i < tokens.count && tokens[i].text == ")" { i += 1 }
                } else if i < tokens.count && tokens[i].kind == .ident {
                    name = tokens[i].text
                    i += 1
                } else {
                    name = ""
                }
                let val = macros[name] != nil ? "1" : "0"
                result.append(Token(kind: .ppNum, text: val, fileName: tok.fileName, lineNo: tok.lineNo))
                continue
            }

            // Expand macros
            if tok.kind == .ident, let macro = macros[tok.text], !tok.hideset.contains(tok.text) {
                let (expanded, next) = try expandMacro(tokens, at: i, macro: macro)
                let sub = try expandForCondition(expanded)
                result.append(contentsOf: sub)
                i = next
                continue
            }

            result.append(tok)
            i += 1
        }
        return result
    }

    // Recursive descent evaluator
    private func evalTernary(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        let cond = try evalLogOr(tokens, &i)
        if i < tokens.count && tokens[i].text == "?" {
            i += 1
            let then = try evalTernary(tokens, &i)
            guard i < tokens.count && tokens[i].text == ":" else {
                throw ParseError("expected ':' in ternary", tokens[max(0, i - 1)].loc)
            }
            i += 1
            let els = try evalTernary(tokens, &i)
            return cond != 0 ? then : els
        }
        return cond
    }

    private func evalLogOr(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalLogAnd(tokens, &i)
        while i < tokens.count && tokens[i].text == "||" {
            i += 1
            let rhs = try evalLogAnd(tokens, &i)
            val = (val != 0 || rhs != 0) ? 1 : 0
        }
        return val
    }

    private func evalLogAnd(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalBitOr(tokens, &i)
        while i < tokens.count && tokens[i].text == "&&" {
            i += 1
            let rhs = try evalBitOr(tokens, &i)
            val = (val != 0 && rhs != 0) ? 1 : 0
        }
        return val
    }

    private func evalBitOr(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalBitXor(tokens, &i)
        while i < tokens.count && tokens[i].text == "|" {
            i += 1
            val |= try evalBitXor(tokens, &i)
        }
        return val
    }

    private func evalBitXor(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalBitAnd(tokens, &i)
        while i < tokens.count && tokens[i].text == "^" {
            i += 1
            val ^= try evalBitAnd(tokens, &i)
        }
        return val
    }

    private func evalBitAnd(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalEquality(tokens, &i)
        while i < tokens.count && tokens[i].text == "&" {
            i += 1
            val &= try evalEquality(tokens, &i)
        }
        return val
    }

    private func evalEquality(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalRelational(tokens, &i)
        while i < tokens.count {
            if tokens[i].text == "==" {
                i += 1; val = try evalRelational(tokens, &i) == val ? 1 : 0
            } else if tokens[i].text == "!=" {
                i += 1; val = try evalRelational(tokens, &i) != val ? 1 : 0
            } else { break }
        }
        return val
    }

    private func evalRelational(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalShift(tokens, &i)
        while i < tokens.count {
            if tokens[i].text == "<" { i += 1; let r = try evalShift(tokens, &i); val = val < r ? 1 : 0 }
            else if tokens[i].text == "<=" { i += 1; let r = try evalShift(tokens, &i); val = val <= r ? 1 : 0 }
            else if tokens[i].text == ">" { i += 1; let r = try evalShift(tokens, &i); val = val > r ? 1 : 0 }
            else if tokens[i].text == ">=" { i += 1; let r = try evalShift(tokens, &i); val = val >= r ? 1 : 0 }
            else { break }
        }
        return val
    }

    private func evalShift(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalAdd(tokens, &i)
        while i < tokens.count {
            if tokens[i].text == "<<" { i += 1; val <<= try evalAdd(tokens, &i) }
            else if tokens[i].text == ">>" { i += 1; val >>= try evalAdd(tokens, &i) }
            else { break }
        }
        return val
    }

    private func evalAdd(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalMul(tokens, &i)
        while i < tokens.count {
            if tokens[i].text == "+" { i += 1; let r = try evalMul(tokens, &i); val = val &+ r }
            else if tokens[i].text == "-" { i += 1; let r = try evalMul(tokens, &i); val = val &- r }
            else { break }
        }
        return val
    }

    private func evalMul(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        var val = try evalUnary(tokens, &i)
        while i < tokens.count {
            if tokens[i].text == "*" { i += 1; let r = try evalUnary(tokens, &i); val = val &* r }
            else if tokens[i].text == "/" {
                i += 1; let r = try evalUnary(tokens, &i)
                val = r != 0 ? val / r : 0
            }
            else if tokens[i].text == "%" {
                i += 1; let r = try evalUnary(tokens, &i)
                val = r != 0 ? val % r : 0
            }
            else { break }
        }
        return val
    }

    private func evalUnary(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        if i < tokens.count {
            if tokens[i].text == "+" { i += 1; return try evalUnary(tokens, &i) }
            if tokens[i].text == "-" { i += 1; return -(try evalUnary(tokens, &i)) }
            if tokens[i].text == "!" { i += 1; return try evalUnary(tokens, &i) == 0 ? 1 : 0 }
            if tokens[i].text == "~" { i += 1; return ~(try evalUnary(tokens, &i)) }
        }
        return try evalPrimary(tokens, &i)
    }

    private func evalPrimary(_ tokens: [Token], _ i: inout Int) throws -> Int64 {
        guard i < tokens.count else {
            throw ParseError("expected expression in #if", SourceLocation(fileName: "", line: 0, column: 0))
        }
        let tok = tokens[i]

        if tok.text == "(" {
            i += 1
            let val = try evalTernary(tokens, &i)
            if i < tokens.count && tokens[i].text == ")" { i += 1 }
            return val
        }

        if tok.kind == .num {
            i += 1
            return tok.val
        }

        if tok.kind == .ident && tok.text == "true" { i += 1; return 1 }
        if tok.kind == .ident && tok.text == "false" { i += 1; return 0 }

        // Character constant
        if tok.kind == .num && tok.ty != nil {
            i += 1
            return tok.val
        }

        i += 1
        return 0
    }

    // MARK: - String literal concatenation

    private func concatenateStringLiterals(_ tokens: [Token]) -> [Token] {
        var result: [Token] = []
        var i = 0
        while i < tokens.count {
            if tokens[i].kind == .str {
                // Collect run of adjacent string literals
                var run: [Token] = [tokens[i]]
                var j = i + 1
                while j < tokens.count && tokens[j].kind == .str {
                    run.append(tokens[j])
                    j += 1
                }

                // First pass: determine the widest element type in the run
                var maxElem = 1
                var wideType: SyntaxType.Kind = .char(isUnsigned: false)
                for t in run {
                    let es = elementSize(t.ty)
                    if es > maxElem {
                        maxElem = es
                        if let elem = elementType(t.ty) { wideType = elem.kind }
                    }
                }

                // Second pass: re-tokenize narrow strings as wide if needed
                if maxElem > 1 {
                    for k in 0..<run.count {
                        if elementSize(run[k].ty) == 1 {
                            // Re-tokenize this narrow string as a wide string
                            run[k] = retokenizeAsWide(run[k], elemSize: maxElem, elemKind: wideType)
                        }
                    }
                }

                // Third pass: concatenate all (now same-width) strings
                var combined = run[0]
                for k in 1..<run.count {
                    combined = concatStrings(combined, run[k])
                }
                result.append(combined)
                i = j
            } else {
                result.append(tokens[i])
                i += 1
            }
        }
        return result
    }

    /// Re-tokenize a narrow string literal's source text as a wide string.
    /// This correctly handles both `"あ"` (UTF-8 → codepoint) and `"\343"` (octal → byte value).
    private func retokenizeAsWide(_ tok: Token, elemSize: Int, elemKind: SyntaxType.Kind) -> Token {
        // Get the quoted content from source text (strip surrounding quotes and any prefix)
        var src = tok.text
        // Remove prefix (u8, u, etc.) if present — narrow strings shouldn't have wide prefixes
        if src.hasPrefix("u8") { src = String(src.dropFirst(2)) }
        // Now src should be `"..."` — we need to lex it as a wide string
        // Prepend L to re-lex as L"..."
        let prefix: String
        if elemSize == 4 { prefix = "L" }
        else if elemSize == 2 { prefix = "u" }
        else { return tok }

        let wideSrc = prefix + src
        // Use the lexer to tokenize this single string literal
        var lexer = Lexer(source: wideSrc, fileName: tok.fileName)
        guard let tokens = try? lexer.tokenize(),
              let strTok = tokens.first(where: { $0.kind == .str }) else {
            return tok
        }
        var result = tok
        result.strData = strTok.strData
        result.ty = strTok.ty
        return result
    }

    private func concatStrings(_ a: Token, _ b: Token) -> Token {
        guard var aData = a.strData, let bData = b.strData else { return a }

        let aElemSize = elementSize(a.ty)
        let bElemSize = elementSize(b.ty)
        let maxElem = max(aElemSize, bElemSize)

        if aElemSize == maxElem && bElemSize == maxElem {
            // Same size: strip null terminator from a, append b
            let nullBytes = aElemSize
            if aData.count >= nullBytes {
                aData.removeLast(nullBytes)
            }
            var result = a
            result.strData = aData + bData
            let totalElems = result.strData!.count / maxElem
            let elemType = elementType(a.ty) ?? SyntaxType(kind: .char(isUnsigned: false), size: 1, align: 1)
            result.ty = SyntaxType(kind: .array(element: elemType, length: totalElems),
                                   size: totalElems * maxElem, align: maxElem)
            return result
        }

        // Different sizes: promote smaller to larger (byte-by-byte)
        let aElems = aData.count / aElemSize
        let bElems = bData.count / bElemSize
        var promoted: [UInt8] = []

        // Convert a (without null terminator)
        for idx in 0..<(aElems - 1) {
            let val = readElement(aData, at: idx, size: aElemSize)
            writeElement(&promoted, val: val, size: maxElem)
        }
        // Append all of b (including null)
        for idx in 0..<bElems {
            let val = readElement(bData, at: idx, size: bElemSize)
            writeElement(&promoted, val: val, size: maxElem)
        }

        var result = a
        result.strData = promoted
        let totalElems = promoted.count / maxElem
        let elemKind: SyntaxType.Kind = maxElem == 4 ? .int(isUnsigned: true) : (maxElem == 2 ? .short(isUnsigned: true) : .char(isUnsigned: false))
        let elemType = SyntaxType(kind: elemKind, size: maxElem, align: maxElem)
        result.ty = SyntaxType(kind: .array(element: elemType, length: totalElems),
                                size: totalElems * maxElem, align: maxElem)
        return result
    }

    private func elementSize(_ ty: SyntaxType?) -> Int {
        guard let ty = ty, case .array(let elem, _) = ty.kind else { return 1 }
        return elem.size
    }

    private func elementType(_ ty: SyntaxType?) -> SyntaxType? {
        guard let ty = ty, case .array(let elem, _) = ty.kind else { return nil }
        return elem
    }

    private func readElement(_ data: [UInt8], at index: Int, size: Int) -> UInt32 {
        let offset = index * size
        var val: UInt32 = 0
        for b in 0..<size {
            if offset + b < data.count {
                val |= UInt32(data[offset + b]) << (b * 8)
            }
        }
        return val
    }

    private func writeElement(_ data: inout [UInt8], val: UInt32, size: Int) {
        for b in 0..<size {
            data.append(UInt8((val >> (b * 8)) & 0xFF))
        }
    }

    // MARK: - Line utilities

    private func collectLine(_ tokens: [Token], from start: Int) -> ([Token], Int) {
        var line: [Token] = []
        var i = start
        while i < tokens.count {
            if tokens[i].kind == .eof || tokens[i].atBOL { break }
            line.append(tokens[i])
            i += 1
        }
        return (line, i)
    }

    private func skipLine(_ tokens: [Token], from start: Int) -> Int {
        var i = start
        while i < tokens.count {
            if tokens[i].kind == .eof || tokens[i].atBOL { break }
            i += 1
        }
        return i
    }

    private func collectLineText(_ tokens: [Token], from start: Int) -> String {
        let (line, _) = collectLine(tokens, from: start)
        return line.map { $0.text }.joined(separator: " ")
    }

    // MARK: - Built-in macros

    /// Create a string token with proper strData and type.
    private static func makeStrToken(_ quotedText: String, tok: Token) -> Token {
        // quotedText is like `"Mar 14 2026"`
        var inner = quotedText
        if inner.hasPrefix("\"") && inner.hasSuffix("\"") {
            inner = String(inner.dropFirst().dropLast())
        }
        let bytes = Array(inner.utf8) + [0]
        let elemType = SyntaxType(kind: .char(isUnsigned: false), size: 1, align: 1)
        var t = Token(kind: .str, text: quotedText, fileName: tok.fileName, lineNo: tok.lineNo)
        t.strData = bytes
        t.ty = SyntaxType(kind: .array(element: elemType, length: bytes.count),
                           size: bytes.count, align: 1)
        return t
    }

    private func initMacros() {
        // Built-in dynamic macros
        addBuiltin("__FILE__") { tok, _ in
            var t = Token(kind: .str, text: "\"\(tok.fileName)\"", fileName: tok.fileName, lineNo: tok.lineNo)
            t.strData = Array(tok.fileName.utf8) + [0]
            let elemType = SyntaxType(kind: .char(isUnsigned: false), size: 1, align: 1)
            t.ty = SyntaxType(kind: .array(element: elemType, length: t.strData!.count),
                              size: t.strData!.count, align: 1)
            return [t]
        }

        addBuiltin("__LINE__") { tok, _ in
            let t = Token(kind: .ppNum, text: "\(tok.lineNo)", fileName: tok.fileName, lineNo: tok.lineNo)
            return [t]
        }

        addBuiltin("__COUNTER__") { tok, pp in
            let val = pp.counterValue
            pp.counterValue += 1
            return [Token(kind: .ppNum, text: "\(val)", fileName: tok.fileName, lineNo: tok.lineNo)]
        }

        addBuiltin("__DATE__") { [dateStr] tok, _ in
            return [Self.makeStrToken(dateStr, tok: tok)]
        }

        addBuiltin("__TIME__") { [timeStr] tok, _ in
            return [Self.makeStrToken(timeStr, tok: tok)]
        }

        addBuiltin("__TIMESTAMP__") { [timestampStr] tok, _ in
            return [Self.makeStrToken(timestampStr, tok: tok)]
        }

        addBuiltin("__BASE_FILE__") { tok, pp in
            let name = pp.baseFile.isEmpty ? tok.fileName : pp.baseFile
            var t = Token(kind: .str, text: "\"\(name)\"", fileName: tok.fileName, lineNo: tok.lineNo)
            t.strData = Array(name.utf8) + [0]
            let elemType = SyntaxType(kind: .char(isUnsigned: false), size: 1, align: 1)
            t.ty = SyntaxType(kind: .array(element: elemType, length: t.strData!.count),
                              size: t.strData!.count, align: 1)
            return [t]
        }

        // Predefined object-like macros
        defineObjMacro("__STDC__", "1")
        defineObjMacro("__STDC_VERSION__", "201112L")
        defineObjMacro("__STDC_HOSTED__", "1")
        defineObjMacro("__STDC_NO_ATOMICS__", "1")
        defineObjMacro("__STDC_NO_COMPLEX__", "1")
        defineObjMacro("__STDC_NO_THREADS__", "1")
        defineObjMacro("__STDC_NO_VLA__", "1")
        defineObjMacro("__STDC_UTF_16__", "1")
        defineObjMacro("__STDC_UTF_32__", "1")

        // Platform macros (x86-64 Linux)
        defineObjMacro("__SIZEOF_FLOAT__", "4")
        defineObjMacro("__SIZEOF_DOUBLE__", "8")
        defineObjMacro("__SIZEOF_LONG_DOUBLE__", "16")
        defineObjMacro("__SIZEOF_SHORT__", "2")
        defineObjMacro("__SIZEOF_INT__", "4")
        defineObjMacro("__SIZEOF_LONG__", "8")
        defineObjMacro("__SIZEOF_LONG_LONG__", "8")
        defineObjMacro("__SIZEOF_POINTER__", "8")
        defineObjMacro("__SIZEOF_PTRDIFF_T__", "8")
        defineObjMacro("__SIZEOF_SIZE_T__", "8")

        defineObjMacro("__SIZE_TYPE__", "unsigned long")
        defineObjMacro("__PTRDIFF_TYPE__", "long")
        defineObjMacro("__WCHAR_TYPE__", "int")
        defineObjMacro("__WINT_TYPE__", "unsigned int")
        defineObjMacro("__INT8_TYPE__", "signed char")
        defineObjMacro("__INT16_TYPE__", "short")
        defineObjMacro("__INT32_TYPE__", "int")
        defineObjMacro("__INT64_TYPE__", "long")
        defineObjMacro("__UINT8_TYPE__", "unsigned char")
        defineObjMacro("__UINT16_TYPE__", "unsigned short")
        defineObjMacro("__UINT32_TYPE__", "unsigned int")
        defineObjMacro("__UINT64_TYPE__", "unsigned long")
        defineObjMacro("__INT_MAX__", "2147483647")
        defineObjMacro("__LONG_MAX__", "9223372036854775807L")
        defineObjMacro("__LONG_LONG_MAX__", "9223372036854775807LL")
        defineObjMacro("__SCHAR_MAX__", "127")
        defineObjMacro("__SHRT_MAX__", "32767")

        defineObjMacro("__LP64__", "1")
        defineObjMacro("_LP64", "1")

        defineObjMacro("__ELF__", "1")
        defineObjMacro("__x86_64__", "1")
        defineObjMacro("__x86_64", "1")
        defineObjMacro("__amd64__", "1")
        defineObjMacro("__amd64", "1")
        defineObjMacro("__linux__", "1")
        defineObjMacro("__linux", "1")
        defineObjMacro("linux", "1")
        defineObjMacro("__unix__", "1")
        defineObjMacro("__unix", "1")
        defineObjMacro("unix", "1")
        defineObjMacro("__gnu_linux__", "1")

        defineObjMacro("__BYTE_ORDER__", "1234")
        defineObjMacro("__ORDER_LITTLE_ENDIAN__", "1234")
        defineObjMacro("__ORDER_BIG_ENDIAN__", "4321")

        defineObjMacro("__CHAR_BIT__", "8")
        defineObjMacro("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_1", "1")
        defineObjMacro("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_2", "1")
        defineObjMacro("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_4", "1")
        defineObjMacro("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_8", "1")

        defineObjMacro("__GNUC__", "14")
        defineObjMacro("__GNUC_MINOR__", "0")
        defineObjMacro("__GNUC_PATCHLEVEL__", "0")

        defineObjMacro("__alignof__", "_Alignof")
        defineObjMacro("__const__", "const")
        defineObjMacro("__volatile__", "volatile")
        defineObjMacro("__signed__", "signed")
        defineObjMacro("__inline__", "inline")
        defineObjMacro("__typeof__", "typeof")

        defineObjMacro("__FLT_MIN__", "1.17549435e-38f")
        defineObjMacro("__FLT_MAX__", "3.40282347e+38f")
        defineObjMacro("__FLT_EPSILON__", "1.19209290e-7f")
        defineObjMacro("__DBL_MIN__", "2.2250738585072014e-308")
        defineObjMacro("__DBL_MAX__", "1.7976931348623157e+308")
        defineObjMacro("__DBL_EPSILON__", "2.2204460492503131e-16")
        defineObjMacro("__LDBL_MIN__", "3.36210314311209350626e-4932L")
        defineObjMacro("__LDBL_MAX__", "1.18973149535723176502e+4932L")
        defineObjMacro("__LDBL_EPSILON__", "1.08420217248550443401e-19L")
    }

    private func addBuiltin(_ name: String, _ handler: @escaping (Token, Preprocessor) throws -> [Token]) {
        macros[name] = Macro(name: name, isObjlike: true, params: [], vaArgsName: nil, body: [], handler: handler)
    }

    private func defineObjMacro(_ name: String, _ value: String) {
        var lexer = Lexer(source: value + "\n", fileName: "<built-in>", fileNo: 0)
        let tokens = (try? lexer.tokenize()) ?? []
        let body = tokens.filter { $0.kind != .eof }
        macros[name] = Macro(name: name, isObjlike: true, params: [], vaArgsName: nil, body: body)
    }
}
