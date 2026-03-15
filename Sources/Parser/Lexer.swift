// C lexer / tokenizer.
// Ported from chibicc's tokenize.c.

import Foundation
import Syntax

// MARK: - Keywords

private let keywords: Set<String> = [
    "return", "if", "else", "for", "while", "int", "sizeof", "char",
    "struct", "union", "short", "long", "void", "typedef", "_Bool",
    "enum", "static", "goto", "break", "continue", "switch", "case",
    "default", "extern", "_Alignof", "_Alignas", "do", "signed",
    "unsigned", "const", "volatile", "auto", "register", "restrict",
    "__restrict", "__restrict__", "_Noreturn", "float", "double",
    "typeof", "asm", "_Thread_local", "__thread", "_Atomic",
    "__attribute__",
]

// MARK: - Multi-char punctuators

private let multiCharPuncts = [
    "<<=", ">>=", "...", "==", "!=", "<=", ">=", "->", "+=",
    "-=", "*=", "/=", "++", "--", "%=", "&=", "|=", "^=", "&&",
    "||", "<<", ">>", "##",
]

// MARK: - Lexer

public struct Lexer {
    private var buf: [UInt8]
    private var pos: Int
    private var fileName: String
    private var displayName: String
    private var fileNo: Int
    private var lineDelta: Int = 0
    private var atBOL: Bool = true
    private var hasSpace: Bool = false
    private var lineNo: Int = 1

    public init(source: String, fileName: String, fileNo: Int = 1) {
        // Pre-process: canonicalize newlines, remove backslash-newline
        var s = source
        s = Lexer.canonicalizeNewlines(s)
        s = Lexer.removeBackslashNewline(s)
        s = Lexer.convertUniversalChars(s)
        // Ensure ends with newline
        if !s.hasSuffix("\n") { s += "\n" }
        self.buf = Array(s.utf8) + [0] // null-terminate
        self.pos = 0
        self.fileName = fileName
        self.displayName = fileName
        self.fileNo = fileNo
        // Skip UTF-8 BOM
        if buf.count >= 3 && buf[0] == 0xEF && buf[1] == 0xBB && buf[2] == 0xBF {
            pos = 3
        }
    }

    // MARK: - Source pre-processing

    static func canonicalizeNewlines(_ s: String) -> String {
        s.replacingOccurrences(of: "\r\n", with: "\n")
         .replacingOccurrences(of: "\r", with: "\n")
    }

    static func removeBackslashNewline(_ s: String) -> String {
        var result: [Character] = []
        var pending = 0
        var chars = Array(s)
        var i = 0
        while i < chars.count {
            if i + 1 < chars.count && chars[i] == "\\" && chars[i+1] == "\n" {
                i += 2
                pending += 1
            } else if chars[i] == "\n" {
                result.append(chars[i])
                i += 1
                for _ in 0..<pending { result.append("\n") }
                pending = 0
            } else {
                result.append(chars[i])
                i += 1
            }
        }
        for _ in 0..<pending { result.append("\n") }
        return String(result)
    }

    static func convertUniversalChars(_ s: String) -> String {
        var result: [UInt8] = []
        let bytes = Array(s.utf8)
        var i = 0
        while i < bytes.count {
            if i + 1 < bytes.count && bytes[i] == UInt8(ascii: "\\") {
                if bytes[i+1] == UInt8(ascii: "u") && i + 5 < bytes.count {
                    if let c = readUniversalChar(bytes, at: i + 2, len: 4) {
                        result.append(contentsOf: encodeUTF8(c))
                        i += 6
                        continue
                    }
                } else if bytes[i+1] == UInt8(ascii: "U") && i + 9 < bytes.count {
                    if let c = readUniversalChar(bytes, at: i + 2, len: 8) {
                        result.append(contentsOf: encodeUTF8(c))
                        i += 10
                        continue
                    }
                }
                // Not a valid universal char, copy both bytes
                result.append(bytes[i])
                i += 1
                if i < bytes.count {
                    result.append(bytes[i])
                    i += 1
                }
            } else {
                result.append(bytes[i])
                i += 1
            }
        }
        return String(decoding: result, as: UTF8.self)
    }

    private static func readUniversalChar(_ bytes: [UInt8], at start: Int, len: Int) -> UInt32? {
        var c: UInt32 = 0
        for j in 0..<len {
            guard start + j < bytes.count else { return nil }
            let b = bytes[start + j]
            guard let h = fromHex(b) else { return nil }
            c = (c << 4) | UInt32(h)
        }
        return c
    }

    // MARK: - Tokenize

    public mutating func tokenize() throws -> [Token] {
        var tokens: [Token] = []

        while pos < buf.count && buf[pos] != 0 {
            // Skip line comments
            if pos + 1 < buf.count && buf[pos] == UInt8(ascii: "/") && buf[pos+1] == UInt8(ascii: "/") {
                pos += 2
                while pos < buf.count && buf[pos] != 0 && buf[pos] != UInt8(ascii: "\n") { pos += 1 }
                hasSpace = true
                continue
            }
            // Skip block comments
            if pos + 1 < buf.count && buf[pos] == UInt8(ascii: "/") && buf[pos+1] == UInt8(ascii: "*") {
                let start = pos
                pos += 2
                while pos + 1 < buf.count && buf[pos] != 0 {
                    if buf[pos] == UInt8(ascii: "*") && buf[pos+1] == UInt8(ascii: "/") {
                        pos += 2
                        break
                    }
                    if buf[pos] == UInt8(ascii: "\n") { lineNo += 1 }
                    pos += 1
                }
                if pos >= buf.count || buf[pos-1] != UInt8(ascii: "/") || buf[pos-2] != UInt8(ascii: "*") {
                    throw ParseError("unclosed block comment",
                                     SourceLocation(fileName: fileName, line: lineNo, column: 0))
                }
                hasSpace = true
                continue
            }
            // Newline
            if buf[pos] == UInt8(ascii: "\n") {
                pos += 1
                lineNo += 1
                atBOL = true
                hasSpace = false
                continue
            }
            // Whitespace
            if isSpace(buf[pos]) {
                pos += 1
                hasSpace = true
                continue
            }

            // Numeric literal (pp-number)
            if isDigit(buf[pos]) || (buf[pos] == UInt8(ascii: ".") && pos + 1 < buf.count && isDigit(buf[pos+1])) {
                let start = pos
                pos += 1
                while pos < buf.count && buf[pos] != 0 {
                    if pos + 1 < buf.count && isExpChar(buf[pos]) && (buf[pos+1] == UInt8(ascii: "+") || buf[pos+1] == UInt8(ascii: "-")) {
                        pos += 2
                    } else if isAlnum(buf[pos]) || buf[pos] == UInt8(ascii: ".") {
                        pos += 1
                    } else {
                        break
                    }
                }
                tokens.append(makeToken(.ppNum, start: start, end: pos))
                continue
            }

            // String literal
            if buf[pos] == UInt8(ascii: "\"") {
                tokens.append(try readStringLiteral(start: pos, quotePos: pos))
                continue
            }
            // u8"..."
            if startsWith("u8\"") {
                tokens.append(try readStringLiteral(start: pos, quotePos: pos + 2))
                continue
            }
            // u"..."
            if startsWith("u\"") {
                tokens.append(try readUTF16StringLiteral(start: pos, quotePos: pos + 1))
                continue
            }
            // L"..."
            if startsWith("L\"") {
                tokens.append(try readUTF32StringLiteral(start: pos, quotePos: pos + 1, elemType: .int(isUnsigned: false), elemSize: 4))
                continue
            }
            // U"..."
            if startsWith("U\"") {
                tokens.append(try readUTF32StringLiteral(start: pos, quotePos: pos + 1, elemType: .int(isUnsigned: true), elemSize: 4))
                continue
            }

            // Character literal
            if buf[pos] == UInt8(ascii: "'") {
                tokens.append(try readCharLiteral(start: pos, quotePos: pos, charType: SyntaxType(kind: .int(isUnsigned: false), size: 4, align: 4)))
                continue
            }
            // u'...'
            if startsWith("u'") {
                var tok = try readCharLiteral(start: pos, quotePos: pos + 1, charType: SyntaxType(kind: .short(isUnsigned: true), size: 2, align: 2))
                tok.val &= 0xFFFF
                tokens.append(tok)
                continue
            }
            // L'...'
            if startsWith("L'") {
                tokens.append(try readCharLiteral(start: pos, quotePos: pos + 1, charType: SyntaxType(kind: .int(isUnsigned: false), size: 4, align: 4)))
                continue
            }
            // U'...'
            if startsWith("U'") {
                var tok = try readCharLiteral(start: pos, quotePos: pos + 1, charType: SyntaxType(kind: .int(isUnsigned: true), size: 4, align: 4))
                tokens.append(tok)
                continue
            }

            // Identifier
            let identLen = readIdent()
            if identLen > 0 {
                let text = stringSlice(pos, pos + identLen)
                let tok = makeToken(.ident, start: pos, end: pos + identLen)
                tokens.append(tok)
                pos += identLen
                continue
            }

            // Punctuators
            let punctLen = readPunct()
            if punctLen > 0 {
                tokens.append(makeToken(.punct, start: pos, end: pos + punctLen))
                pos += punctLen
                continue
            }

            // Unknown character — emit as a single-character punctuator
            // (needed for preprocessor stringification of arbitrary tokens)
            tokens.append(makeToken(.punct, start: pos, end: pos + 1))
            pos += 1
        }

        // EOF token
        tokens.append(Token(kind: .eof, text: "", fileName: fileName, lineNo: lineNo, displayName: displayName, atBOL: atBOL, hasSpace: hasSpace))
        return tokens
    }

    // MARK: - Token construction

    private mutating func makeToken(_ kind: TokenKind, start: Int, end: Int) -> Token {
        let text = stringSlice(start, end)
        var tok = Token(kind: kind, text: text, fileName: fileName, lineNo: lineNo, displayName: displayName, atBOL: atBOL, hasSpace: hasSpace)
        atBOL = false
        hasSpace = false
        return tok
    }

    // MARK: - String/Char literals

    private mutating func readStringLiteral(start: Int, quotePos: Int) throws -> Token {
        let endQuote = try findStringEnd(quotePos + 1)
        var decoded: [UInt8] = []
        var p = quotePos + 1
        while p < endQuote {
            if buf[p] == UInt8(ascii: "\\") {
                let (c, next) = readEscapedChar(p + 1)
                decoded.append(UInt8(truncatingIfNeeded: c))
                p = next
            } else {
                decoded.append(buf[p])
                p += 1
            }
        }
        decoded.append(0) // null terminator

        var tok = makeToken(.str, start: start, end: endQuote + 1)
        tok.strData = decoded
        tok.ty = SyntaxType(kind: .array(element: SyntaxType(kind: .char(isUnsigned: false), size: 1, align: 1), length: decoded.count),
                            size: decoded.count, align: 1)
        pos = endQuote + 1
        return tok
    }

    private mutating func readUTF16StringLiteral(start: Int, quotePos: Int) throws -> Token {
        let endQuote = try findStringEnd(quotePos + 1)
        var codeUnits: [UInt16] = []
        var p = quotePos + 1
        while p < endQuote {
            if buf[p] == UInt8(ascii: "\\") {
                let (c, next) = readEscapedChar(p + 1)
                codeUnits.append(UInt16(truncatingIfNeeded: c))
                p = next
            } else {
                let (cp, len) = buf.withUnsafeBufferPointer { decodeUTF8($0, at: p) }
                if cp < 0x10000 {
                    codeUnits.append(UInt16(cp))
                } else {
                    let c = cp - 0x10000
                    codeUnits.append(0xD800 + UInt16((c >> 10) & 0x3FF))
                    codeUnits.append(0xDC00 + UInt16(c & 0x3FF))
                }
                p += len
            }
        }
        codeUnits.append(0) // null terminator

        // Store as raw bytes
        var rawBytes: [UInt8] = []
        for u in codeUnits {
            rawBytes.append(UInt8(u & 0xFF))
            rawBytes.append(UInt8(u >> 8))
        }

        let elemType = SyntaxType(kind: .short(isUnsigned: true), size: 2, align: 2)
        var tok = makeToken(.str, start: start, end: endQuote + 1)
        tok.strData = rawBytes
        tok.ty = SyntaxType(kind: .array(element: elemType, length: codeUnits.count),
                            size: codeUnits.count * 2, align: 2)
        pos = endQuote + 1
        return tok
    }

    private mutating func readUTF32StringLiteral(start: Int, quotePos: Int, elemType: SyntaxType.Kind, elemSize: Int) throws -> Token {
        let endQuote = try findStringEnd(quotePos + 1)
        var codePoints: [UInt32] = []
        var p = quotePos + 1
        while p < endQuote {
            if buf[p] == UInt8(ascii: "\\") {
                let (c, next) = readEscapedChar(p + 1)
                codePoints.append(UInt32(truncatingIfNeeded: c))
                p = next
            } else {
                let (cp, len) = buf.withUnsafeBufferPointer { decodeUTF8($0, at: p) }
                codePoints.append(cp)
                p += len
            }
        }
        codePoints.append(0) // null

        var rawBytes: [UInt8] = []
        for u in codePoints {
            rawBytes.append(UInt8(u & 0xFF))
            rawBytes.append(UInt8((u >> 8) & 0xFF))
            rawBytes.append(UInt8((u >> 16) & 0xFF))
            rawBytes.append(UInt8((u >> 24) & 0xFF))
        }

        let eType = SyntaxType(kind: elemType, size: elemSize, align: elemSize)
        var tok = makeToken(.str, start: start, end: endQuote + 1)
        tok.strData = rawBytes
        tok.ty = SyntaxType(kind: .array(element: eType, length: codePoints.count),
                            size: codePoints.count * elemSize, align: elemSize)
        pos = endQuote + 1
        return tok
    }

    private mutating func readCharLiteral(start: Int, quotePos: Int, charType: SyntaxType) throws -> Token {
        var p = quotePos + 1
        guard p < buf.count && buf[p] != 0 else {
            throw ParseError("unclosed char literal",
                             SourceLocation(fileName: fileName, line: lineNo, column: 0))
        }
        let c: Int
        if buf[p] == UInt8(ascii: "\\") {
            let (val, next) = readEscapedChar(p + 1)
            c = val
            p = next
        } else {
            let (cp, len) = buf.withUnsafeBufferPointer { decodeUTF8($0, at: p) }
            c = Int(cp)
            p += len
        }

        guard p < buf.count && buf[p] == UInt8(ascii: "'") else {
            throw ParseError("unclosed char literal",
                             SourceLocation(fileName: fileName, line: lineNo, column: 0))
        }

        var tok = makeToken(.num, start: start, end: p + 1)
        tok.ty = charType
        pos = p + 1

        // Plain char literals ('x') sign-extend through Int8 (C char is signed).
        // Wide/Unicode char literals (L'x', U'x', u'x') keep the full codepoint.
        if quotePos == start {
            // Plain char literal
            tok.val = Int64(Int8(truncatingIfNeeded: c))
        } else {
            tok.val = Int64(c)
        }

        return tok
    }

    private func findStringEnd(_ start: Int) throws -> Int {
        var p = start
        while p < buf.count && buf[p] != 0 {
            if buf[p] == UInt8(ascii: "\"") {
                return p
            }
            if buf[p] == UInt8(ascii: "\n") || buf[p] == 0 {
                throw ParseError("unclosed string literal",
                                 SourceLocation(fileName: fileName, line: lineNo, column: 0))
            }
            if buf[p] == UInt8(ascii: "\\") {
                p += 1
            }
            p += 1
        }
        throw ParseError("unclosed string literal",
                         SourceLocation(fileName: fileName, line: lineNo, column: 0))
    }

    private func readEscapedChar(_ p: Int) -> (Int, Int) {
        var p = p
        // Octal
        if p < buf.count && buf[p] >= UInt8(ascii: "0") && buf[p] <= UInt8(ascii: "7") {
            var c = Int(buf[p]) - 0x30
            p += 1
            if p < buf.count && buf[p] >= UInt8(ascii: "0") && buf[p] <= UInt8(ascii: "7") {
                c = (c << 3) + Int(buf[p]) - 0x30
                p += 1
                if p < buf.count && buf[p] >= UInt8(ascii: "0") && buf[p] <= UInt8(ascii: "7") {
                    c = (c << 3) + Int(buf[p]) - 0x30
                    p += 1
                }
            }
            return (c, p)
        }
        // Hex
        if p < buf.count && buf[p] == UInt8(ascii: "x") {
            p += 1
            var c = 0
            while p < buf.count, let h = fromHex(buf[p]) {
                c = (c << 4) + h
                p += 1
            }
            return (c, p)
        }
        // Named escapes
        guard p < buf.count else { return (0, p) }
        let ch = buf[p]
        p += 1
        switch ch {
        case UInt8(ascii: "a"): return (7, p)
        case UInt8(ascii: "b"): return (8, p)
        case UInt8(ascii: "t"): return (9, p)
        case UInt8(ascii: "n"): return (10, p)
        case UInt8(ascii: "v"): return (11, p)
        case UInt8(ascii: "f"): return (12, p)
        case UInt8(ascii: "r"): return (13, p)
        case UInt8(ascii: "e"): return (27, p)  // GNU extension
        default: return (Int(ch), p)
        }
    }

    // MARK: - Identifier

    private func readIdent() -> Int {
        var p = pos
        guard p < buf.count else { return 0 }
        let (c, len) = buf.withUnsafeBufferPointer { decodeUTF8($0, at: p) }
        guard isIdent1(c) else { return 0 }
        p += len
        while p < buf.count {
            let (c2, len2) = buf.withUnsafeBufferPointer { decodeUTF8($0, at: p) }
            guard isIdent2(c2) else { break }
            p += len2
        }
        return p - pos
    }

    // MARK: - Punctuators

    private func readPunct() -> Int {
        for kw in multiCharPuncts {
            if startsWith(kw) { return kw.count }
        }
        if pos < buf.count && isPunct(buf[pos]) { return 1 }
        return 0
    }

    // MARK: - Utility

    private func startsWith(_ s: String) -> Bool {
        let bytes = Array(s.utf8)
        guard pos + bytes.count <= buf.count else { return false }
        for (i, b) in bytes.enumerated() {
            if buf[pos + i] != b { return false }
        }
        return true
    }

    private func stringSlice(_ start: Int, _ end: Int) -> String {
        String(decoding: buf[start..<end], as: UTF8.self)
    }
}

// MARK: - pp-number to number conversion

/// Convert pp-number tokens to num tokens, and identify keywords.
public func convertPPTokens(_ tokens: inout [Token]) {
    for i in tokens.indices {
        if tokens[i].kind == .ident && keywords.contains(tokens[i].text) {
            tokens[i].kind = .keyword
        } else if tokens[i].kind == .ppNum {
            convertPPNumber(&tokens[i])
        }
    }
}

private func convertPPNumber(_ tok: inout Token) {
    if convertPPInt(&tok) { return }
    // Try float
    let text = tok.text
    var remaining = text[...]
    // Try to parse as double
    if let val = Double(text.filter { $0 != "'" }) {
        // just use full text
    }

    // Determine suffix
    var s = text
    var floatType: SyntaxType
    if s.hasSuffix("f") || s.hasSuffix("F") {
        s = String(s.dropLast())
        floatType = SyntaxType(kind: .float, size: 4, align: 4)
    } else if s.hasSuffix("l") || s.hasSuffix("L") {
        s = String(s.dropLast())
        floatType = SyntaxType(kind: .longDouble, size: 16, align: 16)
    } else {
        floatType = SyntaxType(kind: .double, size: 8, align: 8)
    }

    if let val = Double(s) {
        tok.kind = .num
        tok.fval = val
        tok.ty = floatType
    }
}

private func convertPPInt(_ tok: inout Token) -> Bool {
    var s = tok.text
    var base = 10

    if s.lowercased().hasPrefix("0x") && s.count > 2 {
        s = String(s.dropFirst(2))
        base = 16
    } else if s.lowercased().hasPrefix("0b") && s.count > 2 {
        s = String(s.dropFirst(2))
        base = 2
    } else if s.hasPrefix("0") && s.count > 1 && !s.contains(".") && !s.lowercased().contains("e") {
        base = 8
    }

    // Parse suffix
    var hasL = false
    var hasU = false

    // Check for LL/ll/ULL/ull etc suffixes
    var suffixStart = s.endIndex
    let upper = s.uppercased()
    let suffixes = ["LLU", "ULL", "LL", "LU", "UL", "L", "U"]
    for suf in suffixes {
        if upper.hasSuffix(suf) {
            suffixStart = s.index(s.endIndex, offsetBy: -suf.count)
            hasL = suf.contains("L")
            hasU = suf.contains("U")
            break
        }
    }

    let numStr = String(s[s.startIndex..<suffixStart])
    guard let val = UInt64(numStr, radix: base) else { return false }
    let intVal = Int64(bitPattern: val)

    // Infer type
    let ty: SyntaxType
    if base == 10 {
        if hasL && hasU {
            ty = SyntaxType(kind: .long(isUnsigned: true), size: 8, align: 8)
        } else if hasL {
            ty = SyntaxType(kind: .long(isUnsigned: false), size: 8, align: 8)
        } else if hasU {
            ty = val >> 32 != 0
                ? SyntaxType(kind: .long(isUnsigned: true), size: 8, align: 8)
                : SyntaxType(kind: .int(isUnsigned: true), size: 4, align: 4)
        } else {
            ty = val >> 31 != 0
                ? SyntaxType(kind: .long(isUnsigned: false), size: 8, align: 8)
                : SyntaxType(kind: .int(isUnsigned: false), size: 4, align: 4)
        }
    } else {
        if hasL && hasU {
            ty = SyntaxType(kind: .long(isUnsigned: true), size: 8, align: 8)
        } else if hasL {
            ty = val >> 63 != 0
                ? SyntaxType(kind: .long(isUnsigned: true), size: 8, align: 8)
                : SyntaxType(kind: .long(isUnsigned: false), size: 8, align: 8)
        } else if hasU {
            ty = val >> 32 != 0
                ? SyntaxType(kind: .long(isUnsigned: true), size: 8, align: 8)
                : SyntaxType(kind: .int(isUnsigned: true), size: 4, align: 4)
        } else if val >> 63 != 0 {
            ty = SyntaxType(kind: .long(isUnsigned: true), size: 8, align: 8)
        } else if val >> 32 != 0 {
            ty = SyntaxType(kind: .long(isUnsigned: false), size: 8, align: 8)
        } else if val >> 31 != 0 {
            ty = SyntaxType(kind: .int(isUnsigned: true), size: 4, align: 4)
        } else {
            ty = SyntaxType(kind: .int(isUnsigned: false), size: 4, align: 4)
        }
    }

    tok.kind = .num
    tok.val = intVal
    tok.ty = ty
    return true
}

// MARK: - Tokenize string literal (for re-tokenizing in preprocessor)

public func tokenizeStringLiteral(_ tok: Token, baseType: SyntaxType) throws -> Token {
    var lexer = Lexer(source: tok.text, fileName: tok.fileName, fileNo: 1)
    var tokens = try lexer.tokenize()
    guard tokens.count >= 2 && tokens[0].kind == .str else { return tok }
    var result = tokens[0]
    // Copy metadata from original
    result.fileName = tok.fileName
    result.lineNo = tok.lineNo
    result.atBOL = tok.atBOL
    result.hasSpace = tok.hasSpace
    return result
}

// MARK: - Character classification helpers

private func isSpace(_ c: UInt8) -> Bool {
    c == UInt8(ascii: " ") || c == UInt8(ascii: "\t") || c == UInt8(ascii: "\r") || c == 0x0B || c == 0x0C
}

private func isDigit(_ c: UInt8) -> Bool {
    c >= UInt8(ascii: "0") && c <= UInt8(ascii: "9")
}

private func isAlnum(_ c: UInt8) -> Bool {
    isDigit(c) || (c >= UInt8(ascii: "a") && c <= UInt8(ascii: "z")) || (c >= UInt8(ascii: "A") && c <= UInt8(ascii: "Z")) || c == UInt8(ascii: "_")
}

private func isExpChar(_ c: UInt8) -> Bool {
    c == UInt8(ascii: "e") || c == UInt8(ascii: "E") || c == UInt8(ascii: "p") || c == UInt8(ascii: "P")
}

func isHexDigit(_ c: UInt8) -> Bool {
    isDigit(c) || (c >= UInt8(ascii: "a") && c <= UInt8(ascii: "f")) || (c >= UInt8(ascii: "A") && c <= UInt8(ascii: "F"))
}

func fromHex(_ c: UInt8) -> Int? {
    if c >= UInt8(ascii: "0") && c <= UInt8(ascii: "9") { return Int(c - UInt8(ascii: "0")) }
    if c >= UInt8(ascii: "a") && c <= UInt8(ascii: "f") { return Int(c - UInt8(ascii: "a")) + 10 }
    if c >= UInt8(ascii: "A") && c <= UInt8(ascii: "F") { return Int(c - UInt8(ascii: "A")) + 10 }
    return nil
}

private func isPunct(_ c: UInt8) -> Bool {
    switch c {
    case UInt8(ascii: "!"), UInt8(ascii: "\""), UInt8(ascii: "#"),
         UInt8(ascii: "%"), UInt8(ascii: "&"), UInt8(ascii: "'"),
         UInt8(ascii: "("), UInt8(ascii: ")"), UInt8(ascii: "*"),
         UInt8(ascii: "+"), UInt8(ascii: ","), UInt8(ascii: "-"),
         UInt8(ascii: "."), UInt8(ascii: "/"), UInt8(ascii: ":"),
         UInt8(ascii: ";"), UInt8(ascii: "<"), UInt8(ascii: "="),
         UInt8(ascii: ">"), UInt8(ascii: "?"), UInt8(ascii: "@"),
         UInt8(ascii: "["), UInt8(ascii: "\\"), UInt8(ascii: "]"),
         UInt8(ascii: "^"), UInt8(ascii: "{"), UInt8(ascii: "|"),
         UInt8(ascii: "}"), UInt8(ascii: "~"):
        return true
    default:
        return false
    }
}
