// Token types and cursor for the C parser.
// Ported from chibicc's tokenize.c token structures.

import Syntax

public enum TokenKind: Sendable {
    case ident
    case punct
    case keyword
    case str
    case num
    case ppNum
    case eof
}

public struct Token: Sendable {
    public var kind: TokenKind
    public var text: String          // source text of this token
    public var val: Int64 = 0        // integer value (for .num)
    public var fval: Double = 0      // float value (for .num)
    public var strData: [UInt8]?     // decoded string literal bytes (for .str)
    public var ty: SyntaxType?       // type for numeric/string literals
    public var fileName: String = "" // source file name
    public var lineNo: Int = 0       // line number
    public var lineDelta: Int = 0    // #line adjustment
    public var displayName: String = "" // display filename (for #line)
    public var atBOL: Bool = false   // at beginning of line
    public var hasSpace: Bool = false // preceded by space
    public var hideset: Set<String> = [] // macro names already expanded
    public var originIndex: Int? = nil // if macro-expanded, original token index

    public var loc: SourceLocation {
        SourceLocation(fileName: fileName, line: lineNo, column: 0)
    }
}

/// Array-based token stream with index cursor.
public struct TokenCursor {
    public var tokens: [Token]
    public var pos: Int

    public init(_ tokens: [Token]) {
        self.tokens = tokens
        self.pos = 0
    }

    public var current: Token {
        tokens[pos]
    }

    public var isEOF: Bool {
        pos >= tokens.count || tokens[pos].kind == .eof
    }

    public mutating func peek() -> Token {
        tokens[pos]
    }

    public mutating func advance() -> Token {
        let t = tokens[pos]
        pos += 1
        return t
    }

    public func equal(_ s: String) -> Bool {
        tokens[pos].text == s
    }

    public mutating func skip(_ s: String) throws {
        guard tokens[pos].text == s else {
            throw ParseError("expected '\(s)'", tokens[pos].loc)
        }
        pos += 1
    }

    public mutating func consume(_ s: String) -> Bool {
        if tokens[pos].text == s {
            pos += 1
            return true
        }
        return false
    }
}

public struct ParseError: Error, CustomStringConvertible {
    public let message: String
    public let loc: SourceLocation

    public init(_ message: String, _ loc: SourceLocation) {
        self.message = message
        self.loc = loc
    }

    public var description: String {
        "\(loc.fileName):\(loc.line): \(message)"
    }
}
