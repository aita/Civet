// Unicode utilities for C identifier classification and UTF-8 encoding.
// Ported from chibicc's unicode.c.

/// Encode a Unicode code point as UTF-8 bytes.
func encodeUTF8(_ c: UInt32) -> [UInt8] {
    if c <= 0x7F {
        return [UInt8(c)]
    }
    if c <= 0x7FF {
        return [
            UInt8(0xC0 | (c >> 6)),
            UInt8(0x80 | (c & 0x3F)),
        ]
    }
    if c <= 0xFFFF {
        return [
            UInt8(0xE0 | (c >> 12)),
            UInt8(0x80 | ((c >> 6) & 0x3F)),
            UInt8(0x80 | (c & 0x3F)),
        ]
    }
    return [
        UInt8(0xF0 | (c >> 18)),
        UInt8(0x80 | ((c >> 12) & 0x3F)),
        UInt8(0x80 | ((c >> 6) & 0x3F)),
        UInt8(0x80 | (c & 0x3F)),
    ]
}

/// Decode a UTF-8 code point from a byte buffer. Returns (codePoint, bytesConsumed).
func decodeUTF8(_ buf: UnsafeBufferPointer<UInt8>, at i: Int) -> (UInt32, Int) {
    let b = buf[i]
    if b < 0x80 {
        return (UInt32(b), 1)
    }
    let len: Int
    var c: UInt32
    if b >= 0xF0 {
        len = 4; c = UInt32(b & 0x07)
    } else if b >= 0xE0 {
        len = 3; c = UInt32(b & 0x0F)
    } else if b >= 0xC0 {
        len = 2; c = UInt32(b & 0x1F)
    } else {
        return (UInt32(b), 1) // invalid continuation byte
    }
    for j in 1..<len {
        guard i + j < buf.count else { break }
        c = (c << 6) | UInt32(buf[i + j] & 0x3F)
    }
    return (c, len)
}

private func inRange(_ ranges: [(UInt32, UInt32)], _ c: UInt32) -> Bool {
    for (lo, hi) in ranges {
        if lo <= c && c <= hi { return true }
    }
    return false
}

// C11 identifier start characters
private let ident1Ranges: [(UInt32, UInt32)] = [
    (0x5F, 0x5F), // '_'
    (0x61, 0x7A), // a-z
    (0x41, 0x5A), // A-Z
    (0x24, 0x24), // $
    (0x00A8, 0x00A8), (0x00AA, 0x00AA), (0x00AD, 0x00AD), (0x00AF, 0x00AF),
    (0x00B2, 0x00B5), (0x00B7, 0x00BA), (0x00BC, 0x00BE), (0x00C0, 0x00D6),
    (0x00D8, 0x00F6), (0x00F8, 0x00FF), (0x0100, 0x02FF), (0x0370, 0x167F),
    (0x1681, 0x180D), (0x180F, 0x1DBF), (0x1E00, 0x1FFF), (0x200B, 0x200D),
    (0x202A, 0x202E), (0x203F, 0x2040), (0x2054, 0x2054), (0x2060, 0x206F),
    (0x2070, 0x20CF), (0x2100, 0x218F), (0x2460, 0x24FF), (0x2776, 0x2793),
    (0x2C00, 0x2DFF), (0x2E80, 0x2FFF), (0x3004, 0x3007), (0x3021, 0x302F),
    (0x3031, 0x303F), (0x3040, 0xD7FF), (0xF900, 0xFD3D), (0xFD40, 0xFDCF),
    (0xFDF0, 0xFE1F), (0xFE30, 0xFE44), (0xFE47, 0xFFFD),
    (0x10000, 0x1FFFD), (0x20000, 0x2FFFD), (0x30000, 0x3FFFD), (0x40000, 0x4FFFD),
    (0x50000, 0x5FFFD), (0x60000, 0x6FFFD), (0x70000, 0x7FFFD), (0x80000, 0x8FFFD),
    (0x90000, 0x9FFFD), (0xA0000, 0xAFFFD), (0xB0000, 0xBFFFD), (0xC0000, 0xCFFFD),
    (0xD0000, 0xDFFFD), (0xE0000, 0xEFFFD),
]

private let ident2ExtraRanges: [(UInt32, UInt32)] = [
    (0x30, 0x39), // 0-9
    (0x24, 0x24), // $
    (0x0300, 0x036F), (0x1DC0, 0x1DFF), (0x20D0, 0x20FF),
    (0xFE20, 0xFE2F),
]

/// Returns true if `c` is valid as the first character of a C identifier.
func isIdent1(_ c: UInt32) -> Bool {
    inRange(ident1Ranges, c)
}

/// Returns true if `c` is valid as a non-first character of a C identifier.
func isIdent2(_ c: UInt32) -> Bool {
    isIdent1(c) || inRange(ident2ExtraRanges, c)
}
