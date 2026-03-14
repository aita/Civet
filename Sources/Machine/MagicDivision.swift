// MARK: - Magic Number Division (Hacker's Delight)

/// Compute magic number for unsigned 32-bit division by constant d.
/// Returns (magic, shift) such that x/d = (x * magic) >> shift.
func unsignedMagic32(_ d: UInt32) -> (magic: UInt64, shift: Int) {
    precondition(d > 1)
    // Find the minimum shift s such that 2^(32+s) >= d * (2^32 mod d + 2^s)
    // Simplified: s = ceil(log2(d)), magic = ceil(2^(32+s) / d)
    let s = 32 - Int(d.leadingZeroBitCount) // ceil(log2(d)) for non-power-of-2
    let twoTo32PlusS: UInt64 = 1 << (32 + s)
    let magic = (twoTo32PlusS + UInt64(d) - 1) / UInt64(d)
    return (magic, 32 + s)
}

/// Compute magic number for signed 32-bit division by constant d.
/// Returns (magic, shift) such that x/d = (mulhi(x, magic) + adjustment) >> shift.
/// Algorithm from Hacker's Delight, Chapter 10.
func signedMagic32(_ d: Int32) -> (magic: Int64, shift: Int) {
    precondition(d > 1)
    let ad = UInt64(d)
    let t: UInt64 = 0x80000000 // 2^31
    let anc = t - 1 - (t % ad) // absolute value of nc
    var p = 31
    var q1 = t / anc
    var r1 = t - q1 * anc
    var q2 = t / ad
    var r2 = t - q2 * ad
    repeat {
        p += 1
        q1 = q1 &* 2
        r1 = r1 &* 2
        if r1 >= anc {
            q1 = q1 &+ 1
            r1 = r1 &- anc
        }
        q2 = q2 &* 2
        r2 = r2 &* 2
        if r2 >= ad {
            q2 = q2 &+ 1
            r2 = r2 &- ad
        }
    } while q1 < q2 || (q1 == q2 && r1 == 0)
    let magic = Int64(bitPattern: q2 &+ 1)
    let shift = p - 32
    return (magic, shift)
}
