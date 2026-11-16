//! Adler-32 (RFC 1950 §8.2, and §2.2's "ADLER32" paragraph).

/// The modulus: "the largest prime smaller than 65536".
pub const BASE: u32 = 65521;

/// The running sums `(s1, s2)` after `data`, from `(s1, s2)`: "s1 is the sum
/// of all bytes, s2 is the sum of all s1 values. Both sums are done modulo
/// 65521."
pub fn update(s1: u32, s2: u32, data: &[u8]) -> (u32, u32) {
    let mut a = s1;
    let mut b = s2;
    for &byte in data {
        a = a.saturating_add(u32::from(byte)) % BASE;
        b = b.saturating_add(a) % BASE;
    }
    (a, b)
}

/// The checksum of `data`: "s2*65536 + s1", with "s1 initialized to 1, s2 to
/// zero".
pub fn adler32(data: &[u8]) -> u32 {
    let (a, b) = update(1, 0, data);
    (b << 16) | a
}
