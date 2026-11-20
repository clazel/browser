//! CRC-32 of the chunks (PNG 3rd edition, 5.5 "CRC algorithm" and Annex D's
//! sample code).
//!
//! The polynomial is the reflected `0xEDB88320`, the register starts at all
//! ones and the result is its complement. The computation is bitwise (eight
//! shifts per byte), not table-driven: a table would be 256 indexed reads,
//! each one a bounds check to prove, and the chunks of an image are read once.

/// 5.5: the register before any byte.
pub const INIT: u32 = 0xFFFF_FFFF;

/// 5.5: the register after the last byte becomes the CRC.
pub const fn finish(register: u32) -> u32 {
    register ^ 0xFFFF_FFFF
}

/// 5.5 (Annex D, `update_crc`): the register after one more byte.
pub const fn update_byte(register: u32, byte: u8) -> u32 {
    let mut c = register ^ (byte as u32);
    let mut k = 0u8;
    while k < 8 {
        // Annex D: `if (c & 1) c = 0xedb88320L ^ (c >> 1); else c = c >> 1;`
        c = (c >> 1) ^ (0xEDB8_8320 & 0u32.wrapping_sub(c & 1));
        k = k.saturating_add(1);
    }
    c
}

/// 5.5: the register after every byte of `bytes`.
pub fn update(register: u32, bytes: &[u8]) -> u32 {
    let mut c = register;
    for &b in bytes {
        c = update_byte(c, b);
    }
    c
}

/// The CRC-32 of `bytes`.
pub fn crc32(bytes: &[u8]) -> u32 {
    finish(update(INIT, bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_values() {
        // The standard check value of CRC-32/ISO-HDLC.
        assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
        assert_eq!(crc32(b""), 0);
        // The IEND chunk's CRC, which every PNG ends with.
        assert_eq!(crc32(b"IEND"), 0xAE42_6082);
    }

    #[test]
    fn split_updates_agree() {
        let whole = crc32(b"hello, world");
        let part = update(update(INIT, b"hello, "), b"world");
        assert_eq!(finish(part), whole);
    }
}
