//! The bit reader: bits of the stream, least significant first (RFC 9649
//! section 3.3's `ReadBits`), pushed one byte at a time.
//!
//! RFC 9649 section 3.3 ("Nomenclature") and 3.7.2.3: bits are read from the
//! least significant bit of each byte first.

/// The unread bits of the stream. A byte is pushed only when 8 more fit in
/// the 64-bit accumulator; the decoder drains it to under 32 bits after
/// every push.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Bits {
    /// The unread bits, the next one in bit 0. Bits at and above `n` are 0.
    acc: u64,
    /// How many bits of `acc` are unread (0 to 64).
    n: u8,
    /// The last byte of the chunk was pushed: no more bits will come.
    pub(crate) end: bool,
}

impl Bits {
    /// An empty reader.
    pub(crate) const fn new() -> Bits {
        Bits {
            acc: 0,
            n: 0,
            end: false,
        }
    }

    /// The invariant: the accumulator holds no bit at or past `n`.
    pub(crate) fn inv(&self) -> bool {
        self.n <= 64
            && self
                .acc
                .checked_shr(u32::from(self.n))
                .is_none_or(|rest| rest == 0)
    }

    /// How many bits are unread.
    pub(crate) fn len(&self) -> u8 {
        self.n
    }

    /// Appends the next byte of the stream. (Does nothing if the
    /// accumulator is too full; the decoder drains it after every push, so
    /// that does not happen.)
    pub(crate) fn push(&mut self, b: u8) {
        if self.n <= 56 {
            let shifted = u64::from(b).checked_shl(u32::from(self.n)).unwrap_or(0);
            self.acc |= shifted;
            self.n = self.n.saturating_add(8);
        }
    }

    /// The next 32 bits (bits not yet pushed read as 0), the next one in
    /// bit 0.
    pub(crate) fn peek32(&self) -> u32 {
        u32::try_from(self.acc & 0xFFFF_FFFF).unwrap_or(0)
    }

    /// Drops `k` bits (at most the unread ones).
    pub(crate) fn skip(&mut self, k: u8) {
        let k = k.min(self.n);
        self.acc = self.acc.checked_shr(u32::from(k)).unwrap_or(0);
        self.n = self.n.saturating_sub(k);
    }

    /// Reads `k` bits (0 to 32) if that many are unread.
    pub(crate) fn take(&mut self, k: u8) -> Option<u32> {
        if k > 32 || self.n < k {
            return None;
        }
        let mask = if k == 0 {
            0
        } else {
            u32::MAX
                .checked_shr(u32::from(32u8.saturating_sub(k)))
                .unwrap_or(0)
        };
        let v = self.peek32() & mask;
        self.skip(k);
        Some(v)
    }
}

#[cfg(kani)]
impl Bits {
    /// Any reader, the invariant not assumed.
    pub(crate) fn any() -> Bits {
        Bits {
            acc: kani::any(),
            n: kani::any(),
            end: kani::any(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_lsb_first() {
        let mut b = Bits::new();
        b.push(0b1010_0110);
        b.push(0xFF);
        assert_eq!(b.take(3), Some(0b110));
        assert_eq!(b.take(5), Some(0b10100));
        assert_eq!(b.take(8), Some(0xFF));
        assert_eq!(b.take(1), None);
        assert!(b.inv());
    }

    #[test]
    fn zero_and_wide_reads() {
        let mut b = Bits::new();
        for _ in 0..4 {
            b.push(0xAB);
        }
        assert_eq!(b.take(0), Some(0));
        assert_eq!(b.take(32), Some(0xABAB_ABAB));
        assert_eq!(b.len(), 0);
        assert_eq!(b.take(33), None);
    }
}
