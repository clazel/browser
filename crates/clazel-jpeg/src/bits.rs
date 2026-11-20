//! The bit reader of the entropy-coded segment.
//!
//! T.81 F.2.2.5 (Figure F.17, `NEXTBYTE` and `RECEIVE`): bits are taken
//! most significant first from the bytes of the entropy-coded segment. The
//! decoder is fed one byte at a time, so the reader holds the one byte it
//! was last given and the number of its bits not yet taken. Byte stuffing
//! (B.1.1.5: `0xFF` followed by `0x00` stands for the data byte `0xFF`) is
//! undone by the marker machine before a byte gets here.

/// The one byte being read and how many of its low bits are left.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BitReader {
    byte: u8,
    left: u8,
}

impl BitReader {
    /// A reader with no bits.
    pub(crate) const fn empty() -> BitReader {
        BitReader { byte: 0, left: 0 }
    }

    /// A reader holding `left` low bits of `byte`, for the harnesses.
    #[cfg(kani)]
    pub(crate) const fn with(byte: u8, left: u8) -> BitReader {
        BitReader { byte, left }
    }

    /// The invariant: at most the 8 bits of a byte are left.
    pub(crate) const fn inv(&self) -> bool {
        self.left <= 8
    }

    /// Takes a data byte; only called when the reader is empty.
    pub(crate) fn load(&mut self, byte: u8) {
        self.byte = byte;
        self.left = 8;
    }

    /// Drops the bits left in the byte: what a restart marker or the end
    /// of the scan does (E.1.2: the segment is padded with 1-bits to a
    /// byte boundary, and the padding is not data).
    pub(crate) fn clear(&mut self) {
        self.left = 0;
    }

    /// The next bit (0 or 1), most significant first, or `None` if the
    /// byte is used up.
    pub(crate) fn next_bit(&mut self) -> Option<u8> {
        self.left = self.left.checked_sub(1)?;
        Some((self.byte >> self.left) & 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn most_significant_first() {
        let mut r = BitReader::empty();
        assert_eq!(r.next_bit(), None);
        r.load(0b1010_0001);
        let bits: Vec<_> = std::iter::from_fn(|| r.next_bit()).collect();
        assert_eq!(bits, [1, 0, 1, 0, 0, 0, 0, 1]);
        assert!(r.next_bit().is_none() && r.inv());
        r.load(0xFF);
        r.next_bit();
        r.clear();
        assert_eq!(r.next_bit(), None);
    }
}
