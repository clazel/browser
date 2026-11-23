//! The boolean entropy decoder: RFC 6386 section 7.3 ("Actual
//! Implementation", the `bool_decoder` of its code block) and section 8.1's
//! `treed_read`, with section 8's `L(n)` literals.
//!
//! Modelling choices (the argument that the meaning is unchanged is each
//! one's):
//!
//! - **The input is a slice and a position**, not a pointer: `input` is
//!   `data[next..]`. Reading past the end of the slice gives the byte 0, so
//!   the decoder is total.
//! - **`eof`**, the one addition, says the partition was too short. The RFC
//!   reads its input eagerly (two bytes at the start, the next one as soon
//!   as 8 bits were shifted out) and says nothing of a partition that ends
//!   early. `eof` is set when a `read_bool` starts after more bits were
//!   shifted out than the partition's bytes hold: after `s` shifts, the next
//!   decision needs byte number `ceil(s / 8) + 1` (counting from 1), because
//!   its comparison uses the top 8 bits of the 16 in `value`, and `eof` is
//!   set exactly when that byte is not in the slice. That is libwebp's
//!   `eof_` (it loads a byte only when a decision needs it, and flags the
//!   first load that finds none), and the RFC's own decoder, which loads a
//!   byte early, would flag a valid partition one byte too soon. Where a
//!   partition's end is checked is the caller's (`vp8/mod.rs`).
//! - The count of shifts is kept in a `u64`, the position in a `usize`, and
//!   both saturate; neither can reach that in a partition under 2^24 bytes.

/// `Prob` (section 7): the probability, out of 256, of a zero.
pub(crate) type Prob = u8;

/// The decoder state of section 7.3's `bool_decoder`.
#[derive(Debug, Clone)]
pub(crate) struct BoolDecoder<'a> {
    /// The partition's bytes.
    input: &'a [u8],
    /// Index in `input` of the next byte to be read (`input` in the RFC).
    next: usize,
    /// "always identical to encoder's range": 128 to 255 between calls.
    range: u32,
    /// "contains at least 8 significant bits": under `range << 8` between
    /// calls.
    value: u32,
    /// "# of bits shifted out of value, at most 7".
    bit_count: u32,
    /// Bits shifted out in all (for `eof`).
    shifts: u64,
    /// A decision was read after the partition's bytes ran out.
    eof: bool,
}

impl<'a> BoolDecoder<'a> {
    /// `init_bool_decoder`: "value = first 2 input bytes", `range` 255,
    /// `bit_count` 0.
    pub(crate) fn new(input: &'a [u8]) -> BoolDecoder<'a> {
        let first = u32::from(input.first().copied().unwrap_or(0));
        let second = u32::from(input.get(1).copied().unwrap_or(0));
        BoolDecoder {
            input,
            next: 2,
            range: 255,
            value: (first << 8) | second,
            bit_count: 0,
            shifts: 0,
            eof: false,
        }
    }

    /// The invariant: `range` and `value` are in the ranges the RFC's
    /// comments give (`value < range << 8` is what makes every later `value`
    /// fit 16 bits), and the counters are in theirs.
    #[cfg(any(test, kani))]
    pub(crate) fn inv(&self) -> bool {
        (128..=255).contains(&self.range)
            && self.value < self.range << 8
            && self.bit_count < 8
            && self.next >= 2
    }

    /// A decision was needed after the partition's bytes ran out (see the
    /// module's `eof`).
    pub(crate) fn eof(&self) -> bool {
        self.eof
    }

    /// The next input byte, 0 past the end.
    fn byte(&mut self) -> u32 {
        let b = self.input.get(self.next).copied().unwrap_or(0);
        self.next = self.next.saturating_add(1);
        u32::from(b)
    }

    /// `read_bool`: a bool encoded at probability `prob / 256` of a zero.
    pub(crate) fn read_bool(&mut self, prob: Prob) -> bool {
        if !self.eof {
            let needed = self.shifts.div_ceil(8).saturating_add(1);
            if u64::try_from(self.input.len()).is_ok_and(|len| needed > len) {
                self.eof = true;
            }
        }
        // "split is approximately (range * prob) / 256 and, crucially, is
        // strictly bigger than zero and strictly smaller than range"
        let split =
            1u32.wrapping_add(self.range.wrapping_sub(1).wrapping_mul(u32::from(prob)) >> 8);
        let big_split = split << 8;
        let bit = if self.value >= big_split {
            self.range = self.range.wrapping_sub(split);
            self.value = self.value.wrapping_sub(big_split);
            true
        } else {
            self.range = split;
            false
        };
        // "shift out irrelevant value bits"
        while self.range < 128 {
            self.value <<= 1;
            self.range <<= 1;
            self.shifts = self.shifts.saturating_add(1);
            self.bit_count = self.bit_count.wrapping_add(1);
            if self.bit_count == 8 {
                // "shift in new bits 8 at a time"
                self.bit_count = 0;
                self.value |= self.byte();
            }
        }
        bit
    }

    /// `read_literal` (`L(n)`): an `n`-bit unsigned value, "high- to
    /// low-order, with each bit encoded at probability 128".
    pub(crate) fn read_literal(&mut self, n: u32) -> u32 {
        let mut v = 0u32;
        for _ in 0..n {
            v = (v << 1) | u32::from(self.read_bool(128));
        }
        v
    }

    /// `Flag` (`F`): `read_bool(d, 128)`.
    pub(crate) fn read_flag(&mut self) -> bool {
        self.read_bool(128)
    }

    /// The header's optional signed value, section 9.6's `delta()` and the
    /// reference decoder's `bool_maybe_get_int` (section 20.2): a flag, and
    /// if it is set an `n`-bit magnitude then a sign bit (1 is negative);
    /// 0 if the flag is clear.
    pub(crate) fn read_maybe_signed(&mut self, n: u32) -> i32 {
        if !self.read_flag() {
            return 0;
        }
        let magnitude = i32::try_from(self.read_literal(n)).unwrap_or(0);
        if self.read_flag() {
            magnitude.wrapping_neg()
        } else {
            magnitude
        }
    }

    /// `treed_read` (section 8.1): descend `tree` from node `start` (0 is the
    /// root; the coefficient tree is entered at 2 to skip `dct_eob`) with the
    /// node probabilities `probs` (indexed by half the node index) until a
    /// leaf: "a nonpositive entry v corresponds to a leaf whose value is
    /// -v". A tree that is not well formed (not a case here: the trees are
    /// constants, and a unit test checks them) ends at leaf 0 after 16 steps.
    pub(crate) fn read_tree(&mut self, tree: &[i8], probs: &[Prob], start: usize) -> usize {
        let mut i = start;
        for _ in 0..16 {
            let p = probs.get(i >> 1).copied().unwrap_or(128);
            let branch = i.saturating_add(usize::from(self.read_bool(p)));
            let t = tree.get(branch).copied().unwrap_or(0);
            match usize::try_from(t) {
                Ok(next) if next > 0 => i = next,
                _ => return usize::from(t.unsigned_abs()),
            }
        }
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A bool encoder written from the RFC's section 7.3 encoder code block
    /// (shares nothing with the decoder), to round-trip.
    struct Encoder {
        out: Vec<u8>,
        range: u32,
        bottom: u32,
        bit_count: i32,
    }

    impl Encoder {
        fn new() -> Encoder {
            Encoder {
                out: Vec::new(),
                range: 255,
                bottom: 0,
                bit_count: 24,
            }
        }

        /// `add_one_to_output`: carry into the bytes already written.
        fn add_one(&mut self) {
            for b in self.out.iter_mut().rev() {
                if *b == 255 {
                    *b = 0;
                } else {
                    *b = b.wrapping_add(1);
                    break;
                }
            }
        }

        fn write(&mut self, prob: u8, bit: bool) {
            let split =
                1u32.wrapping_add(self.range.wrapping_sub(1).wrapping_mul(u32::from(prob)) >> 8);
            if bit {
                self.bottom = self.bottom.wrapping_add(split);
                self.range = self.range.wrapping_sub(split);
            } else {
                self.range = split;
            }
            while self.range < 128 {
                self.range <<= 1;
                if self.bottom & (1 << 31) != 0 {
                    self.add_one();
                }
                self.bottom <<= 1;
                self.bit_count = self.bit_count.wrapping_sub(1);
                if self.bit_count == 0 {
                    self.out.push((self.bottom >> 24) as u8);
                    self.bottom &= (1 << 24) - 1;
                    self.bit_count = 8;
                }
            }
        }

        fn flush(mut self) -> Vec<u8> {
            let c = u32::try_from(self.bit_count).unwrap_or(0);
            let mut v = self.bottom;
            if v & (1u32.checked_shl(32u32.wrapping_sub(c)).unwrap_or(0)) != 0 {
                self.add_one();
            }
            v <<= c & 7;
            for _ in 0..(c >> 3) {
                v <<= 8;
            }
            for _ in 0..4 {
                self.out.push((v >> 24) as u8);
                v <<= 8;
            }
            self.out
        }
    }

    #[test]
    fn round_trip() {
        let mut state = 0x1234_5678u32;
        let mut next = move || {
            state = state.wrapping_mul(1_103_515_245).wrapping_add(12_345);
            state >> 8
        };
        for round in 0..50 {
            let mut enc = Encoder::new();
            let mut sent = Vec::new();
            for _ in 0..(round * 37 + 5) {
                let prob = u8::try_from(next() % 255 + 1).unwrap_or(1);
                // Skewed so that the probabilities matter.
                let bit = u32::from(prob) * (next() % 256) < 256 * 128;
                sent.push((prob, !bit));
            }
            for &(p, b) in &sent {
                enc.write(p, b);
            }
            let bytes = enc.flush();
            let mut dec = BoolDecoder::new(&bytes);
            for &(p, b) in &sent {
                assert!(dec.inv());
                assert_eq!(dec.read_bool(p), b);
            }
            // The encoder pads, so the partition is not exhausted.
            assert!(!dec.eof());
        }
    }

    #[test]
    fn literal_and_signed() {
        let mut enc = Encoder::new();
        // L(7) = 0b1010011, then F? L(4) F as 1, 0b0101, 1 (= -5), then a
        // clear flag.
        for b in [1, 0, 1, 0, 0, 1, 1] {
            enc.write(128, b == 1);
        }
        for b in [1, 0, 1, 0, 1, 1, 0] {
            enc.write(128, b == 1);
        }
        let bytes = enc.flush();
        let mut dec = BoolDecoder::new(&bytes);
        assert_eq!(dec.read_literal(7), 0b101_0011);
        assert_eq!(dec.read_maybe_signed(4), -5);
        assert_eq!(dec.read_maybe_signed(4), 0);
    }

    #[test]
    fn eof_is_libwebps() {
        // A 1-byte partition: the first decision is fine, and after one
        // shift the second needs byte 2.
        let mut dec = BoolDecoder::new(&[0x00]);
        assert!(!dec.read_bool(128));
        assert!(!dec.eof());
        // Probability 128 on value 0: range 255 -> split 128 -> range 128,
        // no shift yet; a zero at 1: range = 1 + (127 * 1 >> 8) = 1, 7 shifts.
        assert!(!dec.read_bool(1));
        assert!(!dec.eof());
        assert!(!dec.read_bool(128));
        assert!(dec.eof(), "7 shifts were made, byte 2 is needed");
        // An empty partition is exhausted at once.
        let mut dec = BoolDecoder::new(&[]);
        assert!(!dec.read_bool(128));
        assert!(dec.eof());
    }

    #[test]
    fn tree() {
        use crate::vp8::tables::{B_HU_PRED, BMODE_TREE};
        // All ones at probability 128 walk the rightmost path: B_HU_PRED.
        let mut enc = Encoder::new();
        for _ in 0..8 {
            enc.write(128, true);
        }
        let bytes = enc.flush();
        let mut dec = BoolDecoder::new(&bytes);
        let got = dec.read_tree(&BMODE_TREE, &[128; 9], 0);
        assert_eq!(got, usize::from(B_HU_PRED));
    }
}
