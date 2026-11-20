//! The decoding of one 8 by 8 block of the entropy-coded segment, a bit at
//! a time.
//!
//! T.81 F.2.2 (sequential decoding procedures): the DC coefficient is
//! decoded by F.2.2.1 (Figure F.12, `DECODE_DC`, with `RECEIVE` and `EXTEND`
//! of Figures F.16, F.17 and F.12) and the AC coefficients by F.2.2.2
//! (Figure F.13, `DECODE_AC_COEFFICIENTS`). Those are loops that read as
//! many bits as they need; here each bit is one call, so that the block
//! decoder can stop at any bit when the input chunk ends and go on in the
//! next call. The state between bits is the stage, the Huffman code read so
//! far, the count of bits of a value received so far, and the position in
//! the block.

use crate::huffman::{Next, Table};

/// `ZZ`, Figure A.6: the position in the 8 by 8 block (row-major) of the
/// `k`-th coefficient in zig-zag order.
pub(crate) const ZIGZAG: [u8; 64] = [
    0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27, 20,
    13, 6, 7, 14, 21, 28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58, 59,
    52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55, 62, 63,
];

/// Where in the block's syntax the decoder is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Stage {
    /// Reading the Huffman code of `T`, the size category of the DC
    /// difference (Figure F.12: `T = DECODE`).
    DcCode,
    /// Receiving the `T` bits of the DC difference (`DIFF = RECEIVE(T)`,
    /// then `EXTEND`).
    DcBits,
    /// Reading the Huffman code of `RS`, the run and size of the next AC
    /// coefficient (Figure F.13: `RS = DECODE`).
    AcCode,
    /// Receiving the `SSSS` bits of an AC coefficient (`RECEIVE(SSSS)`,
    /// then `EXTEND`).
    AcBits,
}

/// One block being decoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Block {
    stage: Stage,
    /// Huffman code read so far, `len` bits of it.
    code: u16,
    len: u8,
    /// Number of bits of the value being received, and how many came.
    size: u8,
    got: u8,
    acc: u16,
    /// Index in zig-zag order of the next coefficient (`K` of Figure F.13);
    /// during `AcBits` it is the coefficient being received.
    k: u8,
    /// The coefficients, natural order, row-major (`ZZ` already applied).
    pub coef: [i16; 64],
}

/// `EXTEND(V, T)`, Figure F.12: the signed value of the `size` bits `v`.
fn extend(v: u16, size: u8) -> Option<i32> {
    let v = i32::from(v);
    let half = 1i32.checked_shl(u32::from(size).checked_sub(1)?)?;
    if v < half {
        // `V + (-1 << T) + 1`.
        v.checked_sub(half.checked_mul(2)?)?.checked_add(1)
    } else {
        Some(v)
    }
}

impl Block {
    /// A fresh block: zero coefficients, about to read the DC code.
    pub(crate) const fn new() -> Block {
        Block {
            stage: Stage::DcCode,
            code: 0,
            len: 0,
            size: 0,
            got: 0,
            acc: 0,
            k: 0,
            coef: [0; 64],
        }
    }

    /// The invariant: counters in their ranges.
    pub(crate) fn inv(&self) -> bool {
        self.len <= 16
            && self.size <= 15
            && self.got <= self.size
            && self.k <= 64
            && match self.stage {
                Stage::DcCode => self.len < 16,
                Stage::DcBits => self.size >= 1 && self.got < self.size,
                Stage::AcCode => self.len < 16 && self.k >= 1 && self.k < 64,
                Stage::AcBits => self.size >= 1 && self.got < self.size && self.k < 64,
            }
    }

    /// The stage, for the harnesses.
    #[cfg(kani)]
    pub(crate) const fn stage(&self) -> Stage {
        self.stage
    }

    /// A block in any stage with symbolic counters, for the harnesses.
    #[cfg(kani)]
    pub(crate) fn any_block(stage: Stage) -> Block {
        Block {
            stage,
            code: kani::any(),
            len: kani::any(),
            size: kani::any(),
            got: kani::any(),
            acc: kani::any(),
            k: kani::any(),
            coef: kani::any(),
        }
    }

    /// Takes one bit of the block, with the tables of its component and
    /// its DC predictor. `Ok(true)` when the block is complete (the last
    /// coefficient was received, or `EOB`).
    pub(crate) fn bit(
        &mut self,
        bit: u8,
        dc: &Table,
        ac: &Table,
        pred: &mut i32,
    ) -> Result<bool, &'static str> {
        match self.stage {
            Stage::DcCode => match dc.step(self.code, self.len, bit) {
                Next::More { code, len } => {
                    self.code = code;
                    self.len = len;
                }
                Next::Value(t) => {
                    // Listed: DC tables hold symbols of 0 to 15 only.
                    if t == 0 {
                        self.dc_done(pred, 0)?;
                    } else if t <= 15 {
                        self.stage = Stage::DcBits;
                        self.size = t;
                        self.got = 0;
                        self.acc = 0;
                    } else {
                        return Err("DC size category over 15");
                    }
                }
                Next::Bad => return Err("bad Huffman code in a DC coefficient"),
            },
            Stage::DcBits => {
                self.push(bit)?;
                if self.got >= self.size {
                    let diff = extend(self.acc, self.size).ok_or("DC difference")?;
                    self.dc_done(pred, diff)?;
                }
            }
            Stage::AcCode => match ac.step(self.code, self.len, bit) {
                Next::More { code, len } => {
                    self.code = code;
                    self.len = len;
                }
                Next::Value(rs) => return self.ac_symbol(rs),
                Next::Bad => return Err("bad Huffman code in an AC coefficient"),
            },
            Stage::AcBits => {
                self.push(bit)?;
                if self.got >= self.size {
                    let v = extend(self.acc, self.size).ok_or("AC coefficient")?;
                    let v = i16::try_from(v).map_err(|_| "AC coefficient out of range")?;
                    let at = ZIGZAG
                        .get(usize::from(self.k))
                        .copied()
                        .ok_or("coefficient index")?;
                    *self
                        .coef
                        .get_mut(usize::from(at))
                        .ok_or("coefficient index")? = v;
                    self.k = self.k.checked_add(1).ok_or("coefficient index")?;
                    if self.k >= 64 {
                        return Ok(true);
                    }
                    self.code_next(Stage::AcCode);
                }
            }
        }
        Ok(false)
    }

    /// One more bit of the value being received (`RECEIVE`, Figure F.17).
    fn push(&mut self, bit: u8) -> Result<(), &'static str> {
        self.acc = self
            .acc
            .checked_mul(2)
            .and_then(|a| a.checked_add(u16::from(bit & 1)))
            .ok_or("bit count")?;
        self.got = self.got.checked_add(1).ok_or("bit count")?;
        Ok(())
    }

    /// Starts reading a Huffman code in `stage`.
    fn code_next(&mut self, stage: Stage) {
        self.stage = stage;
        self.code = 0;
        self.len = 0;
    }

    /// The DC difference is known: `DC = PRED + DIFF` (Figure F.12). The
    /// block's coefficient 0 must fit 16 bits (libjpeg-turbo truncates
    /// instead; a valid 8-bit stream never gets near).
    fn dc_done(&mut self, pred: &mut i32, diff: i32) -> Result<(), &'static str> {
        *pred = pred.checked_add(diff).ok_or("DC out of range")?;
        let v = i16::try_from(*pred).map_err(|_| "DC out of range")?;
        if let Some(c) = self.coef.first_mut() {
            *c = v;
        }
        self.k = 1;
        self.code_next(Stage::AcCode);
        Ok(())
    }

    /// The symbol `RS` of an AC code (Figure F.13): `R` zeros then a
    /// coefficient of `SSSS` bits; `ZRL` (`R = 15`, `SSSS = 0`) is 16 zeros;
    /// `EOB` (`R < 15`, `SSSS = 0`) ends the block.
    fn ac_symbol(&mut self, rs: u8) -> Result<bool, &'static str> {
        let r = rs >> 4;
        let s = rs & 15;
        if s == 0 {
            if r < 15 {
                // EOB: the rest are zero.
                return Ok(true);
            }
            // ZRL: `K = K + 16`.
            self.k = self
                .k
                .checked_add(16)
                .filter(|&k| k <= 64)
                .ok_or("run past the end of the block")?;
            if self.k >= 64 {
                return Ok(true);
            }
            self.code_next(Stage::AcCode);
            return Ok(false);
        }
        // `K = K + R`: the coefficient is at K.
        self.k = self
            .k
            .checked_add(r)
            .filter(|&k| k < 64)
            .ok_or("run past the end of the block")?;
        self.stage = Stage::AcBits;
        self.size = s;
        self.got = 0;
        self.acc = 0;
        Ok(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tables with the codes `0` for symbol `a` and `1` for symbol `b`.
    fn two(a: u8, b: u8, dc: bool) -> Result<Table, &'static str> {
        let mut c = [0u8; 16];
        if let Some(x) = c.first_mut() {
            *x = 2;
        }
        Table::build(&c, &[a, b], dc)
    }

    /// Feeds `bits` to a fresh block with DC symbols `0 -> 3 bits` and
    /// `1 -> 0 bits` (code `0` and `1`) and AC symbols `0 -> EOB`,
    /// `1 -> run 0 size 1` (code `0` and `1`).
    fn run(bits: &[u8], pred: &mut i32) -> Result<(Block, bool), &'static str> {
        let dc = two(3, 0, true)?;
        let ac = two(0x00, 0x01, false)?;
        let mut b = Block::new();
        let mut done = false;
        for &bit in bits {
            assert!(b.inv());
            done = b.bit(bit, &dc, &ac, pred)?;
            if done {
                break;
            }
        }
        Ok((b, done))
    }

    #[test]
    fn extend_is_figure_f12() {
        // EXTEND(V, T): T = 3: 0..3 are -7..-4, 4..7 are 4..7.
        let got: Vec<_> = (0..8u16).filter_map(|v| extend(v, 3)).collect();
        assert_eq!(got, [-7, -6, -5, -4, 4, 5, 6, 7]);
        assert_eq!(extend(0, 1), Some(-1));
        assert_eq!(extend(1, 1), Some(1));
        assert_eq!(extend(0, 0), None);
        assert_eq!(extend(0, 15), Some(-32767));
    }

    #[test]
    fn a_block_with_dc_and_eob() -> Result<(), &'static str> {
        let mut pred = 10;
        // DC code `0` (3 bits follow): 101 = 5; AC code `0` = EOB.
        let (b, done) = run(&[0, 1, 0, 1, 0], &mut pred)?;
        assert!(done);
        assert_eq!(pred, 15);
        assert_eq!(b.coef.first(), Some(&15));
        assert!(b.coef.iter().skip(1).all(|&c| c == 0));
        Ok(())
    }

    #[test]
    fn dc_category_zero_has_no_bits() -> Result<(), &'static str> {
        let mut pred = -3;
        // DC code `1` is category 0; then EOB.
        let (b, done) = run(&[1, 0], &mut pred)?;
        assert!(done);
        assert_eq!((pred, b.coef.first()), (-3, Some(&-3)));
        Ok(())
    }

    #[test]
    fn an_ac_coefficient_lands_in_zigzag_order() -> Result<(), &'static str> {
        let mut pred = 0;
        // DC category 0 (code 1); AC code `1` = (run 0, size 1), bit 1 = +1
        // at k = 1 (natural position 1); AC `1`, bit 0 = -1 at k = 2
        // (natural position 8); EOB.
        let (b, done) = run(&[1, 1, 1, 1, 0, 0], &mut pred)?;
        assert!(done);
        assert_eq!((b.coef.get(1), b.coef.get(8)), (Some(&1), Some(&-1)));
        Ok(())
    }

    #[test]
    fn a_full_block_ends_without_eob() -> Result<(), &'static str> {
        let mut pred = 0;
        // DC category 0, then 63 coefficients of (run 0, size 1) = +1.
        let mut bits = vec![1];
        for _ in 0..63 {
            bits.extend([1, 1]);
        }
        let (b, done) = run(&bits, &mut pred)?;
        assert!(done);
        assert!(b.coef.iter().skip(1).all(|&c| c == 1));
        Ok(())
    }

    #[test]
    fn a_run_past_the_end_is_an_error() -> Result<(), &'static str> {
        // AC symbol 0xF0 is ZRL; four of them from k = 1 pass 64.
        let dc = two(0, 1, true)?;
        let ac = two(0xF0, 0x00, false)?;
        let mut b = Block::new();
        let mut pred = 0;
        // DC category 0.
        assert_eq!(b.bit(0, &dc, &ac, &mut pred), Ok(false));
        // ZRL x3: k = 1 + 48 = 49, then a fourth makes 65.
        for _ in 0..3 {
            assert_eq!(b.bit(0, &dc, &ac, &mut pred), Ok(false));
        }
        assert!(b.bit(0, &dc, &ac, &mut pred).is_err());
        Ok(())
    }
}
