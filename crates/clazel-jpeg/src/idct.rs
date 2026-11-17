//! Dequantization and the inverse DCT.
//!
//! T.81 Annex A.3.3 defines the 8 by 8 inverse DCT as a real-valued sum;
//! an implementation is any approximation within the accuracy of Annex A.4
//! and Part 2. **Listed choice:** the integer algorithm of libjpeg-turbo's
//! `jidctint.c` (`jpeg_idct_islow`, "slow but accurate", after Loeffler,
//! Ligtenberg and Moschytz, with 13-bit constants and 2 extra bits between
//! the passes), so that the differential test against libjpeg-turbo can be
//! exact. The code below is that function's arithmetic, rewritten with
//! checked operations (workspace lints forbid unchecked arithmetic), and
//! without its two "all AC terms are zero" shortcuts, which compute the
//! same values (`DESCALE` of `dc << 13` is `dc << 2` exactly, and likewise
//! for rows).
//!
//! libjpeg-turbo keeps its arithmetic in `long` (64 bits on LP64) and the
//! between-pass workspace in `int`. Here everything is `i64`; for
//! coefficients and quantizers in their ranges nothing overflows (Kani
//! pair of harnesses proves it, composed: [`idct`] returns `Some` for every block of `i16`
//! coefficients and every `u16` quantizer, each dequantized value being at most
//! 2^31 in magnitude).

/// `CONST_BITS` of `jidctint.c`: the fixed-point constants have 13 bits of
/// fraction.
const CONST_BITS: u32 = 13;
/// `PASS1_BITS` of `jidctint.c`: the first pass keeps 2 extra bits.
const PASS1_BITS: u32 = 2;

// FIX(x) of `jidctint.c`, x * 2^13 rounded.
const FIX_0_298631336: i64 = 2446;
const FIX_0_390180644: i64 = 3196;
const FIX_0_541196100: i64 = 4433;
const FIX_0_765366865: i64 = 6270;
const FIX_0_899976223: i64 = 7373;
const FIX_1_175875602: i64 = 9633;
const FIX_1_501321110: i64 = 12299;
const FIX_1_847759065: i64 = 15137;
const FIX_1_961570560: i64 = 16069;
const FIX_2_053119869: i64 = 16819;
const FIX_2_562915447: i64 = 20995;
const FIX_3_072711026: i64 = 25172;

/// A number whose arithmetic is checked: `None` is overflow, and it
/// propagates through every operation. (Named methods rather than
/// operators: the workspace's `arithmetic_side_effects` lint flags the
/// operators of any type.)
#[derive(Clone, Copy)]
struct Ck(Option<i64>);

impl Ck {
    /// `self + o`.
    fn plus(self, o: Ck) -> Ck {
        Ck(self.0.zip(o.0).and_then(|(a, b)| a.checked_add(b)))
    }

    /// `self - o`.
    fn minus(self, o: Ck) -> Ck {
        Ck(self.0.zip(o.0).and_then(|(a, b)| a.checked_sub(b)))
    }

    /// `self * k`, `MULTIPLY` of `jidctint.c`.
    fn times(self, k: i64) -> Ck {
        Ck(self.0.and_then(|a| a.checked_mul(k)))
    }

    /// `LEFT_SHIFT(x, n)`: `x * 2^n`.
    fn shl(self, n: u32) -> Ck {
        Ck(self
            .0
            .and_then(|a| 1i64.checked_shl(n).and_then(|m| a.checked_mul(m))))
    }

    /// `DESCALE(x, n)`: `(x + 2^(n-1)) >> n`, an arithmetic shift (rounding
    /// half up).
    fn descale(self, n: u32) -> Ck {
        let half = 1i64.checked_shl(n.saturating_sub(1));
        Ck(self
            .0
            .zip(half)
            .and_then(|(a, h)| a.checked_add(h))
            .and_then(|a| a.checked_shr(n)))
    }
}

/// One dimension of the inverse DCT of `jidctint.c` (its even and odd
/// parts, "figure 8"), on eight inputs `x[k]`, the coefficients of
/// frequency `k`. Returns the eight outputs before the final `DESCALE`, in
/// order: `tmp10 + tmp3`, `tmp11 + tmp2`, `tmp12 + tmp1`, `tmp13 + tmp0`,
/// `tmp13 - tmp0`, `tmp12 - tmp1`, `tmp11 - tmp2`, `tmp10 - tmp3`.
fn one_d(x: &[Ck; 8]) -> [Ck; 8] {
    let at = |i: usize| x.get(i).copied().unwrap_or(Ck(Some(0)));
    // Even part: reverse the even part of the forward DCT; the rotator is
    // sqrt(2) * c(-6).
    let (z2, z3) = (at(2), at(6));
    let z1 = z2.plus(z3).times(FIX_0_541196100);
    let tmp2 = z1.plus(z3.times(-FIX_1_847759065));
    let tmp3 = z1.plus(z2.times(FIX_0_765366865));
    let (z2, z3) = (at(0), at(4));
    let tmp0 = z2.plus(z3).shl(CONST_BITS);
    let tmp1 = z2.minus(z3).shl(CONST_BITS);
    let tmp10 = tmp0.plus(tmp3);
    let tmp13 = tmp0.minus(tmp3);
    let tmp11 = tmp1.plus(tmp2);
    let tmp12 = tmp1.minus(tmp2);
    // Odd part: i0..i3 are y7, y5, y3, y1.
    let (tmp0, tmp1, tmp2, tmp3) = (at(7), at(5), at(3), at(1));
    let z1 = tmp0.plus(tmp3);
    let z2 = tmp1.plus(tmp2);
    let z3 = tmp0.plus(tmp2);
    let z4 = tmp1.plus(tmp3);
    let z5 = z3.plus(z4).times(FIX_1_175875602); // sqrt(2) * c3
    let tmp0 = tmp0.times(FIX_0_298631336);
    let tmp1 = tmp1.times(FIX_2_053119869);
    let tmp2 = tmp2.times(FIX_3_072711026);
    let tmp3 = tmp3.times(FIX_1_501321110);
    let z1 = z1.times(-FIX_0_899976223);
    let z2 = z2.times(-FIX_2_562915447);
    let z3 = z3.times(-FIX_1_961570560).plus(z5);
    let z4 = z4.times(-FIX_0_390180644).plus(z5);
    let tmp0 = tmp0.plus(z1).plus(z3);
    let tmp1 = tmp1.plus(z2).plus(z4);
    let tmp2 = tmp2.plus(z2).plus(z3);
    let tmp3 = tmp3.plus(z1).plus(z4);
    [
        tmp10.plus(tmp3),
        tmp11.plus(tmp2),
        tmp12.plus(tmp1),
        tmp13.plus(tmp0),
        tmp13.minus(tmp0),
        tmp12.minus(tmp1),
        tmp11.minus(tmp2),
        tmp10.minus(tmp3),
    ]
}

/// The post-IDCT range limit of libjpeg-turbo (`prepare_range_limit_table`
/// in `jdmaster.c`, indexed by `value & RANGE_MASK` with `RANGE_MASK` =
/// 1023): the sample level shift of +128 and clamping to 0..255 for values
/// of -512 to 511, and the table's wrap-around beyond (reachable only from
/// corrupt data), reproduced so the decoder agrees even then.
pub(crate) fn range_limit(v: i64) -> u8 {
    let i = v & 1023;
    let s = match i {
        0..=127 => i.saturating_add(128),
        128..=511 => 255,
        512..=895 => 0,
        _ => i.saturating_sub(896),
    };
    u8::try_from(s).unwrap_or(0)
}

/// Dequantizes (T.81 A.3.4, `Rij = Sij * Qij`; `coef` and `quant` are in
/// natural, row-major order, vertical frequency first) and inverse
/// transforms one block (A.3.3), giving the 64 samples row-major with the
/// level shift of +128 applied (A.3.1) and clamped to 0..255. `None` only
/// on arithmetic overflow, which the Kani harnesses `one_d_pass1_any` and `one_d_pass2_any` (composed) show cannot
/// happen.
pub(crate) fn idct(coef: &[i16; 64], quant: &[u16; 64]) -> Option<[u8; 64]> {
    // Pass 1: columns from the input, into the workspace, scaled up by
    // sqrt(8) and 2^PASS1_BITS.
    let mut ws = [0i64; 64];
    for col in 0..8usize {
        let mut x = [Ck(Some(0)); 8];
        for (row, slot) in x.iter_mut().enumerate() {
            let at = row.checked_mul(8)?.checked_add(col)?;
            let c = i64::from(*coef.get(at)?);
            let q = i64::from(*quant.get(at)?);
            *slot = Ck(Some(c)).times(q);
        }
        for (row, v) in one_d(&x).into_iter().enumerate() {
            let at = row.checked_mul(8)?.checked_add(col)?;
            *ws.get_mut(at)? = v.descale(CONST_BITS - PASS1_BITS).0?;
        }
    }
    // Pass 2: rows from the workspace, descaled by 8 and 2^PASS1_BITS.
    let mut out = [0u8; 64];
    for row in 0..8usize {
        let base = row.checked_mul(8)?;
        let mut x = [Ck(Some(0)); 8];
        for (k, slot) in x.iter_mut().enumerate() {
            *slot = Ck(Some(*ws.get(base.checked_add(k)?)?));
        }
        for (k, v) in one_d(&x).into_iter().enumerate() {
            let s = v.descale(CONST_BITS + PASS1_BITS + 3).0?;
            *out.get_mut(base.checked_add(k)?)? = range_limit(s);
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn flat_quant() -> [u16; 64] {
        [1; 64]
    }

    #[test]
    fn dc_only_blocks_are_flat() {
        // A DC of d (dequantized) gives round(d / 8) + 128 everywhere.
        for d in [
            -1024i16, -1000, -100, -9, -4, -3, 0, 3, 4, 5, 12, 100, 1016, 1023,
        ] {
            let mut c = [0i16; 64];
            if let Some(dc) = c.first_mut() {
                *dc = d;
            }
            let out = idct(&c, &flat_quant()).unwrap_or([0; 64]);
            let want = ((i32::from(d) + 4).div_euclid(8) + 128).clamp(0, 255);
            assert!(
                out.iter().all(|&s| i32::from(s) == want),
                "dc {d}: {out:?} want {want}"
            );
        }
    }

    #[test]
    fn range_limit_matches_libjpeg_turbos_table() {
        assert_eq!(range_limit(0), 128);
        assert_eq!(range_limit(127), 255);
        assert_eq!(range_limit(-128), 0);
        assert_eq!(range_limit(-129), 0);
        assert_eq!(range_limit(300), 255);
        assert_eq!(range_limit(-300), 0);
        // Wrap-around: 600 & 1023 = 600, which is in the zero region.
        assert_eq!(range_limit(600), 0);
        assert_eq!(range_limit(1024), 128);
        assert_eq!(range_limit(-1), 127);
    }

    #[test]
    fn extreme_blocks_do_not_overflow() {
        let c = [i16::MIN; 64];
        let q = [u16::MAX; 64];
        assert!(idct(&c, &q).is_some());
        let c = [i16::MAX; 64];
        assert!(idct(&c, &q).is_some());
    }

    #[test]
    fn a_single_ac_term_is_a_cosine() {
        // Coefficient (0, 1) with value 80 makes a horizontal cosine: the
        // left columns are brighter than the right ones, antisymmetric
        // about the middle (to within the rounding).
        let mut c = [0i16; 64];
        if let Some(v) = c.get_mut(1) {
            *v = 80;
        }
        let out = idct(&c, &flat_quant()).unwrap_or([0; 64]);
        let rows: Vec<Vec<i32>> = out
            .chunks(8)
            .map(|r| r.iter().map(|&s| i32::from(s) - 128).collect())
            .collect();
        let first = rows.first().cloned().unwrap_or_default();
        assert!(first.windows(2).all(|w| w.first() >= w.get(1)), "{first:?}");
        let mirrored: Vec<i32> = first.iter().rev().copied().collect();
        assert!(
            first
                .iter()
                .zip(&mirrored)
                .all(|(a, b)| a.saturating_add(*b).abs() <= 1),
            "{first:?}"
        );
        // Every row is the same.
        assert!(rows.iter().all(|r| *r == first));
    }
}

/// The overflow argument of [`idct`] in two harnesses that compose: the first
/// pass takes dequantized coefficients (at most 2^31 in magnitude: an `i16`
/// times a `u16`) and its descaled outputs are at most 2^37; the second pass
/// takes inputs of at most 2^37. Both never overflow, so [`idct`] never does.
/// (A single harness over the whole of `idct` was tried and the
/// model checker did not finish it.)
#[cfg(kani)]
mod proofs {
    use super::*;

    fn any_inputs(bound: i64) -> [Ck; 8] {
        let mut x = [Ck(Some(0)); 8];
        for slot in x.iter_mut() {
            let v: i64 = kani::any();
            kani::assume(-bound <= v && v <= bound);
            *slot = Ck(Some(v));
        }
        x
    }

    #[kani::proof]
    #[kani::unwind(10)]
    fn one_d_pass1_any() {
        let out = one_d(&any_inputs(1 << 31));
        for v in out {
            let d = v.descale(CONST_BITS - PASS1_BITS).0;
            assert!(d.is_some_and(|d| -(1i64 << 37) <= d && d <= (1i64 << 37)));
        }
    }

    #[kani::proof]
    #[kani::unwind(10)]
    fn one_d_pass2_any() {
        let out = one_d(&any_inputs(1 << 37));
        for v in out {
            assert!(v.descale(CONST_BITS + PASS1_BITS + 3).0.is_some());
        }
    }
}
