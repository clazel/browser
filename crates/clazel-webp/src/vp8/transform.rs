//! The inverse transforms: RFC 6386 section 14.3 (the Walsh-Hadamard
//! transform of the Y2 block, `vp8_short_inv_walsh4x4_c`) and section 14.4
//! (the DCT of every other block, `short_idct4x4llm_c`), and section 14.5's
//! summation.
//!
//! Each RFC code block is two passes of the same 4-point butterfly, the first
//! down the four columns (`ip[0]`, `ip[4]`, `ip[8]`, `ip[12]` and the same
//! shifted by `ip++`), the second along the four rows (`ip[0]` to `ip[3]`,
//! then `ip += 4`); here the butterfly is one function and the passes
//! gather their four inputs by the index tables [`COLUMNS`] and [`ROWS`]
//! (which also keeps every index a constant). The arithmetic of each is the
//! RFC's, term by term.
//!
//! "The inputs to the inverse DCT (that is, the dequantized coefficients),
//! the intermediate 'horizontally detransformed' signal, and the completely
//! detransformed residue signal are all stored as arrays of 16-bit signed
//! integers": the intermediate arrays here are `i16` too, and a value that
//! does not fit wraps as C's conversion to `short` does (no valid stream
//! reaches it; a hostile one gets the RFC's answer).

/// `cospi8sqrt2minus1` (section 14.4).
const COSPI8SQRT2MINUS1: i32 = 20091;
/// `sinpi8sqrt2` (section 14.4).
const SINPI8SQRT2: i32 = 35468;

/// The indices of each column of a block: the inputs of the first pass.
const COLUMNS: [[usize; 4]; 4] = [[0, 4, 8, 12], [1, 5, 9, 13], [2, 6, 10, 14], [3, 7, 11, 15]];
/// The indices of each row of a block: the inputs of the second pass.
const ROWS: [[usize; 4]; 4] = [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15]];

/// The four values at `idx` of `v`.
fn gather(v: &[i16; 16], idx: &[usize; 4]) -> [i32; 4] {
    let g = |k: usize| {
        idx.get(k)
            .and_then(|&i| v.get(i))
            .copied()
            .map_or(0, i32::from)
    };
    [g(0), g(1), g(2), g(3)]
}

/// Stores `out[k]` at `idx[k]` of `v`, each converted to `i16` as C's
/// `short` assignment does (wrapping).
fn scatter(v: &mut [i16; 16], idx: &[usize; 4], out: [i32; 4]) {
    for (&i, o) in idx.iter().zip(out) {
        if let Some(slot) = v.get_mut(i) {
            *slot = o as i16;
        }
    }
}

/// One 1-D inverse WHT of `ip[0]`, `ip[1]`, `ip[2]`, `ip[3]` (the same shape
/// in the RFC's `ip[0], ip[4], ip[8], ip[12]` of its first pass): `a1`, `b1`,
/// `c1`, `d1` and the four sums `a1 + b1`, `c1 + d1`, `a1 - b1`, `d1 - c1`.
fn wht_1d([i0, i1, i2, i3]: [i32; 4]) -> [i32; 4] {
    let a1 = i0.wrapping_add(i3);
    let b1 = i1.wrapping_add(i2);
    let c1 = i1.wrapping_sub(i2);
    let d1 = i0.wrapping_sub(i3);
    [
        a1.wrapping_add(b1),
        c1.wrapping_add(d1),
        a1.wrapping_sub(b1),
        d1.wrapping_sub(c1),
    ]
}

/// `vp8_short_inv_walsh4x4_c` (section 14.3): the 16 Y2 coefficients to the
/// 16 DC coefficients of the Y blocks, in raster order of the blocks.
pub(crate) fn inverse_wht(input: &[i16; 16]) -> [i16; 16] {
    let mut output = [0i16; 16];
    // First pass: `op[0] = a1 + b1; op[4] = c1 + d1; op[8] = a1 - b1; op[12]
    // = d1 - c1`, down each column.
    for col in &COLUMNS {
        scatter(&mut output, col, wht_1d(gather(input, col)));
    }
    // Second pass: `a2 = a1 + b1; b2 = c1 + d1; c2 = a1 - b1; d2 = d1 - c1`,
    // each `(x + 3) >> 3`, along each row of the intermediate array.
    let mid = output;
    for row in &ROWS {
        let out = wht_1d(gather(&mid, row)).map(|x| x.wrapping_add(3) >> 3);
        scatter(&mut output, row, out);
    }
    output
}

/// One 1-D inverse DCT of `ip[0]`, `ip[1]`, `ip[2]`, `ip[3]` (or `ip[0]`,
/// `ip[4]`, `ip[8]`, `ip[12]`), before the output scaling: `a1 + d1`,
/// `b1 + c1`, `b1 - c1`, `a1 - d1`.
fn dct_1d([i0, i1, i2, i3]: [i32; 4]) -> [i32; 4] {
    let a1 = i0.wrapping_add(i2);
    let b1 = i0.wrapping_sub(i2);
    let temp1 = i1.wrapping_mul(SINPI8SQRT2) >> 16;
    let temp2 = i3.wrapping_add(i3.wrapping_mul(COSPI8SQRT2MINUS1) >> 16);
    let c1 = temp1.wrapping_sub(temp2);
    let temp1 = i1.wrapping_add(i1.wrapping_mul(COSPI8SQRT2MINUS1) >> 16);
    let temp2 = i3.wrapping_mul(SINPI8SQRT2) >> 16;
    let d1 = temp1.wrapping_add(temp2);
    [
        a1.wrapping_add(d1),
        b1.wrapping_add(c1),
        b1.wrapping_sub(c1),
        a1.wrapping_sub(d1),
    ]
}

/// `short_idct4x4llm_c` (section 14.4): the 16 coefficients of a block to
/// its 16 residue values, in raster order.
pub(crate) fn inverse_dct(input: &[i16; 16]) -> [i16; 16] {
    let mut output = [0i16; 16];
    // First pass, down each column: `op[shortpitch*0] = a1+d1; op[*1] =
    // b1+c1; op[*2] = b1-c1; op[*3] = a1-d1`.
    for col in &COLUMNS {
        scatter(&mut output, col, dct_1d(gather(input, col)));
    }
    // Second pass, along each row: `(a1+d1+4)>>3`, `(b1+c1+4)>>3`,
    // `(b1-c1+4)>>3`, `(a1-d1+4)>>3` at `op[0]`, `op[1]`, `op[2]`, `op[3]`.
    let mid = output;
    for row in &ROWS {
        let out = dct_1d(gather(&mid, row)).map(|x| x.wrapping_add(4) >> 3);
        scatter(&mut output, row, out);
    }
    output
}

/// Section 14.5: a pixel of the prediction plus its residue, "calculated
/// first as a 32-bit sum of the prediction and residue, and is then
/// saturated to 8-bit unsigned range".
pub(crate) fn add_residue(pred: u8, residue: i16) -> u8 {
    super::clamp255(i32::from(pred).wrapping_add(i32::from(residue)))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The RFC's `short_idct4x4llm_c`, transcribed with its pointers and
    /// loops, for comparison.
    fn rfc_idct(input: &[i16; 16]) -> [i16; 16] {
        let mut out = [0i16; 16];
        for i in 0..4usize {
            let ip = |k: usize| i32::from(input.get(i.wrapping_add(k)).copied().unwrap_or(0));
            let a1 = ip(0).wrapping_add(ip(8));
            let b1 = ip(0).wrapping_sub(ip(8));
            let temp1 = (ip(4).wrapping_mul(35468)) >> 16;
            let temp2 = ip(12).wrapping_add(ip(12).wrapping_mul(20091) >> 16);
            let c1 = temp1.wrapping_sub(temp2);
            let temp1 = ip(4).wrapping_add(ip(4).wrapping_mul(20091) >> 16);
            let temp2 = (ip(12).wrapping_mul(35468)) >> 16;
            let d1 = temp1.wrapping_add(temp2);
            for (k, v) in [
                (0usize, a1.wrapping_add(d1)),
                (12, a1.wrapping_sub(d1)),
                (4, b1.wrapping_add(c1)),
                (8, b1.wrapping_sub(c1)),
            ] {
                if let Some(s) = out.get_mut(i.wrapping_add(k)) {
                    *s = v as i16;
                }
            }
        }
        let mid = out;
        for i in 0..4usize {
            let b = i.wrapping_mul(4);
            let ip = |k: usize| i32::from(mid.get(b.wrapping_add(k)).copied().unwrap_or(0));
            let a1 = ip(0).wrapping_add(ip(2));
            let b1 = ip(0).wrapping_sub(ip(2));
            let temp1 = (ip(1).wrapping_mul(35468)) >> 16;
            let temp2 = ip(3).wrapping_add(ip(3).wrapping_mul(20091) >> 16);
            let c1 = temp1.wrapping_sub(temp2);
            let temp1 = ip(1).wrapping_add(ip(1).wrapping_mul(20091) >> 16);
            let temp2 = (ip(3).wrapping_mul(35468)) >> 16;
            let d1 = temp1.wrapping_add(temp2);
            for (k, v) in [
                (0usize, a1.wrapping_add(d1).wrapping_add(4) >> 3),
                (3, a1.wrapping_sub(d1).wrapping_add(4) >> 3),
                (1, b1.wrapping_add(c1).wrapping_add(4) >> 3),
                (2, b1.wrapping_sub(c1).wrapping_add(4) >> 3),
            ] {
                if let Some(s) = out.get_mut(b.wrapping_add(k)) {
                    *s = v as i16;
                }
            }
        }
        out
    }

    fn block(seed: u32) -> [i16; 16] {
        let mut s = seed;
        let mut b = [0i16; 16];
        for v in &mut b {
            s = s.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            *v = ((s >> 16) as i16) >> 3;
        }
        b
    }

    #[test]
    fn dct_matches_the_rfc_code() {
        for seed in 0..500 {
            let b = block(seed);
            assert_eq!(inverse_dct(&b), rfc_idct(&b), "{b:?}");
        }
    }

    #[test]
    fn dc_only_dct_is_the_shortcut() {
        // Section 20.8's DC-only path: every residue is (dc + 4) >> 3.
        for dc in [-2048i16, -9, -5, -4, -3, 0, 3, 4, 5, 100, 2047] {
            let mut b = [0i16; 16];
            if let Some(s) = b.first_mut() {
                *s = dc;
            }
            let want = (i32::from(dc) + 4) >> 3;
            assert!(inverse_dct(&b).iter().all(|&r| i32::from(r) == want));
        }
    }

    #[test]
    fn wht_dc_only_is_the_shortcut() {
        // Section 14.3's `vp8_short_inv_walsh4x4_1_c`.
        for dc in [-2048i16, -9, -5, -4, -3, 0, 3, 4, 5, 100, 2047] {
            let mut b = [0i16; 16];
            if let Some(s) = b.first_mut() {
                *s = dc;
            }
            let want = (i32::from(dc) + 3) >> 3;
            assert!(inverse_wht(&b).iter().all(|&r| i32::from(r) == want));
        }
    }

    #[test]
    fn residue_saturates() {
        assert_eq!(add_residue(250, 10), 255);
        assert_eq!(add_residue(5, -10), 0);
        assert_eq!(add_residue(100, -20), 80);
    }
}
