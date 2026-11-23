//! Filtering (PNG 3rd edition, 9 "Filtering"): the five filter types of
//! filter method 0 (9.2) reversed, with their exact arithmetic.
//!
//! Every byte of a scanline is the filtered byte plus a prediction, modulo
//! 256 (9.2: "unsigned arithmetic modulo 256"). `a` is the byte `bpp` places
//! to the left in the same (already unfiltered) scanline, `b` the byte above
//! it in the previous unfiltered scanline, `c` the byte above `a`; outside
//! the image (before the first pixel, above the first row) they are 0 (9.2:
//! "the byte ... is taken to be zero" for bytes outside the image; the
//! caller passes a zero row as `prev` for the first scanline of a pass).

/// 9.4: the Paeth predictor of `a`, `b` and `c`.
pub fn paeth(a: u8, b: u8, c: u8) -> u8 {
    // p = a + b - c; pa = |p - a| = |b - c|, pb = |p - b| = |a - c|,
    // pc = |p - c| = |a + b - 2c|, all exact in u32.
    let (a32, b32, c32) = (u32::from(a), u32::from(b), u32::from(c));
    let pa = b32.abs_diff(c32);
    let pb = a32.abs_diff(c32);
    let pc = a32.saturating_add(b32).abs_diff(c32.saturating_mul(2));
    // 9.4: "if pa <= pb and pa <= pc then Pr = a, else if pb <= pc then Pr = b,
    // else Pr = c" (the order of the comparisons decides ties).
    if pa <= pb && pa <= pc {
        a
    } else if pb <= pc {
        b
    } else {
        c
    }
}

/// 9.3: the Average predictor, `floor((a + b) / 2)`.
pub fn average(a: u8, b: u8) -> u8 {
    // The sum is at most 510, so the half is at most 255.
    u8::try_from(u16::from(a).saturating_add(u16::from(b)) / 2).unwrap_or(u8::MAX)
}

/// 9.2: reverses filter type `filter` on one scanline's bytes `cur` (the
/// bytes after the filter-type byte), given the previous scanline's
/// unfiltered bytes `prev` (all zero for the first scanline of a pass) and
/// `bpp`, the bytes per complete pixel rounded up to 1 (9.2's "bpp").
///
/// Returns false, leaving `cur` partly changed, for a filter type above 4
/// (9.1: "a filter type is 0 to 4"). `prev` shorter than `cur` is read as
/// zeros past its end (the callers pass equal lengths).
pub fn unfilter(filter: u8, bpp: usize, prev: &[u8], cur: &mut [u8]) -> bool {
    if filter > 4 {
        return false;
    }
    let mut i = 0usize;
    while i < cur.len() {
        let left = i.checked_sub(bpp);
        let a = left.and_then(|l| cur.get(l)).copied().unwrap_or(0);
        let b = prev.get(i).copied().unwrap_or(0);
        let c = left.and_then(|l| prev.get(l)).copied().unwrap_or(0);
        if let Some(slot) = cur.get_mut(i) {
            *slot = slot.wrapping_add(match filter {
                1 => a,              // 9.2 type 1, Sub: Raw(x - bpp)
                2 => b,              // 9.2 type 2, Up: Prior(x)
                3 => average(a, b),  // 9.3 type 3, Average
                4 => paeth(a, b, c), // 9.4 type 4, Paeth
                _ => 0,              // 9.2 type 0, None
            });
        }
        i = i.saturating_add(1);
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paeth_ties_and_extremes() {
        assert_eq!(paeth(0, 0, 0), 0);
        assert_eq!(paeth(255, 0, 0), 255);
        assert_eq!(paeth(0, 255, 0), 255);
        // a + b - c = 255, pa = 0 = pb... a wins.
        assert_eq!(paeth(255, 255, 255), 255);
        assert_eq!(paeth(10, 20, 15), 15);
        assert_eq!(paeth(10, 20, 10), 20);
    }

    #[test]
    fn each_filter_on_a_known_row() {
        let prev = [10u8, 20, 30, 40];
        let mut sub = [1u8, 1, 1, 1];
        assert!(unfilter(1, 1, &prev, &mut sub));
        assert_eq!(sub, [1, 2, 3, 4]);
        let mut up = [1u8, 1, 1, 1];
        assert!(unfilter(2, 1, &prev, &mut up));
        assert_eq!(up, [11, 21, 31, 41]);
        let mut avg = [0u8, 0, 0, 0];
        assert!(unfilter(3, 1, &prev, &mut avg));
        assert_eq!(avg, [5, 12, 21, 30]);
        let mut none = [9u8, 8];
        assert!(unfilter(0, 2, &prev, &mut none));
        assert_eq!(none, [9, 8]);
        assert!(!unfilter(5, 1, &prev, &mut none));
    }

    #[test]
    fn wraps_modulo_256() {
        let mut row = [200u8, 100];
        assert!(unfilter(1, 1, &[0, 0], &mut row));
        assert_eq!(row, [200, 44]);
    }

    #[test]
    fn bpp_larger_than_the_row() {
        let mut row = [7u8, 7];
        assert!(unfilter(1, 8, &[0, 0], &mut row));
        assert_eq!(row, [7, 7]);
    }
}
