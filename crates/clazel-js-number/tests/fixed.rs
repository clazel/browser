//! `FixedBig<2>` against `u128` arithmetic, including the cases where the
//! result does not fit and `lost` must say so.

use clazel_js_number::fixed::FixedBig;
use std::cmp::Ordering;

type B = FixedBig<2>;

/// SplitMix64: a fixed-seed generator, so a failure reproduces.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// A value with a random bit length, so short values are common.
    fn wide(&mut self) -> u128 {
        let v = (u128::from(self.next()) << 64) | u128::from(self.next());
        v.checked_shr((self.next() % 128) as u32).unwrap_or(0)
    }
}

#[test]
fn matches_u128() {
    let mut rng = Rng(0x00F1_8ED0_0000_0001);
    let n = if cfg!(miri) { 20 } else { 200_000 };
    for _ in 0..n {
        let x = rng.wide();
        let y = rng.wide();
        let w = rng.next();
        let ww = u128::from(w);
        let bx = B::from_u128(x);
        let by = B::from_u128(y);
        assert!(bx.invariant() && by.invariant());
        assert_eq!(bx.low_u128(), x);
        assert_eq!(bx.bit_len(), u64::from(128 - x.leading_zeros()));
        assert_eq!(bx.cmp_big(&by), x.cmp(&y));
        assert_eq!(bx.cmp_big(&bx), Ordering::Equal);

        let mut s = bx.clone();
        s.add_assign(&by);
        assert!(s.invariant());
        assert_eq!(s.low_u128(), x.wrapping_add(y));
        assert_eq!(s.lost(), x.checked_add(y).is_none());

        let mut d = bx.clone();
        d.sub_assign(&by);
        assert!(d.invariant());
        assert_eq!(d.low_u128(), x.saturating_sub(y));
        assert!(!d.lost());

        let mut m = bx.clone();
        m.mul_small(w);
        assert!(m.invariant());
        assert_eq!(m.low_u128(), x.wrapping_mul(ww));
        assert_eq!(m.lost(), x.checked_mul(ww).is_none());

        let mut a = bx.clone();
        a.add_small(w);
        assert!(a.invariant());
        assert_eq!(a.low_u128(), x.wrapping_add(ww));
        assert_eq!(a.lost(), x.checked_add(ww).is_none());

        let mut q = bx.clone();
        let r = q.div_small(w);
        assert!(q.invariant());
        if w == 0 {
            assert_eq!((q.low_u128(), r), (x, 0));
        } else {
            assert_eq!(q.low_u128(), x.checked_div(ww).unwrap_or(0));
            assert_eq!(u128::from(r), x.checked_rem(ww).unwrap_or(0));
        }

        let sh = rng.next() % 140;
        let shu = sh as u32;
        let l = bx.shl(sh);
        assert!(l.invariant());
        let shifted = x.checked_shl(shu).unwrap_or(0);
        let fits = sh < 128 && shifted.checked_shr(shu) == Some(x);
        assert_eq!(l.lost(), !fits && x != 0);
        if sh < 128 {
            assert_eq!(l.low_u128(), shifted);
        }
        let (rs, sticky) = bx.shr(sh);
        assert!(rs.invariant());
        if sh < 128 {
            assert_eq!(rs.low_u128(), x.checked_shr(shu).unwrap_or(0));
            let mask = 1u128.checked_shl(shu).unwrap_or(0).wrapping_sub(1);
            assert_eq!(sticky, x & mask != 0);
        } else {
            assert_eq!(rs.low_u128(), 0);
            assert_eq!(sticky, x != 0);
        }

        // divrem is exact while the divisor leaves a spare bit.
        if y != 0 && y < 1 << 127 {
            let (qq, rr) = B::divrem(&bx, &by);
            assert!(qq.invariant() && rr.invariant());
            assert_eq!(qq.low_u128(), x.checked_div(y).unwrap_or(0));
            assert_eq!(rr.low_u128(), x.checked_rem(y).unwrap_or(0));
            assert!(!qq.lost());
        }
        let (z, same) = B::divrem(&bx, &B::zero());
        assert!(z.is_zero());
        assert_eq!(same, bx);
    }
}

#[test]
fn zero_and_decimal() {
    assert!(B::zero().is_zero());
    assert_eq!(B::zero().to_decimal(), "0");
    assert_eq!(B::from_u128(u128::MAX).to_decimal(), u128::MAX.to_string());
    assert!(!B::from_u128(u128::MAX).lost());
    // 10^40 does not fit in 128 bits.
    assert!(B::pow10(40).lost());
    assert!(!B::pow10(38).lost());
}
