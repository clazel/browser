//! A fixed-capacity unsigned big integer: `N` little-endian `u64` limbs in an
//! array, and the count of limbs in use. This is the arithmetic of the exact
//! paths of the Number conversions (StringToNumber's fallback, `toFixed`,
//! `toExponential`, `toPrecision` and the power-of-five tables). BigInt values
//! are unbounded and use the `Vec`-backed [`crate::bigint::Big`] instead.
//!
//! Why an array: Kani cannot reason about `Vec` growth. With an array every
//! operation is a loop over at most `N` limbs.
//!
//! Every operation is **total**, and total whatever `N` is, so a proof at a
//! small `N` is a proof about the same generic code that runs at the real `N`:
//!
//! - an operation whose true result needs more than `N` limbs drops the limbs
//!   that do not fit and sets [`FixedBig::lost`] (a sticky flag). The value is
//!   then wrong but defined, and `lost` says so. Callers size `N` so that it
//!   never happens ([`BIG_LIMBS_PARSE`] and [`BIG_LIMBS_FORMAT`]);
//! - `sub_assign` needs `self >= other` and gives zero otherwise; `divrem`
//!   by zero returns `(0, num)`; `divrem` is exact only if
//!   `den.bit_len() < 64 * N` (the running remainder reaches `2 * den`).
//!
//! Representation invariant (every operation keeps it; the Kani harnesses
//! assert it): `len <= N`; `limbs[len..]` are all zero; if `len > 0` then
//! `limbs[len - 1] != 0`. So zero has `len == 0`, and the derived equality is
//! numeric equality (together with the `lost` flag).

use std::cmp::Ordering;

/// Limbs for StringToNumber's exact path (`crate::parse::decimal_exact`).
///
/// At most 801 significant digits (800 and the sticky digit), then either
/// `* 10^e10` with the value below `10^310` (at most 1030 bits), or a
/// division by `10^-e10` with `-e10 <= 330 + 801 = 1131`: `10^1131` is 3757
/// bits, the dividend is shifted to 3757 + 55 bits and the running
/// remainder has one more: 3813 bits, 60 limbs. 64 limbs hold 4096 bits.
/// (Measured over the whole test suite: at most 57 limbs.)
pub const BIG_LIMBS_PARSE: usize = 64;
/// Limbs for the formatters and the power-of-five tables.
///
/// Formatters: the numerator is `m * 2^e2 * 10^scale` and the denominator
/// `2^-e2 * 10^-scale` (each factor only on the side of its sign) for a
/// 53-bit `m`, `e2` in `-1074..=971` and `scale` at most `100 + 324 + 8`
/// (`p <= 101`, a decimal exponent of at least -324, and the loop's eight
/// steps). The worst case is a tiny `x`: the numerator is `53 + 3.33 * 432`
/// bits, 1492 with the shift by one, 24 limbs; the denominator is at most
/// 1075 bits. Tables: `5^342` is 795 bits and the largest dividend is
/// `2^1718`, 27 limbs. 32 limbs hold 2048 bits. (Measured over the whole
/// test suite: at most 28 limbs, counting the pre-trim bound of `shl`, all
/// in the tables.)
pub const BIG_LIMBS_FORMAT: usize = 32;

/// `10^19`, the largest power of ten in a `u64`.
const TEN_19: u64 = 10_000_000_000_000_000_000;
/// `5^27`, the largest power of five in a `u64`.
const FIVE_27: u64 = 7_450_580_596_923_828_125;

/// A mask of the low `bits` bits.
fn low_mask(bits: u32) -> u64 {
    1u64.checked_shl(bits)
        .map_or(u64::MAX, |b| b.wrapping_sub(1))
}

/// An unsigned integer of at most `64 * N` bits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedBig<const N: usize> {
    /// Little-endian limbs; the ones from `len` on are zero.
    limbs: [u64; N],
    /// The number of limbs in use: the last one is nonzero.
    len: usize,
    /// Whether an operation ever had to drop limbs that did not fit.
    lost: bool,
}

impl<const N: usize> FixedBig<N> {
    /// Zero.
    #[must_use]
    pub fn zero() -> Self {
        Self {
            limbs: [0; N],
            len: 0,
            lost: false,
        }
    }

    /// The value `x`.
    #[must_use]
    pub fn from_u64(x: u64) -> Self {
        let mut b = Self::zero();
        b.push(x);
        b.trim();
        b
    }

    /// The value `x`.
    #[must_use]
    pub fn from_u128(x: u128) -> Self {
        let mut b = Self::zero();
        b.push(x as u64);
        b.push((x >> 64) as u64);
        b.trim();
        b
    }

    /// The value with the limbs `limbs`, least significant first.
    #[must_use]
    pub fn from_limbs(limbs: [u64; N]) -> Self {
        let mut b = Self {
            limbs,
            len: N,
            lost: false,
        };
        b.trim();
        b
    }

    /// Append the limb `v` (a nonzero one that does not fit sets `lost`).
    fn push(&mut self, v: u64) {
        match self.limbs.get_mut(self.len) {
            Some(slot) => {
                *slot = v;
                self.len = self.len.saturating_add(1);
            }
            None => self.lost |= v != 0,
        }
    }

    /// Drop zero limbs from the top.
    fn trim(&mut self) {
        while self.len > 0 && self.limbs.get(self.len.saturating_sub(1)) == Some(&0) {
            self.len = self.len.saturating_sub(1);
        }
    }

    /// Whether the value is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.len == 0
    }

    /// Whether an operation had to drop limbs that did not fit (the value is
    /// then not the true result).
    #[must_use]
    pub fn lost(&self) -> bool {
        self.lost
    }

    /// The number of limbs in use.
    #[must_use]
    pub fn limbs_used(&self) -> usize {
        self.len
    }

    /// Whether the representation invariant holds (for the Kani harnesses).
    #[must_use]
    pub fn invariant(&self) -> bool {
        self.len <= N
            && self.limbs.iter().skip(self.len).all(|&l| l == 0)
            && (self.len == 0
                || self
                    .limbs
                    .get(self.len.saturating_sub(1))
                    .is_some_and(|&l| l != 0))
    }

    /// The number of significant bits (zero for zero).
    #[must_use]
    pub fn bit_len(&self) -> u64 {
        if self.len == 0 {
            return 0;
        }
        let top = self
            .limbs
            .get(self.len.saturating_sub(1))
            .copied()
            .unwrap_or(0);
        let below = (self.len as u64).saturating_sub(1).saturating_mul(64);
        below.saturating_add(u64::from(64u32.saturating_sub(top.leading_zeros())))
    }

    /// Bit `i` (bit 0 is the least significant).
    #[must_use]
    pub fn bit(&self, i: u64) -> bool {
        let limb = usize::try_from(i / 64).unwrap_or(usize::MAX);
        match self.limbs.get(limb) {
            Some(&l) => (l >> (i % 64)) & 1 == 1,
            None => false,
        }
    }

    /// The low 128 bits.
    #[must_use]
    pub fn low_u128(&self) -> u128 {
        let lo = self.limbs.first().copied().unwrap_or(0);
        let hi = self.limbs.get(1).copied().unwrap_or(0);
        u128::from(lo) | (u128::from(hi) << 64)
    }

    /// `self *= m`.
    pub fn mul_small(&mut self, m: u64) {
        let mut carry: u128 = 0;
        for l in self.limbs.iter_mut().take(self.len) {
            // (2^64-1)^2 + (2^64-1) < 2^128, so this never wraps.
            let t = u128::from(*l)
                .wrapping_mul(u128::from(m))
                .wrapping_add(carry);
            *l = t as u64;
            carry = t >> 64;
        }
        if carry != 0 {
            self.push(carry as u64);
        }
        self.trim();
    }

    /// `self += a`.
    pub fn add_small(&mut self, a: u64) {
        let mut carry = a;
        for l in self.limbs.iter_mut().take(self.len) {
            if carry == 0 {
                break;
            }
            let (s, c) = l.overflowing_add(carry);
            *l = s;
            carry = u64::from(c);
        }
        if carry != 0 {
            self.push(carry);
        }
    }

    /// `self /= d` for a nonzero word `d`; returns the remainder. Division
    /// by zero leaves `self` alone and returns 0.
    pub fn div_small(&mut self, d: u64) -> u64 {
        if d == 0 {
            return 0;
        }
        let wide = u128::from(d);
        let mut rem: u128 = 0;
        if let Some(used) = self.limbs.get_mut(..self.len) {
            for l in used.iter_mut().rev() {
                // rem < d < 2^64, so the shift loses nothing.
                let cur = (rem << 64) | u128::from(*l);
                *l = cur.checked_div(wide).unwrap_or(0) as u64;
                rem = cur.checked_rem(wide).unwrap_or(0);
            }
        }
        self.trim();
        rem as u64
    }

    /// `self *= 10^k`.
    pub fn mul_pow10(&mut self, k: u32) {
        let mut k = k;
        while k >= 19 {
            self.mul_small(TEN_19);
            k = k.saturating_sub(19);
        }
        let mut p: u64 = 1;
        for _ in 0..k {
            p = p.saturating_mul(10);
        }
        self.mul_small(p);
    }

    /// `self *= 5^k`.
    pub fn mul_pow5(&mut self, k: u32) {
        let mut k = k;
        while k >= 27 {
            self.mul_small(FIVE_27);
            k = k.saturating_sub(27);
        }
        let mut p: u64 = 1;
        for _ in 0..k {
            p = p.saturating_mul(5);
        }
        self.mul_small(p);
    }

    /// `self = floor(self / 5^k)`: floor division composes, so this divides
    /// by `5^27` as often as it fits, then by the rest.
    pub fn div_pow5(&mut self, k: u32) {
        let mut k = k;
        while k >= 27 {
            let _ = self.div_small(FIVE_27);
            k = k.saturating_sub(27);
        }
        let mut p: u64 = 1;
        for _ in 0..k {
            p = p.saturating_mul(5);
        }
        let _ = self.div_small(p);
    }

    /// Store `v` as limb `i` of a result under construction (`lost` if the
    /// limb does not fit and is nonzero).
    fn put(&mut self, i: usize, v: u64) {
        match self.limbs.get_mut(i) {
            Some(slot) => *slot = v,
            None => self.lost |= v != 0,
        }
    }

    /// `self << bits`.
    #[must_use]
    pub fn shl(&self, bits: u64) -> Self {
        let mut out = Self::zero();
        out.lost = self.lost;
        if self.is_zero() {
            return out;
        }
        let skip = usize::try_from(bits / 64).unwrap_or(usize::MAX);
        let rem = (bits % 64) as u32;
        let mut carry: u64 = 0;
        let mut at = skip;
        for &l in self.limbs.iter().take(self.len) {
            if rem == 0 {
                out.put(at, l);
            } else {
                out.put(at, (l << rem) | carry);
                carry = l.checked_shr(64u32.saturating_sub(rem)).unwrap_or(0);
            }
            at = at.saturating_add(1);
        }
        if carry != 0 {
            out.put(at, carry);
        }
        // Every limb written is at an index of `at` or less.
        out.len = at.saturating_add(1).min(N);
        out.trim();
        out
    }

    /// `self << 1 | bit`, in place.
    fn shl1_or(&mut self, bit: bool) {
        let mut carry = u64::from(bit);
        for l in self.limbs.iter_mut().take(self.len) {
            let next = *l >> 63;
            *l = (*l << 1) | carry;
            carry = next;
        }
        if carry != 0 {
            self.push(carry);
        }
    }

    /// `self >> bits`, and whether any bit shifted out was set.
    #[must_use]
    pub fn shr(&self, bits: u64) -> (Self, bool) {
        let mut out = Self::zero();
        out.lost = self.lost;
        let skip = usize::try_from(bits / 64).unwrap_or(usize::MAX);
        let rem = (bits % 64) as u32;
        let mut sticky = false;
        for &l in self.limbs.iter().take(self.len).take(skip) {
            sticky |= l != 0;
        }
        if rem != 0 {
            sticky |= self
                .limbs
                .get(skip)
                .is_some_and(|&l| l & low_mask(rem) != 0);
        }
        let kept = self.len.saturating_sub(skip);
        for i in 0..kept {
            let j = skip.saturating_add(i);
            let l = self.limbs.get(j).copied().unwrap_or(0);
            let w = if rem == 0 {
                l
            } else {
                let next = self.limbs.get(j.saturating_add(1)).copied().unwrap_or(0);
                (l >> rem) | next.checked_shl(64u32.saturating_sub(rem)).unwrap_or(0)
            };
            out.put(i, w);
        }
        out.len = kept.min(N);
        out.trim();
        (out, sticky)
    }

    /// Numeric comparison.
    #[must_use]
    pub fn cmp_big(&self, other: &Self) -> Ordering {
        match self.len.cmp(&other.len) {
            Ordering::Equal => {
                for (a, b) in self
                    .limbs
                    .iter()
                    .take(self.len)
                    .rev()
                    .zip(other.limbs.iter().take(other.len).rev())
                {
                    match a.cmp(b) {
                        Ordering::Equal => {}
                        o => return o,
                    }
                }
                Ordering::Equal
            }
            o => o,
        }
    }

    /// `self += other`.
    pub fn add_assign(&mut self, other: &Self) {
        let mut carry = false;
        let n = self.len.max(other.len);
        // Limbs from `len` on are zero, so the sum needs no special case.
        self.len = n;
        self.lost |= other.lost;
        for (l, &o) in self.limbs.iter_mut().zip(other.limbs.iter()).take(n) {
            let (s1, c1) = l.overflowing_add(o);
            let (s2, c2) = s1.overflowing_add(u64::from(carry));
            *l = s2;
            carry = c1 | c2;
        }
        if carry {
            self.push(1);
        }
        self.trim();
    }

    /// `self -= other`. If `other > self` the result is zero.
    pub fn sub_assign(&mut self, other: &Self) {
        if self.cmp_big(other) == Ordering::Less {
            self.limbs = [0; N];
            self.len = 0;
            return;
        }
        let mut borrow = false;
        for (l, &o) in self.limbs.iter_mut().zip(other.limbs.iter()).take(self.len) {
            let (d1, b1) = l.overflowing_sub(o);
            let (d2, b2) = d1.overflowing_sub(u64::from(borrow));
            *l = d2;
            borrow = b1 | b2;
        }
        self.trim();
    }

    /// Quotient and remainder of `num / den`, by binary long division.
    /// Division by zero returns `(0, num)`.
    #[must_use]
    pub fn divrem(num: &Self, den: &Self) -> (Self, Self) {
        if den.is_zero() {
            return (Self::zero(), num.clone());
        }
        let nbits = num.bit_len();
        let mut quo = Self::zero();
        let mut rem = Self::zero();
        let mut i = nbits;
        while i > 0 {
            i = i.saturating_sub(1);
            rem.shl1_or(num.bit(i));
            if rem.cmp_big(den) != Ordering::Less {
                rem.sub_assign(den);
                let limb = usize::try_from(i / 64).unwrap_or(usize::MAX);
                if let Some(q) = quo.limbs.get_mut(limb) {
                    *q |= 1u64 << (i % 64);
                }
            }
        }
        // `nbits <= 64 * N`, so the quotient has at most `ceil(nbits / 64)`
        // limbs, all of which exist.
        quo.len = usize::try_from(nbits.div_ceil(64)).unwrap_or(0).min(N);
        quo.trim();
        let lost = num.lost | den.lost | rem.lost;
        quo.lost = lost;
        rem.lost = lost;
        (quo, rem)
    }

    /// The decimal digits, most significant first (`"0"` for zero).
    #[must_use]
    pub fn to_decimal(&self) -> String {
        if self.is_zero() {
            return "0".to_string();
        }
        let mut t = self.clone();
        let mut chunks: Vec<u64> = Vec::new();
        while !t.is_zero() {
            chunks.push(t.div_small(TEN_19));
        }
        let mut s = String::new();
        for (i, c) in chunks.iter().rev().enumerate() {
            crate::bigint::push_u64(&mut s, *c, if i == 0 { 0 } else { 19 });
        }
        s
    }

    /// `5^k`.
    #[must_use]
    pub fn pow5(k: u32) -> Self {
        let mut b = Self::from_u64(1);
        b.mul_pow5(k);
        b
    }

    /// `10^k`.
    #[must_use]
    pub fn pow10(k: u32) -> Self {
        let mut b = Self::from_u64(1);
        b.mul_pow10(k);
        b
    }
}
