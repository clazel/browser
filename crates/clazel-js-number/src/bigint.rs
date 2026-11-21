//! A small unsigned big integer: little-endian `u64` limbs, no trailing zero
//! limb. It holds the exact values the slow paths need (powers of ten and
//! five, scaled mantissas) and nothing more: add and multiply by a word,
//! shifts, comparison, subtraction, and long division.
//!
//! Every operation is total. Preconditions that cannot be stated in the type
//! (`sub_assign` needs `self >= other`; `divrem` needs a nonzero divisor)
//! have a defined answer when violated (`sub_assign` gives zero, `divrem` by
//! zero returns `(0, num)`), so no input panics.

use std::cmp::Ordering;

/// An unsigned integer of unbounded size.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Big {
    /// Little-endian limbs; the last one is nonzero (so zero has none).
    limbs: Vec<u64>,
}

/// `10^19`, the largest power of ten in a `u64`.
const TEN_19: u64 = 10_000_000_000_000_000_000;
/// `5^27`, the largest power of five in a `u64`.
const FIVE_27: u64 = 7_450_580_596_923_828_125;

/// Append the decimal digits of `v`, padded with zeros on the left to at
/// least `width` digits (`v = 0` prints one digit when `width` is 0).
pub fn push_u64(s: &mut String, v: u64, width: usize) {
    let mut buf = [b'0'; 20];
    let mut n = v;
    let mut used = 0usize;
    for slot in buf.iter_mut().rev() {
        *slot = b'0'.wrapping_add((n % 10) as u8);
        n /= 10;
        used = used.saturating_add(1);
        if n == 0 {
            break;
        }
    }
    let digits = used.max(width).min(20);
    for _ in 0..width.saturating_sub(20) {
        s.push('0');
    }
    for &b in buf.iter().skip(20usize.saturating_sub(digits)) {
        s.push(char::from(b));
    }
}

/// A mask of the low `bits` bits.
fn low_mask(bits: u32) -> u64 {
    1u64.checked_shl(bits)
        .map_or(u64::MAX, |b| b.wrapping_sub(1))
}

impl Big {
    /// Zero.
    #[must_use]
    pub fn zero() -> Self {
        Self { limbs: Vec::new() }
    }

    /// The value `x`.
    #[must_use]
    pub fn from_u64(x: u64) -> Self {
        let mut b = Self { limbs: vec![x] };
        b.trim();
        b
    }

    /// The value `x`.
    #[must_use]
    pub fn from_u128(x: u128) -> Self {
        let mut b = Self {
            limbs: vec![x as u64, (x >> 64) as u64],
        };
        b.trim();
        b
    }

    fn trim(&mut self) {
        while self.limbs.last() == Some(&0) {
            self.limbs.pop();
        }
    }

    /// Whether the value is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    /// The number of significant bits (zero for zero).
    #[must_use]
    pub fn bit_len(&self) -> u64 {
        match self.limbs.last() {
            None => 0,
            Some(&top) => {
                let below = (self.limbs.len() as u64)
                    .saturating_sub(1)
                    .saturating_mul(64);
                below.saturating_add(u64::from(64u32.saturating_sub(top.leading_zeros())))
            }
        }
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
        for l in &mut self.limbs {
            // (2^64-1)^2 + (2^64-1) < 2^128, so this never wraps.
            let t = u128::from(*l)
                .wrapping_mul(u128::from(m))
                .wrapping_add(carry);
            *l = t as u64;
            carry = t >> 64;
        }
        if carry != 0 {
            self.limbs.push(carry as u64);
        }
        self.trim();
    }

    /// `self += a`.
    pub fn add_small(&mut self, a: u64) {
        let mut carry = a;
        for l in &mut self.limbs {
            if carry == 0 {
                break;
            }
            let (s, c) = l.overflowing_add(carry);
            *l = s;
            carry = u64::from(c);
        }
        if carry != 0 {
            self.limbs.push(carry);
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
        for l in self.limbs.iter_mut().rev() {
            // rem < d < 2^64, so the shift loses nothing.
            let cur = (rem << 64) | u128::from(*l);
            *l = cur.checked_div(wide).unwrap_or(0) as u64;
            rem = cur.checked_rem(wide).unwrap_or(0);
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

    /// `self << bits`.
    #[must_use]
    pub fn shl(&self, bits: u64) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let limbs = usize::try_from(bits / 64).unwrap_or(usize::MAX);
        let rem = (bits % 64) as u32;
        let mut out = vec![0u64; limbs];
        let mut carry: u64 = 0;
        for &l in &self.limbs {
            if rem == 0 {
                out.push(l);
            } else {
                out.push((l << rem) | carry);
                carry = l.checked_shr(64u32.saturating_sub(rem)).unwrap_or(0);
            }
        }
        if carry != 0 {
            out.push(carry);
        }
        let mut b = Self { limbs: out };
        b.trim();
        b
    }

    /// `self << 1 | bit`, in place.
    fn shl1_or(&mut self, bit: bool) {
        let mut carry = u64::from(bit);
        for l in &mut self.limbs {
            let next = *l >> 63;
            *l = (*l << 1) | carry;
            carry = next;
        }
        if carry != 0 {
            self.limbs.push(carry);
        }
    }

    /// `self >> bits`, and whether any bit shifted out was set.
    #[must_use]
    pub fn shr(&self, bits: u64) -> (Self, bool) {
        let limbs = usize::try_from(bits / 64).unwrap_or(usize::MAX);
        let rem = (bits % 64) as u32;
        let mut sticky = false;
        for &l in self.limbs.iter().take(limbs) {
            sticky |= l != 0;
        }
        let kept: Vec<u64> = self.limbs.iter().skip(limbs).copied().collect();
        let mut out = Vec::with_capacity(kept.len());
        if rem == 0 {
            out.extend_from_slice(&kept);
        } else {
            sticky |= kept.first().is_some_and(|&l| l & low_mask(rem) != 0);
            for (i, &l) in kept.iter().enumerate() {
                let next = kept.get(i.saturating_add(1)).copied().unwrap_or(0);
                out.push((l >> rem) | next.checked_shl(64u32.saturating_sub(rem)).unwrap_or(0));
            }
        }
        let mut b = Self { limbs: out };
        b.trim();
        (b, sticky)
    }

    /// Numeric comparison.
    #[must_use]
    pub fn cmp_big(&self, other: &Self) -> Ordering {
        match self.limbs.len().cmp(&other.limbs.len()) {
            Ordering::Equal => {
                for (a, b) in self.limbs.iter().rev().zip(other.limbs.iter().rev()) {
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
        let n = self.limbs.len().max(other.limbs.len());
        self.limbs.resize(n, 0);
        for (i, l) in self.limbs.iter_mut().enumerate() {
            let o = other.limbs.get(i).copied().unwrap_or(0);
            let (s1, c1) = l.overflowing_add(o);
            let (s2, c2) = s1.overflowing_add(u64::from(carry));
            *l = s2;
            carry = c1 | c2;
        }
        if carry {
            self.limbs.push(1);
        }
        self.trim();
    }

    /// `self -= other`. If `other > self` the result is zero.
    pub fn sub_assign(&mut self, other: &Self) {
        if self.cmp_big(other) == Ordering::Less {
            self.limbs.clear();
            return;
        }
        let mut borrow = false;
        for (i, l) in self.limbs.iter_mut().enumerate() {
            let o = other.limbs.get(i).copied().unwrap_or(0);
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
        let qlimbs = usize::try_from(nbits.div_ceil(64)).unwrap_or(0);
        let mut quo = vec![0u64; qlimbs];
        let mut rem = Self::zero();
        let mut i = nbits;
        while i > 0 {
            i = i.saturating_sub(1);
            rem.shl1_or(num.bit(i));
            if rem.cmp_big(den) != Ordering::Less {
                rem.sub_assign(den);
                let limb = usize::try_from(i / 64).unwrap_or(usize::MAX);
                if let Some(q) = quo.get_mut(limb) {
                    *q |= 1u64 << (i % 64);
                }
            }
        }
        let mut q = Self { limbs: quo };
        q.trim();
        (q, rem)
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
            push_u64(&mut s, *c, if i == 0 { 0 } else { 19 });
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
