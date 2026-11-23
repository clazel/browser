//! The unbounded unsigned big integer of BigInt values: little-endian `u64`
//! limbs in a `Vec`, no trailing zero limb. It has what BigInt parsing and
//! printing need: multiply and add a word, divide by a word (with the
//! remainder), comparison, and bit access.
//!
//! The exact paths of the Number conversions use the fixed-capacity,
//! array-backed [`crate::fixed::FixedBig`] instead (Kani cannot reason about
//! `Vec` growth, and those paths are bounded). A BigInt has no bound, so it
//! stays `Vec`-backed.
//!
//! Every operation is total: division by zero leaves the value alone.

use std::cmp::Ordering;

/// An unsigned integer of unbounded size.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Big {
    /// Little-endian limbs; the last one is nonzero (so zero has none).
    limbs: Vec<u64>,
}

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
}
