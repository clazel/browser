//! Contracts the executable limb and modular arithmetic must be proven to
//! meet. Each exec function's `ensures` clause is exactly one of these
//! predicates (and its `requires`, where it has one), so reviewing these
//! and [`super::spec`] is enough to know what the implementation
//! guarantees.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Limb arithmetic.
// ---------------------------------------------------------------------

/// `adc(x, y, carry_in) -> (sum, carry_out)`: `x + y + carry_in` is the
/// two-limb number `carry_out * 2^64 + sum`.
pub open spec fn adc_ensures(x: u64, y: u64, carry_in: bool, sum: u64, carry_out: bool) -> bool {
    x as nat + y as nat + (carry_in as nat) == sum as nat + (carry_out as nat) * base()
}

/// `sbb(x, y, borrow_in) -> (diff, borrow_out)`: `x - y - borrow_in` is
/// `diff - borrow_out * 2^64`.
pub open spec fn sbb_ensures(x: u64, y: u64, borrow_in: bool, diff: u64, borrow_out: bool) -> bool {
    x as nat + (borrow_out as nat) * base() == diff as nat + y as nat + (borrow_in as nat)
}

// ---------------------------------------------------------------------
// Whole-number arithmetic on equal-length limb sequences.
// ---------------------------------------------------------------------

/// Precondition of `add` and `sub`: equal lengths.
pub open spec fn same_len_requires(a: Seq<u64>, b: Seq<u64>) -> bool {
    a.len() == b.len()
}

/// `add(a, b) -> (out, carry)`: `a + b = carry * 2^(64 len) + out`.
pub open spec fn add_ensures(a: Seq<u64>, b: Seq<u64>, out: Seq<u64>, carry: bool) -> bool {
    out.len() == a.len() && value(out) + (carry as nat) * limb_pow(a.len()) == value(a) + value(b)
}

/// `sub(a, b) -> (out, borrow)`: `a - b = out - borrow * 2^(64 len)`.
pub open spec fn sub_ensures(a: Seq<u64>, b: Seq<u64>, out: Seq<u64>, borrow: bool) -> bool {
    out.len() == a.len() && value(out) + value(b) == value(a) + (borrow as nat) * limb_pow(a.len())
}

/// `lt(a, b) -> bool`: `a < b` as numbers.
pub open spec fn lt_ensures(a: Seq<u64>, b: Seq<u64>, result: bool) -> bool {
    result == (value(a) < value(b))
}

// ---------------------------------------------------------------------
// Modular arithmetic. All operands have the modulus's length.
// ---------------------------------------------------------------------

/// Precondition of `mod_add`: equal lengths, both addends below `n`.
pub open spec fn mod_add_requires(a: Seq<u64>, b: Seq<u64>, n: Seq<u64>) -> bool {
    a.len() == n.len() && b.len() == n.len() && value(a) < value(n) && value(b) < value(n)
}

/// `mod_add(a, b, n)`: `(a + b) mod n`.
pub open spec fn mod_add_ensures(a: Seq<u64>, b: Seq<u64>, n: Seq<u64>, out: Seq<u64>) -> bool {
    out.len() == n.len() && value(out) == (value(a) + value(b)) % value(n)
}

/// Precondition of `mod_mul`: equal lengths, the first factor below `n`.
pub open spec fn mod_mul_requires(a: Seq<u64>, b: Seq<u64>, n: Seq<u64>) -> bool {
    a.len() == n.len() && b.len() == n.len() && value(a) < value(n)
}

/// `mod_mul(a, b, n)`: `(a * b) mod n`.
pub open spec fn mod_mul_ensures(a: Seq<u64>, b: Seq<u64>, n: Seq<u64>, out: Seq<u64>) -> bool {
    out.len() == n.len() && value(out) == (value(a) * value(b)) % value(n)
}

/// Precondition of `mod_exp`: equal lengths, `s < n`, `n > 1`.
pub open spec fn mod_exp_requires(s: Seq<u64>, n: Seq<u64>) -> bool {
    s.len() == n.len() && value(s) < value(n) && value(n) > 1
}

/// `mod_exp(s, e, n)`: `s^e mod n`.
pub open spec fn mod_exp_ensures(s: Seq<u64>, e: u64, n: Seq<u64>, out: Seq<u64>) -> bool {
    out.len() == n.len() && value(out) == crate::spec::modpow(value(s), e as nat, value(n))
}

// ---------------------------------------------------------------------
// Octet strings and limbs.
// ---------------------------------------------------------------------

/// Precondition of `from_be_bytes(bytes, start, limbs)`: the octets from
/// `start` on fit in `limbs` limbs.
pub open spec fn from_be_bytes_requires(bytes: Seq<u8>, start: nat, limbs: nat) -> bool {
    start <= bytes.len() && bytes.len() - start <= 8 * limbs
}

/// `from_be_bytes(bytes, start, limbs)`: OS2IP of `bytes[start..]`, in
/// `limbs` limbs.
pub open spec fn from_be_bytes_ensures(bytes: Seq<u8>, start: nat, limbs: nat, out: Seq<u64>) -> bool {
    out.len() == limbs && value(out) == crate::spec::os2ip(bytes.skip(start as int))
}

} // verus!
