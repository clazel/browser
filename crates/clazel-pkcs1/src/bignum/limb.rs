//! One-limb add and subtract with carry, proven to meet
//! [`super::contract`]. They use only wrapping operations and comparisons
//! (no `u128`), so the carry is computed from the comparison `sum < x`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Add with carry: `x + y + carry_in = carry_out * 2^64 + sum`.
pub fn adc(x: u64, y: u64, carry_in: bool) -> (r: (u64, bool))
    ensures
        super::contract::adc_ensures(x, y, carry_in, r.0, r.1),
{
    let s1 = x.wrapping_add(y);
    let c1 = s1 < x;
    let c: u64 = if carry_in {
        1
    } else {
        0
    };
    let s2 = s1.wrapping_add(c);
    let c2 = s2 < s1;
    assert(x as nat + y as nat + (carry_in as nat) == s2 as nat + ((c1 || c2) as nat) * base());
    (s2, c1 || c2)
}

/// Subtract with borrow: `x - y - borrow_in = diff - borrow_out * 2^64`.
pub fn sbb(x: u64, y: u64, borrow_in: bool) -> (r: (u64, bool))
    ensures
        super::contract::sbb_ensures(x, y, borrow_in, r.0, r.1),
{
    let d1 = x.wrapping_sub(y);
    let b1 = x < y;
    let b: u64 = if borrow_in {
        1
    } else {
        0
    };
    let d2 = d1.wrapping_sub(b);
    let b2 = d1 < b;
    assert(x as nat + ((b1 || b2) as nat) * base() == d2 as nat + y as nat + (borrow_in as nat));
    (d2, b1 || b2)
}

} // verus!
