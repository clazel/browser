//! Whole-number addition, subtraction and comparison on equal-length limb
//! slices, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::limb::{adc, sbb};

verus! {

/// One step of `add`'s invariant.
proof fn lemma_add_step(
    vo: nat,
    p: nat,
    limb: nat,
    c_new: nat,
    x: nat,
    y: nat,
    c_old: nat,
    va: nat,
    vb: nat,
)
    requires
        x + y + c_old == limb + c_new * base(),
        vo + c_old * p == va + vb,
    ensures
        (vo + limb * p) + c_new * (p * base()) == (va + x * p) + (vb + y * p),
{
    assert(c_new * (p * base()) + limb * p == (x + y + c_old) * p) by (nonlinear_arith)
        requires
            x + y + c_old == limb + c_new * base(),
    ;
    assert((x + y + c_old) * p == x * p + y * p + c_old * p) by (nonlinear_arith);
}

/// `a + b` for equal-length `a` and `b`: the sum's limbs and the carry
/// out of the top limb.
pub fn add(a: &[u64], b: &[u64]) -> (r: (Vec<u64>, bool))
    requires
        super::contract::same_len_requires(a@, b@),
    ensures
        super::contract::add_ensures(a@, b@, r.0@, r.1),
{
    let mut out: Vec<u64> = Vec::with_capacity(a.len());
    let mut carry = false;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            out.len() == i,
            value(out@) + (carry as nat) * limb_pow(i as nat) == value(a@.take(i as int)) + value(
                b@.take(i as int),
            ),
        decreases a.len() - i,
    {
        let x = a.get(i).cloned().unwrap_or(0);
        let y = b.get(i).cloned().unwrap_or(0);
        let (limb, c2) = adc(x, y, carry);
        proof {
            super::lemmas::lemma_value_push(out@, limb);
            super::lemmas::lemma_value_take_succ(a@, i as int);
            super::lemmas::lemma_value_take_succ(b@, i as int);
            lemma_add_step(
                value(out@),
                limb_pow(i as nat),
                limb as nat,
                c2 as nat,
                x as nat,
                y as nat,
                carry as nat,
                value(a@.take(i as int)),
                value(b@.take(i as int)),
            );
            super::lemmas::lemma_limb_pow_succ(i as nat);
        }
        out.push(limb);
        carry = c2;
        // Never wraps: i < a.len().
        i = i.saturating_add(1);
    }
    proof {
        super::lemmas::lemma_take_all(a@);
        super::lemmas::lemma_take_all(b@);
    }
    (out, carry)
}

/// One step of `sub`'s invariant.
proof fn lemma_sub_step(
    vo: nat,
    p: nat,
    d: nat,
    b_new: nat,
    x: nat,
    y: nat,
    b_old: nat,
    va: nat,
    vb: nat,
)
    requires
        x + b_new * base() == d + y + b_old,
        vo + vb == va + b_old * p,
    ensures
        (vo + d * p) + (vb + y * p) == (va + x * p) + b_new * (p * base()),
{
    assert(b_new * (p * base()) + x * p == (d + y + b_old) * p) by (nonlinear_arith)
        requires
            x + b_new * base() == d + y + b_old,
    ;
    assert((d + y + b_old) * p == d * p + y * p + b_old * p) by (nonlinear_arith);
}

/// `a - b` for equal-length `a` and `b`: the difference's limbs (modulo
/// `base^len`) and the borrow out of the top limb.
pub fn sub(a: &[u64], b: &[u64]) -> (r: (Vec<u64>, bool))
    requires
        super::contract::same_len_requires(a@, b@),
    ensures
        super::contract::sub_ensures(a@, b@, r.0@, r.1),
{
    let mut out: Vec<u64> = Vec::with_capacity(a.len());
    let mut borrow = false;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            out.len() == i,
            value(out@) + value(b@.take(i as int)) == value(a@.take(i as int)) + (borrow as nat)
                * limb_pow(i as nat),
        decreases a.len() - i,
    {
        let x = a.get(i).cloned().unwrap_or(0);
        let y = b.get(i).cloned().unwrap_or(0);
        let (d, b2) = sbb(x, y, borrow);
        proof {
            super::lemmas::lemma_value_push(out@, d);
            super::lemmas::lemma_value_take_succ(a@, i as int);
            super::lemmas::lemma_value_take_succ(b@, i as int);
            lemma_sub_step(
                value(out@),
                limb_pow(i as nat),
                d as nat,
                b2 as nat,
                x as nat,
                y as nat,
                borrow as nat,
                value(a@.take(i as int)),
                value(b@.take(i as int)),
            );
            super::lemmas::lemma_limb_pow_succ(i as nat);
        }
        out.push(d);
        borrow = b2;
        // Never wraps: i < a.len().
        i = i.saturating_add(1);
    }
    proof {
        super::lemmas::lemma_take_all(a@);
        super::lemmas::lemma_take_all(b@);
    }
    (out, borrow)
}

/// `a < b` as numbers, for equal-length `a` and `b`: the borrow of `a - b`.
pub fn lt(a: &[u64], b: &[u64]) -> (r: bool)
    requires
        super::contract::same_len_requires(a@, b@),
    ensures
        super::contract::lt_ensures(a@, b@, r),
{
    let diff = sub(a, b);
    proof {
        super::lemmas::lemma_value_bound(diff.0@);
        super::lemmas::lemma_limb_pow_pos(a@.len());
    }
    diff.1
}

} // verus!
