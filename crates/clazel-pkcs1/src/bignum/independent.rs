//! An independent transcription of the multiple-precision product, from
//! Menezes, van Oorschot and Vanstone, *Handbook of Applied Cryptography*
//! (CRC Press, 1996), chapter 14 (free at <https://cacr.uwaterloo.ca/hac/>):
//! Algorithm 14.12, "Multiple-precision multiplication", in the radix
//! `b = 2^64`. (The task brief calls the multiplication Algorithm 14.7; in
//! the 1996 numbering as the author recalls it, 14.7 is multiple-precision
//! *addition* and 14.12 the multiplication. The chapter's PDF could not be
//! read in this environment, so the numbers are from memory and should be
//! checked against the book.) The exponentiation counterpart, Algorithm
//! 14.79, is in `crate::independent`.
//!
//! Written without re-reading `bignum/spec.rs` or `modular.rs`. It is
//! used to show that the contract's modular product, `(a b) mod n`,
//! is the remainder of Algorithm 14.12's product: the executable
//! double-and-add `mod_mul` is proven against `(value(a) value(b)) mod
//! value(n)`, and [`lemma_hac_14_12_value`] proves that the schoolbook
//! product of a different algorithm is `value(x) value(y)`, with the
//! carries of step 2.2 never overflowing.
//!
//! Not transcribed: Algorithm 14.20 (multiple-precision division). The
//! reduction `mod n` in the contract is the mathematical remainder, and
//! the executable code reduces by conditional subtraction after each
//! addition (`modular.rs`), not by 14.20, so there is no 14.20 for the
//! exec code to be compared with.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Algorithm 14.12, steps 2.2 and 2.3 for one row: "2.2 For j from 0 to n
/// do the following: compute (uv)_b = w_(i+j) + x_j . y_i + c, and set
/// w_(i+j) <- v, c <- u. 2.3 w_(i+n+1) <- u." `x` has the digits
/// `x_0 .. x_n`, so `n + 1` is `x.len()`.
pub open spec fn hac12_row(w: Seq<u64>, x: Seq<u64>, yi: u64, i: nat, j: nat, c: u64) -> Seq<u64>
    decreases x.len() - j,
{
    if j >= x.len() {
        // 2.3
        w.update((i + x.len()) as int, c)
    } else {
        // 2.2: (u v)_b = w_(i+j) + x_j y_i + c.
        let uv = (w[(i + j) as int] as nat) + (x[j as int] as nat) * (yi as nat) + (c as nat);
        let v = (uv % base()) as u64;
        let u = (uv / base()) as u64;
        hac12_row(w.update((i + j) as int, v), x, yi, i, j + 1, u)
    }
}

/// Step 2, "for i from 0 to t": the rows for `y_i, y_(i+1), ...`.
pub open spec fn hac12_rows(w: Seq<u64>, x: Seq<u64>, y: Seq<u64>, i: nat) -> Seq<u64>
    decreases y.len() - i,
{
    if i >= y.len() {
        w
    } else {
        // 2.1 c <- 0 is the last argument of `hac12_row`.
        hac12_rows(hac12_row(w, x, y[i as int], i, 0, 0), x, y, i + 1)
    }
}

/// Algorithm 14.12: "INPUT: positive integers x and y having n + 1 and
/// t + 1 base b digits, respectively. OUTPUT: the product x . y = (w_(n+t+1)
/// ... w_1 w_0)_b. 1. For i from 0 to (n + t + 1) do: w_i <- 0. 2. For i
/// from 0 to t do ... 3. Return((w_(n+t+1) w_(n+t) ... w_1 w_0))."
pub open spec fn hac_14_12(x: Seq<u64>, y: Seq<u64>) -> Seq<u64> {
    // 1.
    let w0 = Seq::new(x.len() + y.len(), |k: int| 0u64);
    // 2.-3.
    hac12_rows(w0, x, y, 0)
}

// ---------------------------------------------------------------------
// Lemmas.
// ---------------------------------------------------------------------

/// `base^(a + b) = base^a base^b`.
proof fn lemma_limb_pow_add(a: nat, b: nat)
    ensures
        limb_pow(a + b) == limb_pow(a) * limb_pow(b),
    decreases b,
{
    if b == 0 {
        assert(limb_pow(0) == 1);
    } else {
        lemma_limb_pow_add(a, (b - 1) as nat);
        assert(limb_pow(a + b) == limb_pow((a + (b - 1)) as nat) * base());
        assert(limb_pow(b) == limb_pow((b - 1) as nat) * base());
        assert(limb_pow(a) * (limb_pow((b - 1) as nat) * base()) == limb_pow(a) * limb_pow(
            (b - 1) as nat,
        ) * base()) by (nonlinear_arith);
    }
}

/// Replacing limb `p` changes the value by the difference at weight
/// `base^p`.
proof fn lemma_value_update(w: Seq<u64>, p: int, v: u64)
    requires
        0 <= p < w.len(),
    ensures
        value(w.update(p, v)) + (w[p] as nat) * limb_pow(p as nat) == value(w) + (v as nat) * limb_pow(
            p as nat,
        ),
    decreases w.len(),
{
    let u = w.update(p, v);
    if p == w.len() - 1 {
        assert(u.drop_last() =~= w.drop_last());
        assert(u.last() == v);
    } else {
        let d = w.drop_last();
        assert(u.drop_last() =~= d.update(p, v));
        assert(u.last() == w.last());
        lemma_value_update(d, p, v);
    }
}

/// `uv = x_j y_i + w + c` stays below `base^2`, so the carry `u` is a
/// limb.
proof fn lemma_digit_product_bound(a: u64, b: u64, c: u64, d: u64)
    ensures
        (a as nat) + (b as nat) * (c as nat) + (d as nat) < base() * base(),
{
    assert((a as nat) + (b as nat) * (c as nat) + (d as nat) < base() * base()) by (nonlinear_arith)
        requires
            a < base(),
            b < base(),
            c < base(),
            d < base(),
    ;
}

/// The arithmetic of one step of a row, over integers.
proof fn lemma_row_arith(
    vw2: int,
    vw: int,
    wij: int,
    v: int,
    u: int,
    xj: int,
    yi: int,
    c: int,
    p: int,
    pi: int,
    pj: int,
    vx: int,
    t0: int,
    vr: int,
)
    requires
        vw2 + wij * p == vw + v * p,
        wij + xj * yi + c == base() as int * u + v,
        p == pi * pj,
        vr == vw2 + u * (p * base() as int) + yi * pi * (vx - (t0 + xj * pj)),
    ensures
        vr == vw + c * p + yi * pi * (vx - t0),
{
    use vstd::arithmetic::mul::*;
    let b = base() as int;
    // vw2 + u p b = vw + p (v + u b - wij) = vw + p (xj yi + c).
    lemma_mul_is_commutative(u, p * b);
    lemma_mul_is_associative(p, b, u);
    lemma_mul_is_distributive_add(p, v, b * u);
    lemma_mul_is_distributive_sub(p, v + b * u, wij);
    lemma_mul_is_distributive_add(p, xj * yi, c);
    lemma_mul_is_commutative(wij, p);
    lemma_mul_is_commutative(v, p);
    assert(u * (p * b) == p * (b * u));
    assert(vw2 + u * (p * b) == vw + p * (xj * yi + c));
    // yi pi (vx - t0 - xj pj) = yi pi (vx - t0) - p xj yi.
    lemma_mul_is_distributive_sub(yi * pi, vx - t0, xj * pj);
    lemma_mul_is_associative(yi * pi, xj, pj);
    lemma_mul_is_associative(yi, pi, xj * pj);
    assert(yi * pi * (xj * pj) == p * (xj * yi)) by (nonlinear_arith)
        requires
            p == pi * pj,
    ;
    assert(yi * pi * (vx - (t0 + xj * pj)) == yi * pi * (vx - t0) - p * (xj * yi)) by (nonlinear_arith)
        requires
            yi * pi * (xj * pj) == p * (xj * yi),
    ;
    assert(p * (xj * yi + c) == p * (xj * yi) + c * p) by (nonlinear_arith);
}

/// One row of Algorithm 14.12 adds `y_i base^i x` to `w` (steps 2.1 to
/// 2.3), provided the position `i + n + 1` it writes last is zero; it
/// touches only positions `i ..= i + n + 1` (here `i .. i + x.len()`).
proof fn lemma_row(w: Seq<u64>, x: Seq<u64>, yi: u64, i: nat, j: nat, c: u64)
    requires
        i + x.len() < w.len(),
        w[(i + x.len()) as int] == 0,
        j <= x.len(),
    ensures
        hac12_row(w, x, yi, i, j, c).len() == w.len(),
        value(hac12_row(w, x, yi, i, j, c)) == value(w) + (c as nat) * limb_pow(i + j) + (yi as nat)
            * limb_pow(i) * (value(x) - value(x.take(j as int))),
        forall|k: int|
            (k < i || k > i + x.len()) && 0 <= k < w.len() ==> #[trigger] hac12_row(w, x, yi, i, j, c)[k]
                == w[k],
    decreases x.len() - j,
{
    let r = hac12_row(w, x, yi, i, j, c);
    if j >= x.len() {
        lemma_value_update(w, (i + x.len()) as int, c);
        assert(x.take(j as int) =~= x);
        assert(value(x) - value(x.take(j as int)) == 0);
        assert((yi as nat) * limb_pow(i) * 0 == 0);
        assert(r == w.update((i + x.len()) as int, c));
        assert forall|k: int|
            (k < i || k > i + x.len()) && 0 <= k < w.len() implies #[trigger] r[k] == w[k] by {
            assert(k != (i + x.len()) as int);
        }
    } else {
        let uv = (w[(i + j) as int] as nat) + (x[j as int] as nat) * (yi as nat) + (c as nat);
        lemma_digit_product_bound(w[(i + j) as int], x[j as int], yi, c);
        let v = (uv % base()) as u64;
        let u = (uv / base()) as u64;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(uv as int, base() as int);
        // u < base: uv < base^2.
        assert(u < base()) by (nonlinear_arith)
            requires
                uv < base() * base(),
                uv == base() * (uv / base()) + uv % base(),
                uv % base() >= 0,
                base() > 0,
        ;
        let w2 = w.update((i + j) as int, v);
        assert(i + j < i + x.len());
        assert(w2[(i + x.len()) as int] == 0);
        assert(w2.len() == w.len());
        lemma_row(w2, x, yi, i, j + 1, u);
        assert forall|k: int|
            (k < i || k > i + x.len()) && 0 <= k < w.len() implies #[trigger] r[k] == w[k] by {
            assert(w2[k] == w[k]);
        }
        lemma_value_update(w, (i + j) as int, v);
        lemma_limb_pow_add(i, j);
        lemma_limb_pow_add(i + j, 1);
        super::lemmas::lemma_value_take_succ(x, j as int);
        // value(w2) + w[i+j] P = value(w) + v P, with P = base^(i+j).
        let p = limb_pow(i + j);
        let xj = x[j as int] as nat;
        // r = row(w2, j + 1, u):
        //   value(r) = value(w2) + u P base + yi base^i (X - take(j + 1)).
        assert(limb_pow(i + j + 1) == p * base());
        assert(limb_pow(i + j) == limb_pow(i) * limb_pow(j));
        // The claim, in the variables of this step.
        let vw = value(w);
        let vx = value(x);
        let t0 = value(x.take(j as int));
        let t1 = t0 + xj * limb_pow(j);
        assert(value(x.take(j as int + 1)) == t1);
        assert(value(r) == value(w2) + (u as nat) * (p * base()) + (yi as nat) * limb_pow(i) * (vx
            - t1));
        lemma_row_arith(
            value(w2) as int,
            vw as int,
            w[(i + j) as int] as int,
            v as int,
            u as int,
            xj as int,
            yi as int,
            c as int,
            p as int,
            limb_pow(i) as int,
            limb_pow(j) as int,
            vx as int,
            t0 as int,
            value(r) as int,
        );
    }
}

/// All rows: `w` holds `x * y.take(i)` and is zero above `i + x.len()`;
/// after the remaining rows it holds `x * y`.
proof fn lemma_rows(w: Seq<u64>, x: Seq<u64>, y: Seq<u64>, i: nat)
    requires
        w.len() == x.len() + y.len(),
        i <= y.len(),
        forall|k: int| i + x.len() <= k < w.len() ==> w[k] == 0,
        value(w) == value(x) * value(y.take(i as int)),
    ensures
        hac12_rows(w, x, y, i).len() == w.len(),
        value(hac12_rows(w, x, y, i)) == value(x) * value(y),
    decreases y.len() - i,
{
    if i >= y.len() {
        assert(y.take(i as int) =~= y);
    } else {
        lemma_row(w, x, y[i as int], i, 0, 0);
        let w1 = hac12_row(w, x, y[i as int], i, 0, 0);
        assert(w[(i + x.len()) as int] == 0);
        assert(x.take(0) =~= Seq::<u64>::empty());
        super::lemmas::lemma_value_empty();
        assert(limb_pow(i + 0) == limb_pow(i));
        super::lemmas::lemma_value_take_succ(y, i as int);
        let yi = y[i as int] as nat;
        // value(w1) = value(x) value(y.take(i)) + yi base^i value(x).
        assert(value(w1) == value(x) * value(y.take(i as int)) + yi * limb_pow(i) * value(x)) by (nonlinear_arith)
            requires
                value(w1) == value(w) + (0nat) * limb_pow(i + 0) + yi * limb_pow(i) * (value(x)
                    - value(Seq::<u64>::empty())),
                value(w) == value(x) * value(y.take(i as int)),
                value(Seq::<u64>::empty()) == 0,
        ;
        assert(value(w1) == value(x) * value(y.take(i as int + 1))) by (nonlinear_arith)
            requires
                value(w1) == value(x) * value(y.take(i as int)) + yi * limb_pow(i) * value(x),
                value(y.take(i as int + 1)) == value(y.take(i as int)) + yi * limb_pow(i),
        ;
        assert forall|k: int| (i + 1) + x.len() <= k < w1.len() implies w1[k] == 0 by {
            assert(k > i + x.len());
            assert(w1[k] == w[k]);
        }
        lemma_rows(w1, x, y, i + 1);
    }
}

/// **Algorithm 14.12 computes the product**: the result has `x.len() +
/// y.len()` digits and its value is `value(x) value(y)`.
pub proof fn lemma_hac_14_12_value(x: Seq<u64>, y: Seq<u64>)
    ensures
        hac_14_12(x, y).len() == x.len() + y.len(),
        value(hac_14_12(x, y)) == value(x) * value(y),
{
    let w0 = Seq::new(x.len() + y.len(), |k: int| 0u64);
    assert(forall|k: int| 0 <= k < w0.len() ==> w0[k] == 0u64);
    super::lemmas::lemma_value_zeros(w0);
    assert(y.take(0) =~= Seq::<u64>::empty());
    super::lemmas::lemma_value_empty();
    assert(value(x) * 0 == 0);
    lemma_rows(w0, x, y, 0);
}

/// The contract's modular product is the remainder of Algorithm 14.12's
/// product.
pub proof fn lemma_mod_mul_is_hac_remainder(a: Seq<u64>, b: Seq<u64>, n: Seq<u64>)
    requires
        value(n) > 0,
    ensures
        (value(a) * value(b)) % value(n) == value(hac_14_12(a, b)) % value(n),
{
    lemma_hac_14_12_value(a, b);
}

} // verus!
