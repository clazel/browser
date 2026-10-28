//! Modular addition, multiplication and exponentiation, proven to meet
//! [`super::contract`].
//!
//! **Which multiplication.** Modular multiplication is double-and-add (the
//! right-to-left binary method, HAC Algorithm 14.79's shape applied to
//! addition instead of multiplication): for each bit of `b`, from the least
//! significant, add the running multiple of `a` into the accumulator if the
//! bit is set, and double the running multiple, every step reduced modulo
//! `n` with one conditional subtraction. It needs only `add`, `sub` and
//! limb loops, works for every modulus (odd or even), and its proof is a
//! chain of congruences. It is slower than Montgomery multiplication
//! (quadratic in the number of bits per multiplication, with a larger
//! constant), which is acceptable because one certificate check is one
//! exponentiation with `e = 65537`, 17 multiplications.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::arith::{add, sub};

verus! {

/// `(a + b) mod n` for `a, b < n`.
pub fn mod_add(a: &[u64], b: &[u64], n: &[u64]) -> (r: Vec<u64>)
    requires
        super::contract::mod_add_requires(a@, b@, n@),
    ensures
        super::contract::mod_add_ensures(a@, b@, n@, r@),
{
    let (t, c) = add(a, b);
    let (d, bw) = sub(t.as_slice(), n);
    proof {
        super::lemmas::lemma_value_bound(n@);
        super::lemmas::lemma_value_bound(t@);
        super::lemmas::lemma_value_bound(d@);
        let r = limb_pow(n@.len());
        let vn = value(n@);
        let s = value(a@) + value(b@);
        // value(t) + c r = s and value(d) + vn = value(t) + bw r.
        if c {
            // s >= r > vn, so value(t) = s - r < vn: the borrow is set and
            // value(d) = s - vn, which is in [0, vn).
            assert(s - vn < vn);
        } else if bw {
            // value(t) < vn, so s = value(t) is already reduced.
            assert(value(t@) < vn);
        } else {
            // value(t) >= vn and s = value(t) < 2 vn: value(d) = s - vn.
            assert(value(d@) < vn);
        }
        if c || !bw {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
                s as int,
                vn as int,
                1,
                value(d@) as int,
            );
        } else {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
                s as int,
                vn as int,
                0,
                value(t@) as int,
            );
        }
    }
    if c || !bw {
        d
    } else {
        t
    }
}

/// Congruence step: if `x = (A X) mod N` and `y = (A Y) mod N` then
/// `(x + y) mod N = (A (X + Y)) mod N`.
proof fn lemma_sum_mod(a: nat, xx: nat, yy: nat, n: nat, x: nat, y: nat)
    requires
        n > 0,
        x == (a * xx) % n,
        y == (a * yy) % n,
    ensures
        (x + y) % n == (a * (xx + yy)) % n,
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop((a * xx) as int, (a * yy) as int, n as int);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(a as int, xx as int, yy as int);
}

/// One bit of `mod_mul`'s inner loop: the new accumulator and running
/// multiple, in terms of the old.
proof fn lemma_bit_step(
    a: nat,
    n: nat,
    v: nat,
    q: nat,
    p: nat,
    pj: nat,
    bit: nat,
    acc: nat,
    cur: nat,
    acc2: nat,
    cur2: nat,
)
    requires
        n > 0,
        bit <= 1,
        acc == (a * (v + q * p)) % n,
        cur == (a * (p * pj)) % n,
        bit == 0 ==> acc2 == acc,
        bit == 1 ==> acc2 == (acc + cur) % n,
        cur2 == (cur + cur) % n,
    ensures
        acc2 == (a * (v + (q + bit * pj) * p)) % n,
        cur2 == (a * (p * (2 * pj))) % n,
{
    if bit == 1 {
        lemma_sum_mod(a, v + q * p, p * pj, n, acc, cur);
        assert(v + q * p + p * pj == v + (q + pj) * p) by (nonlinear_arith);
    } else {
        assert(bit * pj * p == 0) by (nonlinear_arith)
            requires
                bit == 0,
        ;
    }
    lemma_sum_mod(a, p * pj, p * pj, n, cur, cur);
    assert(p * pj + p * pj == p * (2 * pj)) by (nonlinear_arith);
}

/// `(a * b) mod n`, with `a < n`.
pub fn mod_mul(a: &[u64], b: &[u64], n: &[u64]) -> (r: Vec<u64>)
    requires
        super::contract::mod_mul_requires(a@, b@, n@),
    ensures
        super::contract::mod_mul_ensures(a@, b@, n@, r@),
{
    let len = n.len();
    let ghost av = value(a@);
    let ghost nv = value(n@);
    let mut acc: Vec<u64> = vec![0u64;len];
    let mut cur: Vec<u64> = vstd::slice::slice_to_vec(a);
    proof {
        assert(forall|k: int| 0 <= k < acc@.len() ==> acc@[k] == 0u64);
        super::lemmas::lemma_value_zeros(acc@);
        vstd::arithmetic::div_mod::lemma_small_mod(av, nv);
        vstd::arithmetic::mul::lemma_mul_basics(av as int);
        assert(b@.take(0) =~= Seq::<u64>::empty());
        super::lemmas::lemma_value_empty();
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::div_mod::lemma_small_mod(0, nv);
    }
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b.len(),
            acc.len() == len,
            cur.len() == len,
            len == n.len(),
            av == value(a@),
            nv == value(n@),
            nv > 0,
            value(acc@) == (av * value(b@.take(i as int))) % nv,
            value(cur@) == (av * limb_pow(i as nat)) % nv,
        decreases b.len() - i,
    {
        let w0 = b.get(i).cloned().unwrap_or(0);
        let mut w = w0;
        let mut j: u32 = 0;
        let ghost mut q: nat = 0;
        let ghost pre = value(b@.take(i as int));
        let ghost p = limb_pow(i as nat);
        proof {
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::mul::lemma_mul_basics(av as int);
            vstd::arithmetic::mul::lemma_mul_basics(p as int);
            vstd::arithmetic::mul::lemma_mul_basics(pre as int);
        }
        while j < 64
            invariant
                j <= 64,
                i < b.len(),
                acc.len() == len,
                cur.len() == len,
                len == n.len(),
                nv == value(n@),
                nv > 0,
                av == value(a@),
                w0 == b@[i as int],
                w0 == q + vstd::arithmetic::power2::pow2(j as nat) * w,
                q < vstd::arithmetic::power2::pow2(j as nat),
                p == limb_pow(i as nat),
                pre == value(b@.take(i as int)),
                value(acc@) == (av * (pre + q * p)) % nv,
                value(cur@) == (av * (p * vstd::arithmetic::power2::pow2(j as nat))) % nv,
            decreases 64 - j,
        {
            let bit = w % 2;
            let ghost acc_before = acc@;
            let ghost cur_before = cur@;
            if bit == 1 {
                acc = mod_add(acc.as_slice(), cur.as_slice(), n);
            }
            cur = mod_add(cur.as_slice(), cur.as_slice(), n);
            proof {
                let pj = vstd::arithmetic::power2::pow2(j as nat);
                vstd::arithmetic::power2::lemma_pow2_unfold(j as nat + 1);
                vstd::arithmetic::power2::lemma_pow2_pos(j as nat);
                lemma_bit_step(
                    av,
                    nv,
                    pre,
                    q,
                    p,
                    pj,
                    bit as nat,
                    value(acc_before),
                    value(cur_before),
                    value(acc@),
                    value(cur@),
                );
                // w = 2 (w / 2) + bit, so w0 = (q + bit pj) + 2 pj (w / 2).
                let w2 = w / 2;
                assert(w == 2 * w2 + bit);
                assert(w0 == (q + (bit as nat) * pj) + (2 * pj) * w2) by (nonlinear_arith)
                    requires
                        w0 == q + pj * w,
                        w == 2 * w2 + bit,
                ;
                assert((bit as nat) * pj <= pj) by (nonlinear_arith)
                    requires
                        bit <= 1,
                ;
                q = q + (bit as nat) * pj;
            }
            w /= 2;
            // Never overflows: j < 64.
            j = j.saturating_add(1);
        }
        proof {
            // w0 < 2^64 and w0 = q + 2^64 w, so w = 0 and q = w0.
            vstd::arithmetic::power2::lemma2_to64();
            assert(vstd::arithmetic::power2::pow2(64) == base());
            assert(w == 0) by (nonlinear_arith)
                requires
                    w0 == q + base() * w,
                    w0 < base(),
                    q >= 0,
            ;
            assert(q == w0);
            super::lemmas::lemma_value_take_succ(b@, i as int);
            // acc: A (pre + w0 p) = A value(take(i + 1)).
            assert(pre + q * p == value(b@.take(i as int + 1)));
            super::lemmas::lemma_limb_pow_succ(i as nat);
            assert(p * base() == limb_pow(i as nat + 1));
        }
        i = i.saturating_add(1);
    }
    proof {
        super::lemmas::lemma_take_all(b@);
    }
    acc
}

/// The limbs of 1, in `len > 0` limbs.
fn one(len: usize) -> (r: Vec<u64>)
    requires
        len > 0,
    ensures
        r.len() == len,
        value(r@) == 1,
{
    let mut v: Vec<u64> = Vec::new();
    v.push(1);
    proof {
        super::lemmas::lemma_value_push(Seq::<u64>::empty(), 1u64);
        super::lemmas::lemma_value_empty();
        assert(limb_pow(0) == 1);
    }
    while v.len() < len
        invariant
            1 <= v.len() <= len,
            value(v@) == 1,
        decreases len - v.len(),
    {
        proof {
            super::lemmas::lemma_value_push(v@, 0u64);
        }
        v.push(0);
    }
    v
}

/// One step of `mod_exp`'s invariant: with `ec = 2m + bit`, squaring the
/// base and multiplying the result by the base if `bit` is set keeps
/// `s^e = r b^ec` (modulo `n`).
proof fn lemma_exp_step(m_val: int, n: int, r: int, bv: int, ec: nat, r2: int, bv2: int)
    requires
        n > 0,
        0 <= r < n,
        ec % 2 == 1 ==> r2 == (r * bv) % n,
        ec % 2 == 0 ==> r2 == r,
        bv2 == (bv * bv) % n,
        m_val == (r * vstd::arithmetic::power::pow(bv, ec)) % n,
    ensures
        m_val == (r2 * vstd::arithmetic::power::pow(bv2, ec / 2)) % n,
{
    use vstd::arithmetic::div_mod::*;
    use vstd::arithmetic::mul::*;
    use vstd::arithmetic::power::*;
    let m = (ec / 2) as nat;
    let bit = (ec % 2) as nat;
    // ec = 2 m + bit, so b^ec = (b b)^m b^bit.
    lemma_pow_adds(bv, 2 * m, bit);
    lemma_pow_multiplies(bv, 2, m);
    lemma_square_is_pow2(bv);
    let q = pow(bv * bv, m);
    let x = if bit == 1 {
        r * bv
    } else {
        r
    };
    if bit == 1 {
        lemma_pow1(bv);
    } else {
        lemma_pow0(bv);
    }
    // b^ec = b^bit q, so r b^ec = x q.
    assert(ec == 2 * m + bit);
    assert(pow(bv, 2) == bv * bv);
    assert(pow(pow(bv, 2), m) == q);
    assert(pow(bv, 2 * m) == q);
    assert(pow(bv, ec) == pow(bv, 2 * m) * pow(bv, bit));
    assert(pow(bv, ec) == pow(bv, bit) * q) by (nonlinear_arith)
        requires
            pow(bv, ec) == pow(bv, 2 * m) * pow(bv, bit),
            pow(bv, 2 * m) == q,
    ;
    lemma_mul_is_associative(r, pow(bv, bit), q);
    assert(r * pow(bv, ec) == x * q);
    // r2 = x mod n.
    if bit == 0 {
        lemma_small_mod(r as nat, n as nat);
    }
    assert(r2 == x % n);
    // (x q) mod n = (x mod n)(q mod n) mod n, and q mod n = (bv2)^m mod n.
    lemma_mul_mod_noop(x, q, n);
    lemma_pow_mod_noop(bv * bv, m, n);
    lemma_mul_mod_noop(r2, pow(bv2, m), n);
    lemma_mod_twice(r2, n);
    lemma_mod_twice(x, n);
    assert(r2 % n == r2) by {
        lemma_small_mod(r2 as nat, n as nat);
    }
}

/// `s^e mod n`, for `s < n` and `n > 1`: right-to-left binary
/// exponentiation (HAC Algorithm 14.79's right-to-left variant), over
/// `mod_mul`.
pub fn mod_exp(s: &[u64], e: u64, n: &[u64]) -> (r: Vec<u64>)
    requires
        super::contract::mod_exp_requires(s@, n@),
    ensures
        super::contract::mod_exp_ensures(s@, e, n@, r@),
{
    let len = n.len();
    proof {
        // n > 1 as a number, so it has at least one limb.
        super::lemmas::lemma_value_empty();
    }
    let ghost sv = value(s@);
    let ghost nv = value(n@);
    let mut result = one(len);
    let mut base = vstd::slice::slice_to_vec(s);
    let mut ec = e;
    proof {
        vstd::arithmetic::mul::lemma_mul_basics(vstd::arithmetic::power::pow(sv as int, e as nat));
        vstd::arithmetic::div_mod::lemma_small_mod(1, nv);
    }
    while ec != 0
        invariant
            result.len() == len,
            base.len() == len,
            len == n.len(),
            nv == value(n@),
            nv > 1,
            value(result@) < nv,
            value(base@) < nv,
            crate::spec::modpow(sv, e as nat, nv) == (value(result@) * vstd::arithmetic::power::pow(
                value(base@) as int,
                ec as nat,
            )) % (nv as int),
        decreases ec,
    {
        let ghost r_old = value(result@);
        let ghost b_old = value(base@);
        if ec % 2 == 1 {
            result = mod_mul(result.as_slice(), base.as_slice(), n);
        }
        base = mod_mul(base.as_slice(), base.as_slice(), n);
        proof {
            let r2 = value(result@) as int;
            let bv2 = value(base@) as int;
            lemma_exp_step(
                crate::spec::modpow(sv, e as nat, nv) as int,
                nv as int,
                r_old as int,
                b_old as int,
                ec as nat,
                r2,
                bv2,
            );
            vstd::arithmetic::div_mod::lemma_mod_bound(value(result@) as int, nv as int);
        }
        ec /= 2;
    }
    proof {
        vstd::arithmetic::power::lemma_pow0(value(base@) as int);
        vstd::arithmetic::mul::lemma_mul_basics(value(result@) as int);
        vstd::arithmetic::div_mod::lemma_small_mod(value(result@), nv);
    }
    result
}

} // verus!
