//! P-384's p is prime, proven here rather than cited.
//!
//! SP 800-186 §3.2.1.4 states that p is prime. The equivalence of
//! `independent.rs` and `spec.rs` ([`crate::equivalence`]) needs that fact,
//! as Euclid's lemma for p ([`crate::equivalence::euclid`]): the two texts
//! read SEC 1 §2.2.1 rule 3 differently, and the readings agree on the curve
//! only over a prime field. A cited fact would be an axiom, so this module
//! proves it instead.
//!
//! The proof is a chain of Pocklington certificates (H. C. Pocklington,
//! "The determination of the prime or composite nature of large numbers by
//! Fermat's theorem", Proc. Cambridge Philos. Soc. 18 (1914), pp. 29-30), in
//! the form of Brillhart, Lehmer and Selfridge, Math. Comp. 29 (1975),
//! Theorem 4 restricted to `F^2 > N`: if `F` divides `N - 1`, `F^2 > N`, and
//! some `a` has `a^(N-1) ≡ 1 (mod N)` and `gcd(a^((N-1)/q) - 1, N) = 1` for
//! every prime `q` dividing `F`, then `N` is prime. The theorem is proven
//! below ([`lemma_pocklington`]), not cited. Each certificate gives `N`, `a`
//! and the prime factors of `F`, and the numeric conditions are evaluated
//! with `by (compute_only)`. The primes of each `F` have certificates of
//! their own, down to primes below 2^20, which trial division proves
//! ([`lemma_trial`]).
//!
//! The certificates were found outside the repository: `N - 1` factored by
//! trial division, Pollard's rho and Lenstra's elliptic curve method, and
//! the largest prime factors taken until `F^2 > N`. Nothing here depends on
//! how they were found; Verus checks each one.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Primes, gcd and Euclid's lemma.
// ---------------------------------------------------------------------

/// `n` is prime: greater than 1, and no `k` with `1 < k < n` divides it.
pub open spec fn is_prime(n: nat) -> bool {
    n > 1 && forall|k: nat| 1 < k < n ==> #[trigger] (n % k) != 0
}

/// The extended Euclidean algorithm: `(g, x, y)` with `a x + b y = g`, and
/// `g` dividing `a` and `b` ([`lemma_egcd`]).
pub open spec fn egcd(a: nat, b: nat) -> (nat, int, int)
    decreases b,
{
    if b == 0 {
        (a, 1, 0)
    } else {
        let t = egcd(b, a % b);
        (t.0, t.2, t.1 - (a / b) as int * t.2)
    }
}

/// Bézout's identity for [`egcd`], and that its `g` divides both.
pub proof fn lemma_egcd(a: nat, b: nat)
    ensures
        a * egcd(a, b).1 + b * egcd(a, b).2 == egcd(a, b).0,
        a > 0 || b > 0 ==> egcd(a, b).0 > 0,
        egcd(a, b).0 > 0 ==> a % egcd(a, b).0 == 0 && b % egcd(a, b).0 == 0,
    decreases b,
{
    if b == 0 {
        if a > 0 {
            vstd::arithmetic::div_mod::lemma_mod_self_0(a as int);
            vstd::arithmetic::div_mod::lemma_small_mod(0, a);
        }
    } else {
        lemma_egcd(b, a % b);
        let t = egcd(b, a % b);
        let g = t.0;
        let x1 = t.1;
        let y1 = t.2;
        let q = (a / b) as int;
        let rr = (a % b) as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, b as int);
        assert(a == b * q + rr);
        assert((b * q + rr) * y1 == b * (q * y1) + rr * y1) by (nonlinear_arith);
        assert(b * (x1 - q * y1) == b * x1 - b * (q * y1)) by (nonlinear_arith);
        if g > 0 {
            let gi = g as int;
            crate::equivalence::lemma_cong_zero_mul(gi, b as int, q);
            crate::equivalence::lemma_cong_add(gi, b * q, 0, rr, 0);
            vstd::arithmetic::div_mod::lemma_small_mod(0, g);
        }
    }
}

/// A positive multiple of `g` is at least `g`.
pub proof fn lemma_divisor_le(x: nat, g: nat)
    requires
        x > 0,
        g > 0,
        x % g == 0,
    ensures
        g <= x,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, g as int);
    let k = x / g;
    assert(g <= x) by (nonlinear_arith)
        requires
            x == g * k,
            x > 0,
            g > 0,
            k >= 0,
    ;
}

/// For a prime `p`: if `p` divides `u v` and not `u`, it divides `v`.
pub proof fn lemma_prime_cancel(p: nat, u: int, v: int)
    requires
        is_prime(p),
        (u * v) % (p as int) == 0,
        u % (p as int) != 0,
    ensures
        v % (p as int) == 0,
{
    let pi = p as int;
    crate::equivalence::lemma_cong_mod(pi, u);
    let uu = (u % pi) as nat;
    lemma_egcd(p, uu);
    let g = egcd(p, uu).0;
    let x = egcd(p, uu).1;
    let y = egcd(p, uu).2;
    lemma_divisor_le(uu, g);
    if g > 1 {
        assert(p % g != 0);
    }
    assert(g == 1);
    // uu y ≡ 1 (mod p).
    vstd::arithmetic::div_mod::lemma_mod_self_0(pi);
    crate::equivalence::lemma_cong_zero_mul(pi, pi, x);
    assert(uu * y == 1 - p * x);
    crate::equivalence::lemma_cong_add(pi, 1, 1, p * x, 0);
    assert(crate::equivalence::cong(pi, uu * y, 1));
    // v ≡ (uu y) v = y (uu v) ≡ y (u v) ≡ 0.
    crate::equivalence::lemma_cong_mul(pi, uu * y, 1, v, v);
    crate::equivalence::lemma_assoc_swap(v, y, uu as int);
    crate::equivalence::lemma_cong_mul(pi, uu as int, u, v, v);
    vstd::arithmetic::div_mod::lemma_small_mod(0, p);
    crate::equivalence::lemma_cong_zero_mul(pi, uu * v, y);
}

/// Euclid's lemma holds for a prime.
pub proof fn lemma_prime_euclid(p: nat)
    requires
        is_prime(p),
    ensures
        crate::equivalence::euclid(p),
{
    let pi = p as int;
    assert forall|u: int, v: int| #[trigger] ((u * v) % pi) == 0 implies u % pi == 0 || v % pi
        == 0 by {
        if u % pi != 0 {
            lemma_prime_cancel(p, u, v);
        }
    }
}

/// A number with a divisor strictly between 1 and itself has one whose
/// square is at most the number.
pub proof fn lemma_small_divisor(n: nat, k: nat)
    requires
        1 < k < n,
        n % k == 0,
    ensures
        ({
            let r = if k * k <= n {
                k
            } else {
                n / k
            };
            1 < r && r * r <= n && n % r == 0
        }),
{
    if k * k > n {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, k as int);
        let r = n / k;
        assert(n == k * r);
        assert(r > 1) by (nonlinear_arith)
            requires
                n == k * r,
                k < n,
        ;
        assert(r * r <= n) by (nonlinear_arith)
            requires
                n == k * r,
                k * k > n,
                r > 1,
        ;
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(k as int, r as int);
        assert(k * r == r * k) by (nonlinear_arith);
    }
}

// ---------------------------------------------------------------------
// Trial division.
// ---------------------------------------------------------------------

/// No `j` with `k <= j` and `j^2 <= n` divides `n`.
pub open spec fn trial(n: nat, k: nat) -> bool
    decreases n - k,
{
    if k >= n || k * k > n {
        true
    } else if n % k == 0 {
        false
    } else {
        trial(n, k + 1)
    }
}

/// Trial division from `j` finds every divisor `r >= j` with `r^2 <= n`.
proof fn lemma_trial_finds(n: nat, j: nat, r: nat)
    requires
        trial(n, j),
        2 <= j <= r,
        r * r <= n,
        1 < r < n,
    ensures
        n % r != 0,
    decreases r - j,
{
    assert(j * j <= r * r) by (nonlinear_arith)
        requires
            2 <= j <= r,
    ;
    if j < r {
        lemma_trial_finds(n, j + 1, r);
    }
}

/// Trial division up to the square root proves a number prime.
pub proof fn lemma_trial(n: nat)
    requires
        n > 1,
        trial(n, 2),
    ensures
        is_prime(n),
{
    assert forall|k: nat| 1 < k < n implies #[trigger] (n % k) != 0 by {
        if n % k == 0 {
            lemma_small_divisor(n, k);
            let r = if k * k <= n {
                k
            } else {
                n / k
            };
            assert(r < n) by (nonlinear_arith)
                requires
                    1 < r,
                    r * r <= n,
            ;
            lemma_trial_finds(n, 2, r);
        }
    }
}

// ---------------------------------------------------------------------
// Powers modulo a divisor, and the multiplicative order.
// ---------------------------------------------------------------------

/// `pow_mod` modulo `n`, reduced again modulo a divisor `r` of `n`, is the
/// power modulo `r`.
pub proof fn lemma_pow_mod_divisor(a: nat, e: nat, n: nat, r: nat)
    requires
        n > 0,
        r > 0,
        n % r == 0,
    ensures
        pow_mod(a, e, n) % r == vstd::arithmetic::power::pow(a as int, e) % (r as int),
{
    crate::equivalence::lemma_pow_mod_is_power(a, e, n);
    crate::equivalence::lemma_power_is_pow(a, e);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, r as int);
    let k = n / r;
    assert(k > 0) by (nonlinear_arith)
        requires
            n == r * k,
            n > 0,
            r > 0,
            k >= 0,
    ;
    vstd::arithmetic::div_mod::lemma_mod_mod(
        vstd::arithmetic::power::pow(a as int, e),
        r as int,
        k as int,
    );
}

/// The least `i` in `[lo, hi)` with `a^i ≡ 1 (mod r)`, or `hi`.
pub open spec fn first_one(a: nat, r: nat, lo: nat, hi: nat) -> nat
    decreases hi - lo,
{
    if lo >= hi {
        hi
    } else if vstd::arithmetic::power::pow(a as int, lo) % (r as int) == 1 {
        lo
    } else {
        first_one(a, r, lo + 1, hi)
    }
}

/// [`first_one`] is the least exponent in `[lo, hi]` with power 1, given
/// that `hi` has one.
proof fn lemma_first_one(a: nat, r: nat, lo: nat, hi: nat)
    requires
        lo <= hi,
        vstd::arithmetic::power::pow(a as int, hi) % (r as int) == 1,
    ensures
        lo <= first_one(a, r, lo, hi) <= hi,
        vstd::arithmetic::power::pow(a as int, first_one(a, r, lo, hi)) % (r as int) == 1,
        forall|i: nat|
            lo <= i < first_one(a, r, lo, hi) ==> #[trigger] vstd::arithmetic::power::pow(
                a as int,
                i,
            ) % (r as int) != 1,
    decreases hi - lo,
{
    if lo < hi && vstd::arithmetic::power::pow(a as int, lo) % (r as int) != 1 {
        lemma_first_one(a, r, lo + 1, hi);
    }
}

/// `a^d ≡ 1` gives `a^(d t) ≡ 1`.
proof fn lemma_pow_one_mul(a: nat, r: nat, d: nat, t: nat)
    requires
        r > 1,
        vstd::arithmetic::power::pow(a as int, d) % (r as int) == 1,
    ensures
        vstd::arithmetic::power::pow(a as int, d * t) % (r as int) == 1,
{
    let ad = vstd::arithmetic::power::pow(a as int, d);
    vstd::arithmetic::power::lemma_pow_multiplies(a as int, d, t);
    vstd::arithmetic::power::lemma_pow_mod_noop(ad, t, r as int);
    vstd::arithmetic::power::lemma1_pow(t);
    vstd::arithmetic::div_mod::lemma_small_mod(1, r);
}

/// The facts about `a` modulo `r` that Pocklington's proof uses: `a^(n-1)
/// ≡ 1`, and `d` is the order of `a` (the least positive exponent with
/// power 1).
pub open spec fn order_facts(a: nat, r: nat, n: nat, d: nat) -> bool {
    r > 1 && n > 2 && vstd::arithmetic::power::pow(a as int, (n - 1) as nat) % (r as int) == 1
        && 1 <= d <= n - 1 && vstd::arithmetic::power::pow(a as int, d) % (r as int) == 1
        && forall|i: nat|
        1 <= i < d ==> #[trigger] vstd::arithmetic::power::pow(a as int, i) % (r as int) != 1
}

/// `a^i` has an inverse modulo `r`: `a^i (a^(n-2))^i ≡ 1`.
proof fn lemma_pow_inverse(a: nat, r: nat, n: nat, d: nat, i: nat)
    requires
        order_facts(a, r, n, d),
    ensures
        crate::equivalence::cong(
            r as int,
            vstd::arithmetic::power::pow(a as int, i) * vstd::arithmetic::power::pow(
                vstd::arithmetic::power::pow(a as int, (n - 2) as nat),
                i,
            ),
            1,
        ),
{
    let ai = vstd::arithmetic::power::pow(a as int, (n - 2) as nat);
    vstd::arithmetic::power::lemma_pow_adds(a as int, 1, (n - 2) as nat);
    vstd::arithmetic::power::lemma_pow1(a as int);
    assert(a * ai == vstd::arithmetic::power::pow(a as int, (n - 1) as nat));
    vstd::arithmetic::power::lemma_pow_distributes(a as int, ai, i);
    vstd::arithmetic::power::lemma_pow_mod_noop(a * ai, i, r as int);
    vstd::arithmetic::power::lemma1_pow(i);
    vstd::arithmetic::div_mod::lemma_small_mod(1, r);
}

/// The order divides `n - 1`.
proof fn lemma_order_divides(a: nat, r: nat, n: nat, d: nat)
    requires
        order_facts(a, r, n, d),
    ensures
        ((n - 1) as nat) % d == 0,
{
    let nm1 = (n - 1) as nat;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(nm1 as int, d as int);
    let t = nm1 / d;
    let m = nm1 % d;
    assert(nm1 == d * t + m);
    vstd::arithmetic::power::lemma_pow_adds(a as int, d * t, m);
    lemma_pow_one_mul(a, r, d, t);
    let ri = r as int;
    vstd::arithmetic::div_mod::lemma_small_mod(1, r);
    crate::equivalence::lemma_cong_mul(
        ri,
        vstd::arithmetic::power::pow(a as int, d * t),
        1,
        vstd::arithmetic::power::pow(a as int, m),
        vstd::arithmetic::power::pow(a as int, m),
    );
    vstd::arithmetic::div_mod::lemma_small_mod(1, r);
    assert(vstd::arithmetic::power::pow(a as int, m) % ri == 1);
    if m >= 1 {
        assert(vstd::arithmetic::power::pow(a as int, m) % ri != 1);
    }
}

/// The order is at most `r - 1`: the powers `a^0, ..., a^(d-1)` are
/// distinct modulo `r` and none is 0, so there are at most `r - 1` of them.
proof fn lemma_order_bound(a: nat, r: nat, n: nat, d: nat)
    requires
        order_facts(a, r, n, d),
    ensures
        d <= r - 1,
{
    let ri = r as int;
    let ai = vstd::arithmetic::power::pow(a as int, (n - 2) as nat);
    let f = |i: int| vstd::arithmetic::power::pow(a as int, i as nat) % ri;
    let x = vstd::set_lib::set_int_range(0, d as int);
    let y = x.map(f);
    let z = vstd::set_lib::set_int_range(1, ri);
    vstd::set_lib::lemma_int_range(0, d as int);
    vstd::set_lib::lemma_int_range(1, ri);
    vstd::arithmetic::div_mod::lemma_small_mod(1, r);
    vstd::arithmetic::div_mod::lemma_small_mod(0, r);
    // Distinct.
    assert forall|i: int, j: int| x.contains(i) && x.contains(j) && #[trigger] f(i) == #[trigger] f(
        j,
    ) implies i == j by {
        if i != j {
            let (lo, hi) = if i < j {
                (i as nat, j as nat)
            } else {
                (j as nat, i as nat)
            };
            let plo = vstd::arithmetic::power::pow(a as int, lo);
            let phi = vstd::arithmetic::power::pow(a as int, hi);
            let pdiff = vstd::arithmetic::power::pow(a as int, (hi - lo) as nat);
            let inv = vstd::arithmetic::power::pow(ai, lo);
            lemma_pow_inverse(a, r, n, d, lo);
            vstd::arithmetic::power::lemma_pow_adds(a as int, lo, (hi - lo) as nat);
            assert(phi == plo * pdiff);
            // pdiff ≡ (plo inv) pdiff = inv phi ≡ inv plo ≡ 1.
            crate::equivalence::lemma_cong_mul(ri, plo * inv, 1, pdiff, pdiff);
            assert((plo * inv) * pdiff == inv * (plo * pdiff)) by (nonlinear_arith);
            crate::equivalence::lemma_cong_mul(ri, inv, inv, phi, plo);
            assert(inv * plo == plo * inv) by (nonlinear_arith);
            assert(pdiff % ri == 1);
            assert(pdiff % ri != 1);
        }
    }
    assert(x.injective_on(f));
    vstd::set_lib::lemma_map_size(x, y, f);
    // In [1, r).
    assert forall|v: int| y.contains(v) implies z.contains(v) by {
        broadcast use vstd::set::Set::lemma_map_contains;
        let i = choose|i: int| x.contains(i) && f(i) == v;
        let pi = vstd::arithmetic::power::pow(a as int, i as nat);
        lemma_pow_inverse(a, r, n, d, i as nat);
        crate::equivalence::lemma_cong_mod(ri, pi);
        if v == 0 {
            crate::equivalence::lemma_cong_zero_mul(
                ri,
                pi,
                vstd::arithmetic::power::pow(ai, i as nat),
            );
        }
    }
    vstd::set_lib::lemma_len_subset(y, z);
}

// ---------------------------------------------------------------------
// Pocklington's criterion.
// ---------------------------------------------------------------------

/// `q^e`.
pub open spec fn pw(q: nat, e: nat) -> nat
    decreases e,
{
    if e == 0 {
        1
    } else {
        q * pw(q, (e - 1) as nat)
    }
}

/// `F`, the product of the prime powers `q^e` listed.
pub open spec fn prod(fs: Seq<(nat, nat)>) -> nat
    decreases fs.len(),
{
    if fs.len() == 0 {
        1
    } else {
        prod(fs.drop_last()) * pw(fs.last().0, fs.last().1)
    }
}

/// The conditions on one prime power `q^e` of `F`, given the product
/// `prefix` of those before it: `q^e` divides `N - 1`; `gcd(a^((N-1)/q) - 1,
/// N) = 1`, with `a^((N-1)/q) - 1` taken modulo `N`; and `q^e` is coprime to
/// `prefix`. That `q` is prime is a separate requirement.
pub open spec fn factor_ok(n: nat, a: nat, prefix: nat, q: nat, e: nat) -> bool {
    q > 1 && e >= 1 && ((n - 1) as nat) % pw(q, e) == 0 && ((n - 1) as nat) % q == 0 && egcd(
        n,
        ((pow_mod(a, ((n - 1) as nat / q) as nat, n) + n - 1) % (n as int)) as nat,
    ).0 == 1 && egcd(prefix, pw(q, e)).0 == 1
}

/// [`factor_ok`] for every prime power listed.
pub open spec fn factors_ok(n: nat, a: nat, fs: Seq<(nat, nat)>) -> bool
    decreases fs.len(),
{
    fs.len() == 0 || (factors_ok(n, a, fs.drop_last()) && factor_ok(
        n,
        a,
        prod(fs.drop_last()),
        fs.last().0,
        fs.last().1,
    ))
}

/// The numeric conditions of Pocklington's criterion, each evaluable.
pub open spec fn pocklington(n: nat, a: nat, fs: Seq<(nat, nat)>) -> bool {
    n > 2 && pow_mod(a, (n - 1) as nat, n) == 1 && prod(fs) * prod(fs) > n && factors_ok(n, a, fs)
}

/// Every `q` listed is prime.
pub open spec fn all_prime(fs: Seq<(nat, nat)>) -> bool {
    forall|i: int| 0 <= i < fs.len() ==> is_prime(#[trigger] fs[i].0)
}

/// `q^e` is positive for `q > 0`.
proof fn lemma_pw_pos(q: nat, e: nat)
    requires
        q > 0,
    ensures
        pw(q, e) > 0,
    decreases e,
{
    if e > 0 {
        lemma_pw_pos(q, (e - 1) as nat);
        assert(q * pw(q, (e - 1) as nat) > 0) by (nonlinear_arith)
            requires
                q > 0,
                pw(q, (e - 1) as nat) > 0,
        ;
    }
}

/// `F` is positive.
proof fn lemma_prod_pos(n: nat, a: nat, fs: Seq<(nat, nat)>)
    requires
        factors_ok(n, a, fs),
    ensures
        prod(fs) > 0,
    decreases fs.len(),
{
    if fs.len() > 0 {
        lemma_prod_pos(n, a, fs.drop_last());
        lemma_pw_pos(fs.last().0, fs.last().1);
        let x = prod(fs.drop_last());
        let y = pw(fs.last().0, fs.last().1);
        assert(x * y > 0) by (nonlinear_arith)
            requires
                x > 0,
                y > 0,
        ;
    }
}

/// `z % m == 0` as `z = m k`.
proof fn lemma_divides_elim(z: int, m: int)
    requires
        m > 0,
        z % m == 0,
    ensures
        z == m * (z / m),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(z, m);
}

/// `m k` is a multiple of `m`.
proof fn lemma_divides_intro(m: int, k: int)
    requires
        m > 0,
    ensures
        (m * k) % m == 0,
{
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(k, m);
    assert(k * m == m * k) by (nonlinear_arith);
}

/// For a prime `q` not dividing `t`: if `q^e` divides `x t`, it divides `x`.
proof fn lemma_prime_power_cancel(q: nat, e: nat, x: nat, t: nat)
    requires
        is_prime(q),
        t % q != 0,
        (x * t) % pw(q, e) == 0,
    ensures
        x % pw(q, e) == 0,
    decreases e,
{
    if e == 0 {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x as int, 1, x as int, 0);
    } else {
        let pp = pw(q, (e - 1) as nat);
        lemma_pw_pos(q, (e - 1) as nat);
        let qi = q as int;
        // q divides x t, hence x.
        vstd::arithmetic::div_mod::lemma_mod_mod((x * t) as int, qi, pp as int);
        vstd::arithmetic::div_mod::lemma_small_mod(0, q);
        assert(t * x == x * t) by (nonlinear_arith);
        lemma_prime_cancel(q, t as int, x as int);
        lemma_divides_elim(x as int, qi);
        let x1 = (x / q) as nat;
        // q^(e-1) divides x1 t.
        lemma_divides_elim((x * t) as int, (q * pp) as int);
        let k = (x * t) / (q * pp);
        assert(q * (x1 * t) == q * (pp * k)) by (nonlinear_arith)
            requires
                x == q * x1,
                x * t == (q * pp) * k,
        ;
        assert(x1 * t == pp * k) by (nonlinear_arith)
            requires
                q * (x1 * t) == q * (pp * k),
                q > 1,
        ;
        lemma_divides_intro(pp as int, k as int);
        lemma_prime_power_cancel(q, (e - 1) as nat, x1, t);
        lemma_divides_elim(x1 as int, pp as int);
        let m = x1 / pp;
        assert(x == (q * pp) * m) by (nonlinear_arith)
            requires
                x == q * x1,
                x1 == pp * m,
        ;
        lemma_divides_intro((q * pp) as int, m as int);
    }
}

/// If coprime `A` and `B` both divide `d`, so does `A B`.
proof fn lemma_coprime_mul(aa: nat, bb: nat, d: nat)
    requires
        aa > 0,
        bb > 0,
        d % aa == 0,
        d % bb == 0,
        egcd(aa, bb).0 == 1,
    ensures
        d % (aa * bb) == 0,
{
    lemma_egcd(aa, bb);
    let x = egcd(aa, bb).1;
    let y = egcd(aa, bb).2;
    lemma_divides_elim(d as int, aa as int);
    let k = d / aa;
    // k = k (A x + B y) = d x + B (k y), and B divides both terms.
    assert(k == d * x + bb * (k * y)) by (nonlinear_arith)
        requires
            aa * x + bb * y == 1,
            d == aa * k,
    ;
    let bi = bb as int;
    crate::equivalence::lemma_cong_zero_mul(bi, d as int, x);
    lemma_divides_intro(bi, k * y);
    crate::equivalence::lemma_cong_add(bi, d * x, 0, bb * (k * y), 0);
    vstd::arithmetic::div_mod::lemma_small_mod(0, bb);
    lemma_divides_elim(k as int, bi);
    let m = k / bb;
    assert(d == (aa * bb) * m) by (nonlinear_arith)
        requires
            d == aa * k,
            k == bb * m,
    ;
    assert(aa * bb > 0) by (nonlinear_arith)
        requires
            aa > 0,
            bb > 0,
    ;
    lemma_divides_intro((aa * bb) as int, m as int);
}

/// One prime power `q^e` of `F` divides the order `d` of `a` modulo a
/// divisor `r` of `N`.
proof fn lemma_factor_divides_order(n: nat, a: nat, prefix: nat, q: nat, e: nat, r: nat, d: nat)
    requires
        factor_ok(n, a, prefix, q, e),
        is_prime(q),
        order_facts(a, r, n, d),
        n % r == 0,
    ensures
        d % pw(q, e) == 0,
{
    let nm1 = (n - 1) as nat;
    let ri = r as int;
    lemma_order_divides(a, r, n, d);
    lemma_divides_elim(nm1 as int, d as int);
    let t = nm1 / d;
    let nq = (nm1 / q) as nat;
    vstd::arithmetic::div_mod::lemma_small_mod(1, r);
    vstd::arithmetic::div_mod::lemma_small_mod(0, r);
    // (i) d does not divide (n - 1) / q: else a^((n-1)/q) ≡ 1 (mod r), and
    // r would divide both a^((n-1)/q) - 1 and n, whose gcd is 1.
    if nq % d == 0 {
        lemma_divides_elim(nq as int, d as int);
        lemma_pow_one_mul(a, r, d, nq / d);
        let b = pow_mod(a, nq, n);
        lemma_pow_mod_divisor(a, nq, n, r);
        assert(b % r == 1);
        let b1 = ((b + n - 1) % (n as int)) as nat;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, ri);
        vstd::arithmetic::div_mod::lemma_mod_mod(b + n - 1, ri, (n / r) as int);
        assert(b1 % r == (b + n - 1) % ri);
        crate::equivalence::lemma_cong_add(ri, b as int, 1, n as int, 0);
        crate::equivalence::lemma_cong_add(ri, (b + n) as int, 1, 1, 1);
        assert(b1 % r == 0);
        lemma_egcd(n, b1);
        let x = egcd(n, b1).1;
        let y = egcd(n, b1).2;
        crate::equivalence::lemma_cong_zero_mul(ri, n as int, x);
        crate::equivalence::lemma_cong_zero_mul(ri, b1 as int, y);
        crate::equivalence::lemma_cong_add(ri, n * x, 0, b1 * y, 0);
        assert(false);
    }
    // (ii) q does not divide t = (n - 1) / d.
    if t % q == 0 {
        lemma_divides_elim(t as int, q as int);
        let t2 = t / q;
        assert(nm1 == q * (d * t2)) by (nonlinear_arith)
            requires
                nm1 == d * t,
                t == q * t2,
        ;
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish((d * t2) as int, q as int);
        lemma_divides_intro(d as int, t2 as int);
        assert(false);
    }
    // (iii) q^e divides n - 1 = d t, and q does not divide t.
    lemma_prime_power_cancel(q, e, d, t);
}

/// `F` divides the order.
proof fn lemma_prod_divides_order(n: nat, a: nat, fs: Seq<(nat, nat)>, r: nat, d: nat)
    requires
        factors_ok(n, a, fs),
        all_prime(fs),
        order_facts(a, r, n, d),
        n % r == 0,
    ensures
        d % prod(fs) == 0,
    decreases fs.len(),
{
    if fs.len() == 0 {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(d as int, 1, d as int, 0);
    } else {
        let init = fs.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies is_prime(#[trigger] init[i].0) by {
            assert(init[i] == fs[i]);
        }
        assert(is_prime(fs[fs.len() - 1].0));
        lemma_prod_divides_order(n, a, init, r, d);
        lemma_factor_divides_order(n, a, prod(init), fs.last().0, fs.last().1, r, d);
        lemma_prod_pos(n, a, init);
        lemma_pw_pos(fs.last().0, fs.last().1);
        lemma_coprime_mul(prod(init), pw(fs.last().0, fs.last().1), d);
    }
}

/// No divisor `r` of `N` with `1 < r` and `r^2 <= N`.
proof fn lemma_no_small_divisor(n: nat, a: nat, fs: Seq<(nat, nat)>, r: nat)
    requires
        pocklington(n, a, fs),
        all_prime(fs),
        1 < r,
        r * r <= n,
        n % r == 0,
    ensures
        false,
{
    let nm1 = (n - 1) as nat;
    lemma_pow_mod_divisor(a, nm1, n, r);
    vstd::arithmetic::div_mod::lemma_small_mod(1, r);
    lemma_first_one(a, r, 1, nm1);
    let d = first_one(a, r, 1, nm1);
    assert(order_facts(a, r, n, d));
    lemma_prod_divides_order(n, a, fs, r, d);
    lemma_order_bound(a, r, n, d);
    lemma_prod_pos(n, a, fs);
    lemma_divisor_le(d, prod(fs));
    let f = prod(fs);
    assert(f * f < r * r) by (nonlinear_arith)
        requires
            0 < f <= d,
            d <= r - 1,
    ;
}

/// **Pocklington's criterion**: a number meeting [`pocklington`], whose
/// listed factors are prime, is prime.
pub proof fn lemma_pocklington(n: nat, a: nat, fs: Seq<(nat, nat)>)
    requires
        pocklington(n, a, fs),
        all_prime(fs),
    ensures
        is_prime(n),
{
    assert forall|k: nat| 1 < k < n implies #[trigger] (n % k) != 0 by {
        if n % k == 0 {
            lemma_small_divisor(n, k);
            let r = if k * k <= n {
                k
            } else {
                n / k
            };
            lemma_no_small_divisor(n, a, fs, r);
        }
    }
}

} // verus!
