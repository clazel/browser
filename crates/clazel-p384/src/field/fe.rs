//! The executable field: a residue modulo p or n as six Montgomery-domain
//! limbs, with arithmetic that calls fiat-crypto through the six axioms of
//! `crate::axioms` and is proven against [`super::contract`].
//!
//! What is proven here, over those axioms and nothing else:
//!
//! - the conversion into the Montgomery domain (`mul` by `R^2 mod m`) and
//!   out of it (`mul` by 1);
//! - our own octet-string conversions, big-endian, with the range check
//!   (SEC 1 §2.3.6 step 1) as a limb comparison;
//! - `pow`, square-and-multiply from the most significant bit of a 48-octet
//!   exponent, against [`crate::spec::pow_mod`];
//! - `inv`: `pow` with exponent `m - 2` and the check `a w ≡ 1`, against
//!   [`crate::spec::inv`].
//!
//! No fiat byte function, no fiat conversion function and no fiat `nonzero`
//! is called: the axioms are `mul`, `add` and `sub`, and nothing else.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A residue modulo p ([`Which::P`]) or n ([`Which::N`]).
///
/// The limbs are the Montgomery form, little-endian, of a number below the
/// modulus (the type invariant, which is fiat's precondition `0 <= eval z <
/// m`). [`Fe::val`] is the residue they stand for.
pub struct Fe {
    which: Which,
    limbs: [u64; 6],
}

impl Fe {
    #[verifier::type_invariant]
    spec fn well_formed(&self) -> bool {
        value(self.limbs@) < modulus(self.which)
    }

    /// Which modulus this element is a residue of.
    pub closed spec fn which(&self) -> Which {
        self.which
    }

    /// The residue this element stands for: fiat's `eval (from_montgomery
    /// limbs)`, a number in `[0, modulus(which))`.
    pub closed spec fn val(&self) -> nat {
        from_montgomery(self.which, self.limbs@)
    }

    /// The residue is below the modulus. A no-op at run time: it hands the
    /// type invariant to the caller's proof.
    pub fn val_lt_modulus(&self)
        ensures
            self.val() < modulus(self.which()),
    {
        proof {
            use_type_invariant(self);
            super::lemmas::lemma_from_montgomery(self.which, self.limbs@);
        }
    }
}

// ---------------------------------------------------------------------
// The six fiat operations, dispatched on the modulus.
// ---------------------------------------------------------------------

/// Montgomery multiplication: fiat's `mul`, with the equation read off its
/// postcondition (`from_montgomery out` is already reduced).
fn raw_mul(w: Which, a: &[u64; 6], b: &[u64; 6]) -> (out: [u64; 6])
    requires
        value(a@) < modulus(w),
        value(b@) < modulus(w),
    ensures
        value(out@) < modulus(w),
        from_montgomery(w, out@) == from_montgomery(w, a@) * from_montgomery(w, b@) % modulus(w),
{
    let out = match w {
        Which::P => crate::axioms::p_mul(a, b),
        Which::N => crate::axioms::n_mul(a, b),
    };
    proof {
        super::lemmas::lemma_from_montgomery(w, out@);
        vstd::arithmetic::div_mod::lemma_small_mod(from_montgomery(w, out@), modulus(w));
    }
    out
}

/// Addition: fiat's `add`.
fn raw_add(w: Which, a: &[u64; 6], b: &[u64; 6]) -> (out: [u64; 6])
    requires
        value(a@) < modulus(w),
        value(b@) < modulus(w),
    ensures
        value(out@) < modulus(w),
        from_montgomery(w, out@) == (from_montgomery(w, a@) + from_montgomery(w, b@)) % modulus(
            w,
        ),
{
    let out = match w {
        Which::P => crate::axioms::p_add(a, b),
        Which::N => crate::axioms::n_add(a, b),
    };
    proof {
        super::lemmas::lemma_from_montgomery(w, out@);
        vstd::arithmetic::div_mod::lemma_small_mod(from_montgomery(w, out@), modulus(w));
    }
    out
}

/// Subtraction: fiat's `sub`, with its `(x - y) mod m` read as
/// [`crate::spec::fe_sub`].
fn raw_sub(w: Which, a: &[u64; 6], b: &[u64; 6]) -> (out: [u64; 6])
    requires
        value(a@) < modulus(w),
        value(b@) < modulus(w),
    ensures
        value(out@) < modulus(w),
        from_montgomery(w, out@) == crate::spec::fe_sub(
            modulus(w),
            from_montgomery(w, a@),
            from_montgomery(w, b@),
        ),
{
    let out = match w {
        Which::P => crate::axioms::p_sub(a, b),
        Which::N => crate::axioms::n_sub(a, b),
    };
    proof {
        super::lemmas::lemma_from_montgomery(w, out@);
        super::lemmas::lemma_from_montgomery(w, a@);
        super::lemmas::lemma_from_montgomery(w, b@);
        super::lemmas::lemma_modulus(w);
        super::lemmas::lemma_fe_sub(modulus(w), from_montgomery(w, a@), from_montgomery(w, b@));
        vstd::arithmetic::div_mod::lemma_small_mod(from_montgomery(w, out@), modulus(w));
    }
    out
}

// ---------------------------------------------------------------------
// Constants.
// ---------------------------------------------------------------------

/// The limbs of the modulus.
fn modulus_limbs(w: Which) -> (r: [u64; 6])
    ensures
        value(r@) == modulus(w),
{
    let r = match w {
        Which::P => [
            0xffff_ffffu64,
            0xffff_ffff_0000_0000,
            0xffff_ffff_ffff_fffe,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
        ],
        Which::N => [
            0xecec_196a_ccc5_2973u64,
            0x581a_0db2_48b0_a77a,
            0xc763_4d81_f437_2ddf,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
        ],
    };
    proof {
        super::lemmas::lemma_value6(r@);
        match w {
            Which::P => {
                assert(modulus(Which::P) == 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_fffffffe_ffffffff_00000000_00000000_ffffffffnat)
                    by (compute_only);
            },
            Which::N => {
                assert(modulus(Which::N) == 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_c7634d81_f4372ddf_581a0db2_48b0a77a_ecec196a_ccc52973nat)
                    by (compute_only);
            },
        }
    }
    r
}

/// The limbs of `R^2 mod m`, which the conversion into the Montgomery domain
/// multiplies by.
fn r2_limbs(w: Which) -> (r: [u64; 6])
    ensures
        value(r@) == radix() * radix() % modulus(w),
        value(r@) < modulus(w),
{
    let r = match w {
        Which::P => [
            0xffff_fffe_0000_0001u64,
            0x2_0000_0000,
            0xffff_fffe_0000_0000,
            0x2_0000_0000,
            0x1,
            0x0,
        ],
        Which::N => [
            0x2d31_9b24_19b4_09a9u64,
            0xff3d_81e5_df1a_a419,
            0xbc3e_483a_fcb8_2947,
            0xd40d_4917_4aab_1cc5,
            0x3fb0_5b7a_2826_6895,
            0x0c84_ee01_2b39_bf21,
        ],
    };
    proof {
        super::lemmas::lemma_value6(r@);
        super::lemmas::lemma_limb_pow_consts();
        match w {
            Which::P => {
                assert(radix() * radix() % modulus(Which::P) == 0x1_00000002_00000000_fffffffe_00000000_00000002_00000000_fffffffe_00000001nat)
                    by (compute_only);
                assert(modulus(Which::P) == 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_fffffffe_ffffffff_00000000_00000000_ffffffffnat)
                    by (compute_only);
            },
            Which::N => {
                assert(radix() * radix() % modulus(Which::N) == 0x0c84ee01_2b39bf21_3fb05b7a_28266895_d40d4917_4aab1cc5_bc3e483a_fcb82947_ff3d81e5_df1aa419_2d319b24_19b409a9nat)
                    by (compute_only);
                assert(modulus(Which::N) == 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_c7634d81_f4372ddf_581a0db2_48b0a77a_ecec196a_ccc52973nat)
                    by (compute_only);
            },
        }
    }
    r
}

/// The exponent `m - 2` of Fermat's inverse, as 48 big-endian octets.
fn exponent_m_minus_2(w: Which) -> (e: [u8; 48])
    ensures
        crate::spec::os2ip(e@) == modulus(w) - 2,
{
    let e = match w {
        Which::P => [
            0xffu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0xff, 0xff, 0xff, 0xfd,
        ],
        Which::N => [
            0xffu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc7, 0x63, 0x4d, 0x81,
            0xf4, 0x37, 0x2d, 0xdf, 0x58, 0x1a, 0x0d, 0xb2, 0x48, 0xb0, 0xa7, 0x7a, 0xec, 0xec,
            0x19, 0x6a, 0xcc, 0xc5, 0x29, 0x71,
        ],
    };
    proof {
        super::lemmas::lemma_exponent(w);
        match w {
            Which::P => {
                assert(e@ =~= super::lemmas::exponent_octets(Which::P));
            },
            Which::N => {
                assert(e@ =~= super::lemmas::exponent_octets(Which::N));
            },
        }
    }
    e
}

// ---------------------------------------------------------------------
// Montgomery-domain conversion, by `mul`.
// ---------------------------------------------------------------------

impl Fe {
    /// The residue `x`, for `x` the limbs of a number below the modulus (not
    /// in Montgomery form): `mul(x, R^2 mod m)`, whose `from_montgomery` is
    /// `x R^(-1) R^2 R^(-1) = x`.
    fn from_raw(w: Which, x: &[u64; 6]) -> (r: Fe)
        requires
            value(x@) < modulus(w),
        ensures
            r.which() == w,
            r.val() == value(x@),
    {
        let r2 = r2_limbs(w);
        let out = raw_mul(w, x, &r2);
        proof {
            super::lemmas::lemma_modulus(w);
            super::lemmas::lemma_rinv(w);
            super::lemmas::lemma_from_montgomery(w, x@);
            super::lemmas::lemma_from_montgomery(w, r2@);
            // r2 = R^2 mod m is below m, so it is its own residue.
            vstd::arithmetic::div_mod::lemma_small_mod(value(r2@), modulus(w));
            super::lemmas::lemma_to_mont(
                modulus(w),
                radix(),
                super::lemmas::rinv(w),
                value(r2@),
                value(x@),
            );
            vstd::arithmetic::div_mod::lemma_small_mod(value(x@), modulus(w));
        }
        Fe { which: w, limbs: out }
    }

    /// The limbs of the residue itself, not in Montgomery form: `mul(self,
    /// 1)`. Fiat's `mul` leaves `value(out) R^(-1) = a R^(-1) R^(-1)`, so
    /// `value(out) = a R^(-1)`, which is below the modulus.
    fn to_raw(&self) -> (raw: [u64; 6])
        ensures
            value(raw@) == self.val(),
    {
        proof {
            use_type_invariant(self);
        }
        let one = [1u64, 0, 0, 0, 0, 0];
        proof {
            super::lemmas::lemma_value6(one@);
            super::lemmas::lemma_modulus(self.which);
        }
        let out = raw_mul(self.which, &self.limbs, &one);
        proof {
            let w = self.which;
            let m = modulus(w);
            let r = super::lemmas::rinv(w);
            let x = from_montgomery(w, self.limbs@);
            super::lemmas::lemma_modulus(w);
            super::lemmas::lemma_rinv(w);
            super::lemmas::lemma_from_montgomery(w, self.limbs@);
            super::lemmas::lemma_from_montgomery(w, one@);
            super::lemmas::lemma_from_montgomery(w, out@);
            assert(value(one@) == 1);
            // value(out) r = x (1 r) = x r (mod m)
            vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(x as int, (1 * r) as int, m as int);
            super::lemmas::lemma_cancel(m, radix(), r, value(out@), x);
            vstd::arithmetic::div_mod::lemma_small_mod(value(out@), m);
            vstd::arithmetic::div_mod::lemma_small_mod(x, m);
        }
        out
    }

    /// The element 1.
    pub fn one(w: Which) -> (r: Fe)
        ensures
            r.which() == w,
            super::contract::one_ensures(r.val()),
    {
        let one = [1u64, 0, 0, 0, 0, 0];
        proof {
            super::lemmas::lemma_value6(one@);
            super::lemmas::lemma_modulus(w);
        }
        Fe::from_raw(w, &one)
    }
}

// ---------------------------------------------------------------------
// Field operations.
// ---------------------------------------------------------------------

impl Fe {
    /// `self + other`.
    pub fn add(&self, other: &Fe) -> (r: Fe)
        requires
            self.which() == other.which(),
        ensures
            r.which() == self.which(),
            super::contract::add_ensures(self.which(), self.val(), other.val(), r.val()),
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(other);
        }
        let out = raw_add(self.which, &self.limbs, &other.limbs);
        Fe { which: self.which, limbs: out }
    }

    /// `self - other`.
    pub fn sub(&self, other: &Fe) -> (r: Fe)
        requires
            self.which() == other.which(),
        ensures
            r.which() == self.which(),
            super::contract::sub_ensures(self.which(), self.val(), other.val(), r.val()),
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(other);
        }
        let out = raw_sub(self.which, &self.limbs, &other.limbs);
        Fe { which: self.which, limbs: out }
    }

    /// `self * other`.
    pub fn mul(&self, other: &Fe) -> (r: Fe)
        requires
            self.which() == other.which(),
        ensures
            r.which() == self.which(),
            super::contract::mul_ensures(self.which(), self.val(), other.val(), r.val()),
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(other);
        }
        let out = raw_mul(self.which, &self.limbs, &other.limbs);
        Fe { which: self.which, limbs: out }
    }

    /// Whether `self` and `other` are the same residue. The Montgomery form
    /// of a residue below the modulus is unique (`from_montgomery` is
    /// injective on numbers below the modulus), so this compares limbs.
    pub fn equals(&self, other: &Fe) -> (r: bool)
        requires
            self.which() == other.which(),
        ensures
            super::contract::eq_ensures(self.val(), other.val(), r),
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(other);
        }
        let r = self.limbs[0] == other.limbs[0] && self.limbs[1] == other.limbs[1]
            && self.limbs[2] == other.limbs[2] && self.limbs[3] == other.limbs[3]
            && self.limbs[4] == other.limbs[4] && self.limbs[5] == other.limbs[5];
        proof {
            let w = self.which;
            let m = modulus(w);
            super::lemmas::lemma_modulus(w);
            super::lemmas::lemma_rinv(w);
            super::lemmas::lemma_from_montgomery(w, self.limbs@);
            super::lemmas::lemma_from_montgomery(w, other.limbs@);
            if r {
                assert(self.limbs@ =~= other.limbs@);
            }
            if self.val() == other.val() {
                // value(a) r = value(b) r (mod m), so value(a) = value(b)
                // (both are below m), so the limbs are equal.
                super::lemmas::lemma_cancel(
                    m,
                    radix(),
                    super::lemmas::rinv(w),
                    value(self.limbs@),
                    value(other.limbs@),
                );
                vstd::arithmetic::div_mod::lemma_small_mod(value(self.limbs@), m);
                vstd::arithmetic::div_mod::lemma_small_mod(value(other.limbs@), m);
                super::lemmas::lemma_value_inj(self.limbs@, other.limbs@);
                assert(r);
            }
        }
        r
    }
}

// ---------------------------------------------------------------------
// Octet strings.
// ---------------------------------------------------------------------

/// `a < b` as numbers, comparing from the most significant limb.
fn lt6(a: &[u64; 6], b: &[u64; 6]) -> (r: bool)
    ensures
        r == (value(a@) < value(b@)),
{
    proof {
        super::lemmas::lemma_value6(a@);
        super::lemmas::lemma_value6(b@);
    }
    if a[5] != b[5] {
        return a[5] < b[5];
    }
    if a[4] != b[4] {
        return a[4] < b[4];
    }
    if a[3] != b[3] {
        return a[3] < b[3];
    }
    if a[2] != b[2] {
        return a[2] < b[2];
    }
    if a[1] != b[1] {
        return a[1] < b[1];
    }
    a[0] < b[0]
}

/// The eight octets `o[start..start + 8]` as a big-endian integer.
fn load_be64(o: &[u8; 48], start: usize) -> (v: u64)
    requires
        start <= 40,
    ensures
        v as nat == crate::spec::os2ip(o@.subrange(start as int, start as int + 8)),
{
    let mut v: u64 = 0;
    let mut j: usize = 0;
    proof {
        assert(o@.subrange(start as int, start as int) =~= Seq::<u8>::empty());
    }
    while j < 8
        invariant
            j <= 8,
            start <= 40,
            v as nat == crate::spec::os2ip(o@.subrange(start as int, start as int + j as int)),
        decreases 8 - j,
    {
        let idx = start.saturating_add(j);
        let x: u8 = match o.get(idx) {
            Some(b) => *b,
            None => 0,
        };
        proof {
            let pre = o@.subrange(start as int, start as int + j as int);
            super::lemmas::lemma_os2ip_push(pre, x);
            super::lemmas::lemma_os2ip_below_2_56(pre);
            assert(o@.subrange(start as int, start as int + j as int + 1) =~= pre.push(x));
        }
        // Never saturates: the octets so far are below 2^56.
        v = v.saturating_mul(256).saturating_add(x as u64);
        j = j.saturating_add(1);
    }
    v
}

/// The 48 octets as six limbs, least significant first: SEC 1 §2.3.8
/// (<https://www.secg.org/sec1-v2.pdf>) step 1, `x = Σ 2^(8 (mlen - 1 - i))
/// M_i`, the first octet the most significant.
fn load_limbs(o: &[u8; 48]) -> (l: [u64; 6])
    ensures
        value(l@) == crate::spec::os2ip(o@),
{
    let l0 = load_be64(o, 40);
    let l1 = load_be64(o, 32);
    let l2 = load_be64(o, 24);
    let l3 = load_be64(o, 16);
    let l4 = load_be64(o, 8);
    let l5 = load_be64(o, 0);
    let l = [l0, l1, l2, l3, l4, l5];
    proof {
        super::lemmas::lemma_os2ip_chunks(o@);
        super::lemmas::lemma_value6(l@);
    }
    l
}

/// The eight octets of a limb, big-endian.
fn store_be64(x: u64) -> (r: [u8; 8])
    ensures
        crate::spec::os2ip(r@) == x as nat,
{
    let d1 = x / 256;
    let d2 = d1 / 256;
    let d3 = d2 / 256;
    let d4 = d3 / 256;
    let d5 = d4 / 256;
    let d6 = d5 / 256;
    let d7 = d6 / 256;
    let r = [
        d7 as u8,
        (d6 % 256) as u8,
        (d5 % 256) as u8,
        (d4 % 256) as u8,
        (d3 % 256) as u8,
        (d2 % 256) as u8,
        (d1 % 256) as u8,
        (x % 256) as u8,
    ];
    proof {
        super::lemmas::lemma_os2ip8(r@);
    }
    r
}

/// The six limbs as 48 octets, most significant first: the inverse of SEC 1
/// §2.3.8 step 1, that is SEC 1 §2.3.7 (Integer-to-Octet-String) with `mlen =
/// 48`.
fn store_limbs(l: &[u64; 6]) -> (o: [u8; 48])
    ensures
        o@.len() == 48,
        crate::spec::os2ip(o@) == value(l@),
{
    let c5 = store_be64(l[5]);
    let c4 = store_be64(l[4]);
    let c3 = store_be64(l[3]);
    let c2 = store_be64(l[2]);
    let c1 = store_be64(l[1]);
    let c0 = store_be64(l[0]);
    let o = [
        c5[0], c5[1], c5[2], c5[3], c5[4], c5[5], c5[6], c5[7], c4[0], c4[1], c4[2], c4[3], c4[4],
        c4[5], c4[6], c4[7], c3[0], c3[1], c3[2], c3[3], c3[4], c3[5], c3[6], c3[7], c2[0], c2[1],
        c2[2], c2[3], c2[4], c2[5], c2[6], c2[7], c1[0], c1[1], c1[2], c1[3], c1[4], c1[5], c1[6],
        c1[7], c0[0], c0[1], c0[2], c0[3], c0[4], c0[5], c0[6], c0[7],
    ];
    proof {
        super::lemmas::lemma_os2ip_chunks(o@);
        super::lemmas::lemma_value6(l@);
        assert(o@.subrange(0, 8) =~= c5@);
        assert(o@.subrange(8, 16) =~= c4@);
        assert(o@.subrange(16, 24) =~= c3@);
        assert(o@.subrange(24, 32) =~= c2@);
        assert(o@.subrange(32, 40) =~= c1@);
        assert(o@.subrange(40, 48) =~= c0@);
    }
    o
}

impl Fe {
    /// SEC 1 §2.3.6: the residue whose big-endian octets are `o`, if that
    /// integer is below the modulus (step 1: "Output 'invalid' and stop if a
    /// does not lie in the interval [0, m - 1]"), and none otherwise.
    pub fn from_octets(w: Which, o: &[u8; 48]) -> (r: Option<Fe>)
        ensures
            match r {
                Some(f) => f.which() == w && super::contract::from_octets_ensures(
                    w,
                    o@,
                    Some(f.val()),
                ),
                None => super::contract::from_octets_ensures(w, o@, None),
            },
    {
        let limbs = load_limbs(o);
        let m = modulus_limbs(w);
        if lt6(&limbs, &m) {
            Some(Fe::from_raw(w, &limbs))
        } else {
            None
        }
    }

    /// The 48 octets of the residue, big-endian: SEC 1 §2.3.5
    /// (Field-Element-to-Octet-String), whose step 1 (§2.3.9) is the identity
    /// for an odd prime (SP 800-186 F.1) and whose step 2 is §2.3.7.
    pub fn to_octets(&self) -> (r: [u8; 48])
        ensures
            super::contract::to_octets_ensures(self.val(), r@),
    {
        let raw = self.to_raw();
        store_limbs(&raw)
    }
}

// ---------------------------------------------------------------------
// Exponentiation and inversion.
// ---------------------------------------------------------------------

/// A bit as a number.
spec fn bit_nat(b: bool) -> nat {
    if b {
        1
    } else {
        0
    }
}

/// Take the bit worth `t` off `rem`: whether `rem >= t`, and `rem` without it.
fn split_bit(rem: u8, t: u8) -> (r: (bool, u8))
    ensures
        r.0 == (rem >= t),
        rem as nat == r.1 as nat + (if r.0 {
            t as nat
        } else {
            0nat
        }),
        r.1 <= rem,
{
    if rem >= t {
        (true, rem.wrapping_sub(t))
    } else {
        (false, rem)
    }
}

/// One step of square-and-multiply: `acc^2`, times `a` if `bit`.
fn pow_step(a: &Fe, acc: &Fe, bit: bool, Ghost(q): Ghost<nat>) -> (r: Fe)
    requires
        a.which() == acc.which(),
        acc.val() == crate::spec::pow_mod(a.val(), q, modulus(a.which())),
    ensures
        r.which() == a.which(),
        r.val() == crate::spec::pow_mod(a.val(), 2 * q + bit_nat(bit), modulus(a.which())),
{
    a.val_lt_modulus();
    proof {
        super::lemmas::lemma_modulus(a.which());
        super::lemmas::lemma_pow_mod_step(a.val(), q, bit, modulus(a.which()));
        vstd::arithmetic::div_mod::lemma_small_mod(a.val(), modulus(a.which()));
    }
    let sq = acc.mul(acc);
    if bit {
        sq.mul(a)
    } else {
        sq
    }
}

/// Eight steps of square-and-multiply, one per bit of `byte`, most
/// significant first: `acc^256 a^byte`.
fn pow_byte(a: &Fe, acc: &Fe, byte: u8, Ghost(q): Ghost<nat>) -> (r: Fe)
    requires
        a.which() == acc.which(),
        acc.val() == crate::spec::pow_mod(a.val(), q, modulus(a.which())),
    ensures
        r.which() == a.which(),
        r.val() == crate::spec::pow_mod(a.val(), q * 256 + byte as nat, modulus(a.which())),
{
    let (b7, rem) = split_bit(byte, 128);
    let acc = pow_step(a, acc, b7, Ghost(q));
    let ghost q1: nat = 2 * q + bit_nat(b7);
    let (b6, rem) = split_bit(rem, 64);
    let acc = pow_step(a, &acc, b6, Ghost(q1));
    let ghost q2: nat = 2 * q1 + bit_nat(b6);
    let (b5, rem) = split_bit(rem, 32);
    let acc = pow_step(a, &acc, b5, Ghost(q2));
    let ghost q3: nat = 2 * q2 + bit_nat(b5);
    let (b4, rem) = split_bit(rem, 16);
    let acc = pow_step(a, &acc, b4, Ghost(q3));
    let ghost q4: nat = 2 * q3 + bit_nat(b4);
    let (b3, rem) = split_bit(rem, 8);
    let acc = pow_step(a, &acc, b3, Ghost(q4));
    let ghost q5: nat = 2 * q4 + bit_nat(b3);
    let (b2, rem) = split_bit(rem, 4);
    let acc = pow_step(a, &acc, b2, Ghost(q5));
    let ghost q6: nat = 2 * q5 + bit_nat(b2);
    let (b1, rem) = split_bit(rem, 2);
    let acc = pow_step(a, &acc, b1, Ghost(q6));
    let ghost q7: nat = 2 * q6 + bit_nat(b1);
    let last = split_bit(rem, 1);
    let b0 = last.0;
    let acc = pow_step(a, &acc, b0, Ghost(q7));
    proof {
        // rem is now 0, and byte = 128 b7 + 64 b6 + ... + b0.
        assert(last.1 == 0);
        assert(2 * q7 + bit_nat(b0) == q * 256 + byte as nat);
    }
    acc
}

impl Fe {
    /// `self^e` for the exponent `e` given as 48 big-endian octets.
    pub fn pow(&self, e: &[u8; 48]) -> (r: Fe)
        ensures
            r.which() == self.which(),
            super::contract::pow_ensures(self.which(), self.val(), e@, r.val()),
    {
        let mut acc = Fe::one(self.which);
        let mut i: usize = 0;
        let ghost mut q: nat = 0;
        proof {
            super::lemmas::lemma_modulus(self.which);
            assert(e@.subrange(0, 0) =~= Seq::<u8>::empty());
            assert(crate::spec::pow_mod(self.val(), 0, modulus(self.which)) == 1nat % modulus(
                self.which,
            ));
            vstd::arithmetic::div_mod::lemma_small_mod(1nat, modulus(self.which));
        }
        while i < 48
            invariant
                i <= 48,
                acc.which() == self.which(),
                q == crate::spec::os2ip(e@.subrange(0, i as int)),
                acc.val() == crate::spec::pow_mod(self.val(), q, modulus(self.which())),
            decreases 48 - i,
        {
            let byte: u8 = match e.get(i) {
                Some(b) => *b,
                None => 0,
            };
            let next = pow_byte(self, &acc, byte, Ghost(q));
            proof {
                let pre = e@.subrange(0, i as int);
                super::lemmas::lemma_os2ip_push(pre, byte);
                assert(e@.subrange(0, i as int + 1) =~= pre.push(byte));
                q = q * 256 + byte as nat;
            }
            acc = next;
            i = i.saturating_add(1);
        }
        proof {
            assert(e@.subrange(0, 48) =~= e@);
        }
        acc
    }

    /// `self^(-1)`: `self^(m - 2)`, accepted only if `self * self^(m - 2)`
    /// is 1. This is the spec's `inv`; FIPS 186-5 §6.4.2 step 4 says "using
    /// the routine in Appendix B.1", and B.1 allows any algorithm with an
    /// equivalent result (choice 3 of `crate::spec`).
    pub fn inv(&self) -> (r: Option<Fe>)
        ensures
            match r {
                Some(f) => f.which() == self.which() && super::contract::inv_ensures(
                    self.which(),
                    self.val(),
                    Some(f.val()),
                ),
                None => super::contract::inv_ensures(self.which(), self.val(), None),
            },
    {
        let w = self.which;
        let e = exponent_m_minus_2(w);
        let x = self.pow(&e);
        let chk = self.mul(&x);
        let one = Fe::one(w);
        let ok = chk.equals(&one);
        self.val_lt_modulus();
        proof {
            super::lemmas::lemma_modulus(w);
            vstd::arithmetic::div_mod::lemma_small_mod(self.val(), modulus(w));
        }
        if ok {
            Some(x)
        } else {
            None
        }
    }
}

} // verus!
