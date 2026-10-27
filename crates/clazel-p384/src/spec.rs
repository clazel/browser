//! Executable-style specification of ECDSA signature verification over
//! NIST P-384. Nothing here runs; it defines what "correct" means.
//!
//! # Sources (pinned)
//!
//! Each is the NIST or SECG PDF, identified by the SHA-256 of the file that
//! was transcribed. Step numbers below are those of these texts, read from
//! the text extracted from the PDFs, and for FIPS 186-5 §6.4.2 and B.1 also
//! from the rendered pages; they were not recalled.
//!
//! - **FIPS 186-5**, *Digital Signature Standard (DSS)*, published
//!   3 February 2023, <https://doi.org/10.6028/NIST.FIPS.186-5>, PDF SHA-256
//!   `fbb9c7c2ba442f03c57b63b43c888311903c9d0f29f89b06efdebd9b619140c5`.
//!   §6.4.2 "ECDSA Signature Verification Algorithm" (printed page 25, nine
//!   steps), Appendix B.1 "Computation of the Inverse Value" (page 53) and
//!   B.2.1 "Conversion of a Bit String to an Integer" (page 54).
//! - **NIST SP 800-186**, *Recommendations for Discrete Logarithm-based
//!   Cryptography: Elliptic Curve Domain Parameters*, February 2023,
//!   <https://doi.org/10.6028/NIST.SP.800-186>, PDF SHA-256
//!   `53c7cf3340528aaa0a7bbeaef947f2099568192367d4341a7d4abceb55f78432`.
//!   §3.2.1 (the Weierstrass equation, a = -3, h = 1), §3.2.1.4 (the P-384
//!   parameters), Appendix D.1.1.1 "Partial Public Key Validation" and
//!   Appendix F.1 "Conversion of a Field Element to an Integer".
//! - **SEC 1: Elliptic Curve Cryptography**, version 2.0, 21 May 2009,
//!   <https://www.secg.org/sec1-v2.pdf>, PDF SHA-256
//!   `54687189af3de645756a30a801b596fd14c6566992c13bfd58eede399f324a89`.
//!   §2.2.1 (the group law), §2.3.1, §2.3.2, §2.3.4, §2.3.6, §2.3.8 and
//!   §2.3.9 (conversions), §3.2.2.1 (public key validation) and §4.1.4
//!   (the verifying operation).
//!
//! FIPS 186-5 is the algorithm. Where it defers to "the routine" (Appendix
//! B.1 for the inverse, SP 800-186 Appendix F.1 for the field element to
//! integer conversion, SP 800-186 Appendix D.1 for the public key) the
//! function says which source it follows. FIPS 186-5 gives no group law and
//! no point decoding; those are SEC 1's.
//!
//! # How the extracted text was read
//!
//! The text extracted from the PDFs loses typography, so the pages were
//! also rendered and read. Two losses matter.
//!
//! - FIPS 186-5 §6.4.2 step 3a prints `⌈log2(n)⌉` (ceiling brackets). The
//!   extracted text shows `log2(n)`. The brackets are in the PDF, and SEC 1
//!   §4.1.4 step 3.2 prints `⌈log2 n⌉` too. So the number of bits kept is
//!   `⌈log2 n⌉`, the bit length `len(n)` of FIPS 186-5 §6.4.1 step 2a and
//!   §6.1.1 ("the leftmost len(n) bits"). For a prime n > 2 the two agree,
//!   and for P-384 both are 384. A floor reading would give 383 and is not
//!   what any of the three texts says.
//! - Step 8 names the integer `r1`, which the extraction prints as `p 1`.
//!
//! # Modelling choices
//!
//! Each one is a deliberate, listed deviation in form or in domain.
//!
//! 1. **The input is the digest H, not the message M.** Step 2 ("Compute H
//!    = Hash(M)") is the only use of M, so the meaning is unchanged. The hash
//!    is computed by `clazel-crypto`, which holds the hash axioms; **this
//!    crate therefore has no axiom.** H is an octet string of any length
//!    (the contract limits it to 0 to 64 octets). The bit string "H" of the
//!    standard, with `hashlen` bits, is those octets read most significant
//!    bit first (SEC 1 §2.3.2), so `hashlen = 8 |H|`.
//! 2. **The domain parameters D are a [`Curve`] value.** FIPS 186-5 is
//!    itself parameterised by D. [`p384`] is transcribed from SP 800-186
//!    §3.2.1.4. [`toy`] is a small curve that no standard defines, used
//!    only by `examples.rs` and the mutation certificates. The cofactor
//!    h = 1 is not a field: both curves have it, and choice 8 uses it. The
//!    coefficient a is stored as the residue `p - 3`. FIPS 186-5 §6.4.2
//!    says the validity of D "shall be assured" before verification
//!    (§6.2.2 item 1). That is a precondition, not a step: this file
//!    transcribes D and does not re-check it at run time. That the
//!    transcribed constants satisfy their stated properties is for
//!    `lemmas.rs`, and that p and n are prime is cited from SP 800-186.
//! 3. **Division mod m (m = p or m = n) is [`inv`]**: Fermat's
//!    `a^(m-2) mod m`, accepted only if it is checked to be an inverse, and
//!    `None` (which makes the signature invalid) otherwise. FIPS 186-5 step
//!    4 says "using the routine in Appendix B.1", and B.1 itself says
//!    "Other (constant time) algorithms that produce an equivalent result
//!    may be used". B.1 is also transcribed here, as [`b1_inverse`], and
//!    `examples.rs` evaluates both on the same inputs. For a prime modulus
//!    and `0 < z < m` they agree (Fermat's little theorem for [`inv`];
//!    B.1's correctness for [`b1_inverse`]); that is cited, not proven, and
//!    the `None` branch of [`inv`] is reachable only for `a ≡ 0`, which
//!    steps 1 and 4 and SEC 1 §2.2.1's own case split rule out.
//! 4. **The group law is SEC 1 §2.2.1's affine rules, in its order.** The
//!    point at infinity is the distinct [`Point::Infinity`]. SEC 1's rule 3
//!    ("two points with the same x-coordinates when the points are either
//!    distinct or have y-coordinate 0") is recognised as `x1 = x2` and
//!    `y1 + y2 ≡ 0`, and rule 5 (doubling) is the remaining `x1 = x2` case.
//!    On the curve these are the same cases; for points not on the curve
//!    SEC 1 defines nothing, and [`ec_add`] is not claimed to mean anything
//!    there (the verification never reaches that case, because every point
//!    comes from a validated Q or from G). Points are kept with both
//!    coordinates in [0, p-1], so `x1 = x2` compares field elements.
//!    [`ec_add`] returns `Option` because [`inv`] can fail.
//! 5. **`[k]P` is [`scalar_mul`], MSB-first double-and-add** over [`ec_add`].
//!    SEC 1 §2.2.1 defines kP as P added to itself k times and says it is
//!    computed "using the addition rule together with the double-and-add
//!    algorithm or one of its variants". That the two are equal follows from
//!    the associativity of the group law, which SEC 1 asserts ("The set of
//!    points on E(Fp) forms a group") and which is cited, not proven.
//! 6. **`[u]G + [v]Q` is the sum of two separately computed products**
//!    (step 6), not a joint ladder. Equal by the same associativity.
//! 7. **Only the uncompressed form is accepted.** SEC 1 §2.3.4 step 2
//!    (compressed points `02`/`03`) is refused: [`os2p`] returns `None`.
//!    RFC 5480 §2.2 requires support for the uncompressed form only. SEC 1
//!    §2.3.4 itself refuses every other first octet (step 3.2), so hybrid
//!    `06`/`07` is invalid there too, and the point at infinity `00`
//!    (§2.3.4 step 1) is decoded and then refused by [`public_key_valid`].
//!    An input whose length is none of the three that §2.3.4 admits is
//!    invalid (§2.3.4's input condition is not met).
//! 8. **The public key is always validated, with partial validation.**
//!    FIPS 186-5 §6.4.2 says the validity of Q "should also be checked (see
//!    Appendix D.1 of SP 800-186)". "Should" does not oblige; this
//!    specification rejects an invalid Q. [`public_key_valid`] is SP 800-186
//!    D.1.1.1 steps 1 to 3 (equivalently SEC 1 §3.2.2.1 steps 1 and 2). The
//!    check `nQ = O` (SP 800-186 D.1.1.2 step 2, SEC 1 §3.2.2.1 step 4) is
//!    omitted. SEC 1 §3.2.2.1 says why that is sound: "if h = 1, then nQ = O
//!    is implied by the checks in Steps 2 and 3". P-384 has h = 1 (SP 800-186
//!    §3.2.1.4), so partial validation is full validation. This is checked
//!    first, before step 1, following the preamble of §6.4.2 ("validity ...
//!    prior to the verification"); the order changes only which [`Step`] is
//!    reported, not the verdict.
//! 9. **r and s are integers.** FIPS 186-5 inputs (r, s) are "a pair of
//!    integers". The executable code takes 48-octet big-endian strings
//!    and converts them with [`os2ip`]; the range check is step 1, here,
//!    not a DER rule.
//! 10. **Step 3 is done on bit strings, as printed.** [`derive_e`] reads H
//!     as a bit string (SEC 1 §2.3.2), keeps all of it if `⌈log2 n⌉ ≥ hashlen`
//!     and otherwise its leftmost `⌈log2 n⌉` bits (SEC 1 §4.1.4 step 3.2),
//!     and converts that to an integer by Appendix B.2.1 (SP 800-186 F.4).
//!     SEC 1 §4.1.4 goes through an octet string (§2.3.1, which pads on the
//!     left with zeros, then §2.3.8); the integer is the same. A digest of 0
//!     octets gives e = 0. The result may exceed n; step 5 reduces it.
//! 11. **Steps 7 and 8 are folded.** Step 7 takes the x-coordinate of the
//!     affine representation, which [`Point::Affine`] already is. Step 8
//!     converts it to an integer by SP 800-186 F.1; for an odd prime q, F.1
//!     step 1 is the identity (a is already an integer in [0, q-1]), and so
//!     is SEC 1 §2.3.9 step 1.
//! 12. **The result says which step rejected.** [`ecdsa_verify_steps`]
//!     returns `Err(step)` so that a deliberate bug in one check can be told
//!     apart from a bug elsewhere. The standard's output is only "accept" or
//!     "reject"; that is [`ecdsa_verify`]. A failure of [`inv`] or of [`ec_add`]
//!     while computing step 4 or step 6 is reported at that step. Step 3 and
//!     step 5 cannot reject. FIPS 186-5 prints step 3's second sub-step as
//!     "a." again; it is written 3b here (see `docs/ERRATA.md`).
//! 13. **No constant time.** Every input is public.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Domain parameters (FIPS 186-5 §6.1, SP 800-186 §3.2.1).
// ---------------------------------------------------------------------

/// The domain parameters D = (q = p, h = 1, n, a, b, G) of FIPS 186-5 §6.1
/// for a curve `y^2 = x^3 + a x + b` over GF(p) (SP 800-186 §3.2.1), plus
/// `octets`, the length `⌈(log2 p)/8⌉` of a field element as an octet string
/// (SEC 1 §2.3.4's `⌈(log2 q)/8⌉`). The cofactor is 1 (choice 8) and is not a
/// field. `a` is the residue in [0, p-1] (for a = -3, `p - 3`).
pub struct Curve {
    /// The prime modulus of the field GF(p).
    pub p: nat,
    /// The coefficient a, as a residue in [0, p-1].
    pub a: nat,
    /// The coefficient b.
    pub b: nat,
    /// The x-coordinate of the base point G.
    pub gx: nat,
    /// The y-coordinate of the base point G.
    pub gy: nat,
    /// The (prime) order of G, which is the order of the group (h = 1).
    pub n: nat,
    /// The length in octets of a field element: `⌈(log2 p)/8⌉`.
    pub octets: nat,
}

/// NIST P-384, SP 800-186 §3.2.1.4 (printed pages 11-12). Every constant
/// below is the hexadecimal value printed there, and was also checked against
/// the printed decimal value and, for p, against `2^384 - 2^128 - 2^96 +
/// 2^32 - 1`, with a script.
///
/// - p = `2^384 - 2^128 - 2^96 + 2^32 - 1`
/// - n = `0xffffffff ffffffff ffffffff ffffffff ffffffff ffffffff c7634d81
///   f4372ddf 581a0db2 48b0a77a ecec196a ccc52973`
/// - a = -3, that is `p - 3`
/// - b, Gx and Gy as printed there
/// - h = 1 (not a field, choice 8)
pub open spec fn p384() -> Curve {
    Curve {
        p: 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_fffffffe_ffffffff_00000000_00000000_ffffffffnat,
        a: 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_fffffffe_ffffffff_00000000_00000000_fffffffcnat,
        b: 0xb3312fa7_e23ee7e4_988e056b_e3f82d19_181d9c6e_fe814112_0314088f_5013875a_c656398d_8a2ed19d_2a85c8ed_d3ec2aefnat,
        gx: 0xaa87ca22_be8b0537_8eb1c71e_f320ad74_6e1d3b62_8ba79b98_59f741e0_82542a38_5502f25d_bf55296c_3a545e38_72760ab7nat,
        gy: 0x3617de4a_96262c6f_5d9e98bf_9292dc29_f8f41dbd_289a147c_e9da3113_b5f0b8c0_0a60b1ce_1d7e819d_7a431d7c_90ea0e5fnat,
        n: 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_c7634d81_f4372ddf_581a0db2_48b0a77a_ecec196a_ccc52973nat,
        octets: 48,
    }
}

/// A toy curve for evaluated examples. **No standard defines it**, and it is
/// never used by any executable code: it is small enough for `by
/// (compute_only)` to evaluate a whole verification.
///
/// `y^2 = x^3 - 3x + 50` over GF(83): p = 83 and a = 80 = -3 (mod 83).
/// The group has 67 elements, a prime, so n = 67 and h = 1, and every point
/// other than O generates it. G = (1, 31). Field elements are one octet. n
/// has 7 bits, so a digest is truncated at a bit that is not an octet
/// boundary, and n < p, so an x-coordinate can be at least n and `x mod n`
/// matters (step 9). How it was found and checked is in the comment below;
/// `examples.rs` evaluates the checks that can be.
///
/// ```text
/// # Search (Python 3): every prime p < 128 and b in [0, p), with
/// # 4a^3 + 27b^2 != 0 mod p for a = -3, counting points by brute force:
/// #   count = 1 + sum over x of #{y : y^2 = x^3 - 3x + b}
/// # keeping those whose count n is prime with 64 <= n < p. The one chosen
/// # is (p, b, n) = (83, 50, 67); G is the first point found, (1, 31).
/// # Checks, same script: the curve has 66 affine points (so n = 67 with O);
/// # n * P = O for every one of them with an independent double-and-add
/// # (so each has order n, h = 1); 67 is prime; 83 is prime.
/// ```
///
/// `examples.rs` shows `[67]G = O` and `[66]G = -G` by evaluation.
pub open spec fn toy() -> Curve {
    Curve { p: 83, a: 80, b: 50, gx: 1, gy: 31, n: 67, octets: 1 }
}

// ---------------------------------------------------------------------
// Points and the group law (SEC 1 §2.2.1).
// ---------------------------------------------------------------------

/// A point of E(Fp): the point at infinity O, or an affine point (x, y) with
/// both coordinates in [0, p-1] (SEC 1 §2.2.1).
pub enum Point {
    /// The point at infinity O.
    Infinity,
    /// An affine point `(x, y)`.
    Affine {
        /// The x-coordinate, in [0, p-1].
        x: nat,
        /// The y-coordinate, in [0, p-1].
        y: nat,
    },
}

/// The base point G of D (FIPS 186-5 §6.1).
pub open spec fn base_point(c: Curve) -> Point {
    Point::Affine { x: c.gx, y: c.gy }
}

/// `x^3 + a x + b` in GF(p), reduced.
pub open spec fn curve_rhs(c: Curve, x: nat) -> nat {
    (x * x * x + c.a * x + c.b) % c.p
}

/// The defining equation `y^2 ≡ x^3 + a x + b (mod p)` (SEC 1 §2.2.1;
/// SP 800-186 §3.2.1). It says nothing about the range of x and y.
pub open spec fn satisfies_equation(c: Curve, x: nat, y: nat) -> bool {
    y * y % c.p == curve_rhs(c, x)
}

/// `x - y` in GF(p), for any naturals x and y, as a residue in [0, p-1].
pub open spec fn fe_sub(m: nat, x: nat, y: nat) -> nat {
    ((x % m) + m - (y % m)) as nat % m
}

/// `a^e mod m` by square-and-multiply, from the most significant bit of e
/// (a helper of [`inv`], not a step of any standard).
pub open spec fn pow_mod(a: nat, e: nat, m: nat) -> nat
    decreases e,
{
    if e == 0 {
        1nat % m
    } else {
        let half = pow_mod(a, e / 2, m);
        let sq = half * half % m;
        if e % 2 == 0 {
            sq
        } else {
            sq * (a % m) % m
        }
    }
}

/// `a^(-1) mod m` (choice 3): `w = a^(m-2) mod m`, and `Some(w)` only if
/// `a w ≡ 1 (mod m)`; `None` otherwise. `m` is p or n, both prime
/// (SP 800-186 §3.2.1.4), so by Fermat's little theorem the check passes
/// exactly when `a ≢ 0`. FIPS 186-5 step 4 and SEC 1 §2.2.1's divisions
/// both mean this.
pub open spec fn inv(m: nat, a: nat) -> Option<nat> {
    let w = pow_mod(a, (m - 2) as nat, m);
    if (a % m) * w % m == 1 {
        Some(w)
    } else {
        None
    }
}

/// FIPS 186-5 Appendix B.1 steps 3 to 7: the loop of the extended Euclidean
/// algorithm, with the state `(i, j, y2, y1)` of step 2, run until `j` is 0
/// (step 7 "If (j > 0), then go to step 3"). Returns `(i, y2)`. The caller
/// has already ensured j > 0 (step 1), so the loop body runs at least once,
/// as the standard's does.
pub open spec fn b1_loop(i: nat, j: nat, y2: int, y1: int) -> (nat, int)
    decreases j,
{
    if j == 0 {
        (i, y2)
    } else {
        // 3. quotient = ⌊i/j⌋.
        let quotient = i / j;
        // 4. remainder = i - (j × quotient). That is i mod j, which is also
        //    what makes the recursion terminate.
        let remainder = i % j;
        // 5. y = y2 - (y1 × quotient).
        let y = y2 - y1 * quotient;
        // 6. Set i = j, j = remainder, y2 = y1, and y1 = y.
        // 7. If (j > 0), then go to step 3.
        b1_loop(j, remainder, y1, y)
    }
}

/// FIPS 186-5 Appendix B.1, "Computation of the Inverse Value" (printed
/// page 53). Input `z` and `a`; `None` is the ERROR indication, and
/// `Some(z^-1 mod a)` is SUCCESS. It is the reference routine of step 4;
/// [`inv`] is the one used (choice 3).
pub open spec fn b1_inverse(z: nat, a: nat) -> Option<nat> {
    // 1. "Verify that a and z are positive integers such that z < a; if not,
    //    return an ERROR indication." (Inputs: a is "a positive integer
    //    greater than 1".)
    if !(a > 1 && z > 0 && z < a) {
        None
    } else {
        // 2. Set i = a, j = z, y2 = 0, and y1 = 1.
        // 3. to 7. The loop.
        let (i, y2) = b1_loop(a, z, 0, 1);
        // 8. If (i ≠ 1), then return an ERROR indication.
        if i != 1 {
            None
        } else {
            // 9. Return SUCCESS and z^-1 = y2 mod a.
            Some((y2 % (a as int)) as nat)
        }
    }
}

/// SEC 1 §2.2.1, the addition rule on E(Fp) (printed page 7, rules 1 to 5),
/// in the order printed. `None` is a failed division ([`inv`] returned
/// `None`), which makes the whole verification reject (choice 3).
pub open spec fn ec_add(c: Curve, pp: Point, qq: Point) -> Option<Point> {
    match (pp, qq) {
        // 1. "Rule to add the point at infinity to itself: O + O = O."
        (Point::Infinity, Point::Infinity) => Some(Point::Infinity),
        // 2. "Rule to add the point at infinity to any other point:
        //    (x, y) + O = O + (x, y) = (x, y)."
        (Point::Infinity, Point::Affine { x, y }) => Some(qq),
        (Point::Affine { x, y }, Point::Infinity) => Some(pp),
        (Point::Affine { x: x1, y: y1 }, Point::Affine { x: x2, y: y2 }) => {
            if x1 == x2 && (y1 + y2) % c.p == 0 {
                // 3. "Rule to add two points with the same x-coordinates when
                //    the points are either distinct or have y-coordinate 0:
                //    (x, y) + (x, -y) = O."
                Some(Point::Infinity)
            } else if x1 != x2 {
                // 4. "Rule to add two points with different x-coordinates:
                //    ... λ ≡ (y2 - y1)/(x2 - x1) (mod p),
                //    x3 ≡ λ^2 - x1 - x2 (mod p),
                //    y3 ≡ λ(x1 - x3) - y1 (mod p)."
                match inv(c.p, fe_sub(c.p, x2, x1)) {
                    None => None,
                    Some(w) => {
                        let lambda = fe_sub(c.p, y2, y1) * w % c.p;
                        let x3 = fe_sub(c.p, fe_sub(c.p, lambda * lambda % c.p, x1), x2);
                        let y3 = fe_sub(c.p, lambda * fe_sub(c.p, x1, x3) % c.p, y1);
                        Some(Point::Affine { x: x3, y: y3 })
                    },
                }
            } else {
                // 5. "Rule to add a point to itself (double a point): Let
                //    (x1, y1) be a point with y1 ≠ 0. ...
                //    λ ≡ (3 x1^2 + a)/(2 y1) (mod p),
                //    x3 ≡ λ^2 - 2 x1 (mod p),
                //    y3 ≡ λ(x1 - x3) - y1 (mod p)."
                // Here x1 = x2 and not rule 3. On the curve that means
                // y2 = y1 ≠ 0 (modelling choice 4).
                match inv(c.p, 2 * y1 % c.p) {
                    None => None,
                    Some(w) => {
                        let lambda = (3 * x1 * x1 + c.a) % c.p * w % c.p;
                        let x3 = fe_sub(c.p, lambda * lambda % c.p, 2 * x1 % c.p);
                        let y3 = fe_sub(c.p, lambda * fe_sub(c.p, x1, x3) % c.p, y1);
                        Some(Point::Affine { x: x3, y: y3 })
                    },
                }
            }
        },
    }
}

/// `[k]P` (SEC 1 §2.2.1 "scalar multiplication"; choice 5): MSB-first
/// double-and-add. It handles the bits of `k` from the most significant: the
/// result for `k` is the result for `k / 2`, doubled, plus P when `k` is odd.
/// `[0]P = O`. `None` if any addition fails.
pub open spec fn scalar_mul(c: Curve, k: nat, pt: Point) -> Option<Point>
    decreases k,
{
    if k == 0 {
        Some(Point::Infinity)
    } else {
        match scalar_mul(c, k / 2, pt) {
            None => None,
            Some(half) => match ec_add(c, half, half) {
                None => None,
                Some(twice) => if k % 2 == 1 {
                    ec_add(c, twice, pt)
                } else {
                    Some(twice)
                },
            },
        }
    }
}

// ---------------------------------------------------------------------
// Conversions (SEC 1 §2.3, SP 800-186 Appendix F, FIPS 186-5 B.2.1).
// ---------------------------------------------------------------------

/// `2^m`, by repeated squaring.
pub open spec fn two_to(m: nat) -> nat
    decreases m,
{
    if m == 0 {
        1
    } else if m % 2 == 0 {
        let half = two_to(m / 2);
        half * half
    } else {
        2 * two_to((m - 1) as nat)
    }
}

/// SEC 1 §2.3.8 Octet-String-to-Integer Conversion, step 1:
/// `x = Σ 2^(8(mlen-1-i)) M_i`, the first octet the most significant.
pub open spec fn os2ip(m: Seq<u8>) -> nat
    decreases m.len(),
{
    if m.len() == 0 {
        0
    } else {
        os2ip(m.drop_last()) * 256 + m.last() as nat
    }
}

/// SEC 1 §2.3.2 Octet-String-to-Bit-String Conversion, step 1: "B_8i ...
/// B_8i+7 = M_i". Bit `i` of the result is bit `7 - (i mod 8)` of octet
/// `i / 8` (each octet written most significant bit first).
pub open spec fn octets_to_bits(m: Seq<u8>) -> Seq<bool> {
    Seq::new(8 * m.len(), |i: int| (m[i / 8] as nat / two_to((7 - i % 8) as nat)) % 2 == 1)
}

/// FIPS 186-5 Appendix B.2.1 (printed page 54), step 2: "{x1, ..., xn} →
/// (x1 × 2^(n-1)) + ... + xn": the first bit is the most significant. The
/// empty bit string is 0. Same as SP 800-186 F.4.
pub open spec fn bits_to_int(b: Seq<bool>) -> nat
    decreases b.len(),
{
    if b.len() == 0 {
        0
    } else {
        bits_to_int(b.drop_last()) * 2 + if b.last() {
            1nat
        } else {
            0nat
        }
    }
}

/// `⌈log2 n⌉`: the least `L` with `n ≤ 2^L` (0 for n ≤ 1). For a prime n > 2
/// this is the bit length `len(n)` (see the header, "How the extracted text
/// was read").
pub open spec fn ceil_log2(n: nat) -> nat
    decreases n,
{
    if n <= 1 {
        0
    } else {
        1 + ceil_log2((n + 1) / 2)
    }
}

/// SEC 1 §2.3.6 Octet-String-to-Field-Element Conversion, for q = p an odd
/// prime. Input: an octet string of `mlen` octets (the caller passes
/// exactly `octets`).
pub open spec fn os2fe(c: Curve, m: Seq<u8>) -> Option<nat> {
    // 1. "Convert M to an integer a using the conversion routine specified in
    //    Section 2.3.8. Output 'invalid' and stop if a does not lie in the
    //    interval [0, p - 1], otherwise output a."
    let a = os2ip(m);
    if a < c.p {
        Some(a)
    } else {
        None
    }
}

/// SEC 1 §2.3.4 Octet-String-to-Elliptic-Curve-Point Conversion, with the
/// compressed form refused (choice 7). `None` is "invalid".
pub open spec fn os2p(c: Curve, m: Seq<u8>) -> Option<Point> {
    if m.len() == 1 && m[0] == 0x00 {
        // 1. "If M = 00, output P = O."
        Some(Point::Infinity)
    } else if m.len() == c.octets + 1 {
        // 2. The compressed form (`02`, `03`): refused (choice 7).
        None
    } else if m.len() == 2 * c.octets + 1 {
        // 3.1. "Parse M = W || X || Y as a single octet W followed by
        //      ⌈(log2 q)/8⌉ octets X followed by ⌈(log2 q)/8⌉ octets Y."
        let w = m[0];
        let xs = m.subrange(1, 1 + c.octets as int);
        let ys = m.subrange(1 + c.octets as int, 1 + 2 * c.octets as int);
        if w != 0x04 {
            // 3.2. "Check that W = 04. If W ≠ 04, output 'invalid' and stop."
            None
        } else {
            // 3.3. Convert X to a field element x_P (§2.3.6), else invalid.
            // 3.4. Convert Y to a field element y_P (§2.3.6), else invalid.
            match (os2fe(c, xs), os2fe(c, ys)) {
                (Some(x), Some(y)) =>
                // 3.5. "Check that P = (x_P, y_P) satisfies the defining
                //      equation of the elliptic curve."
                if satisfies_equation(c, x, y) {
                    // 3.6. "Output P = (x_P, y_P)."
                    Some(Point::Affine { x, y })
                } else {
                    None
                },
                _ => None,
            }
        }
    } else {
        // The input condition of §2.3.4 (one of three lengths) is not met.
        None
    }
}

// ---------------------------------------------------------------------
// Public key validation (SP 800-186 D.1.1.1, SEC 1 §3.2.2.1).
// ---------------------------------------------------------------------

/// SP 800-186 Appendix D.1.1.1 Partial Public Key Validation (identical to
/// SEC 1 §3.2.2.1 steps 1 and 2 for a prime field). The check `nQ = O`
/// (SEC 1 §3.2.2.1 step 4) is omitted because h = 1 (choice 8).
pub open spec fn public_key_valid(c: Curve, q: Point) -> bool {
    match q {
        // 1. "If Q is the point at infinity, output REJECT."
        Point::Infinity => false,
        Point::Affine { x, y } =>
        // 2. "Verify that x and y are integers in the interval [0, p-1]."
        // 3. "Verify that (x, y) is a point on W_a,b by checking that (x, y)
        //    satisfies the defining equation y^2 = x^3 + ax + b, where
        //    computations are carried out in GF(p)."
        // 4. "Otherwise, output ACCEPT."
        x < c.p && y < c.p && satisfies_equation(c, x, y),
    }
}

/// The public key Q as the octet string `q` (an ECPoint): converted by SEC 1
/// §2.3.4 ([`os2p`]), then validated ([`public_key_valid`]). `None` rejects.
pub open spec fn decode_public_key(c: Curve, q: Seq<u8>) -> Option<Point> {
    match os2p(c, q) {
        Some(pt) => if public_key_valid(c, pt) {
            Some(pt)
        } else {
            None
        },
        None => None,
    }
}

// ---------------------------------------------------------------------
// FIPS 186-5 §6.4.2.
// ---------------------------------------------------------------------

/// The step that rejected a signature (modelling choice 12). `Key` is the
/// validity check of Q that FIPS 186-5 §6.4.2's preamble puts before step 1.
/// Steps 2, 3, 5, 7 and 8 cannot reject. `S6` also covers a failed division
/// inside the group law, `S4` a failed inverse of s.
pub enum Step {
    /// The public key Q is not a valid point (preamble of §6.4.2).
    Key,
    /// Step 1: r or s is not an integer in [1, n - 1].
    S1,
    /// Step 4: s has no inverse mod n.
    S4,
    /// Step 6: R1 is the point at infinity (or a group operation failed).
    S6,
    /// Step 9: r ≠ r1 mod n.
    S9,
}

/// The integer `e` of step 3: "Derive the integer e from H as follows".
/// `h` is the digest H as octets; the bit string H has `hashlen = 8 |h|`
/// bits (choice 1).
pub open spec fn derive_e(c: Curve, h: Seq<u8>) -> nat {
    let hbits = octets_to_bits(h);
    let hashlen = hbits.len();
    // 3a. "If ⌈log2(n)⌉ ≥ hashlen, set E = H. Otherwise, set E equal to the
    //      leftmost ⌈log2(n)⌉ bits of H."
    let e_bits = if ceil_log2(c.n) >= hashlen {
        hbits
    } else {
        hbits.take(ceil_log2(c.n) as int)
    };
    // 3b. (printed "a.") "Convert the bit string E to the integer e as
    //      specified in Appendix B.2.1."
    bits_to_int(e_bits)
}

/// `R1 = [u]G + [v]Q` (step 6), by choices 5 and 6.
pub open spec fn compute_r1(c: Curve, u: nat, v: nat, q: Point) -> Option<Point> {
    match (scalar_mul(c, u, base_point(c)), scalar_mul(c, v, q)) {
        (Some(ug), Some(vq)) => ec_add(c, ug, vq),
        _ => None,
    }
}

/// FIPS 186-5 §6.4.2 ECDSA Signature Verification Algorithm (printed page
/// 25), <https://doi.org/10.6028/NIST.FIPS.186-5>.
///
/// Inputs: the domain parameters D (`c`), the digest H of the message
/// (choice 1), the pair of integers (r, s) and the purported verification key
/// Q as an octet string `q`. `Ok(())` is "accept"; `Err(step)` is "reject"
/// at that step.
pub open spec fn ecdsa_verify_steps(c: Curve, h: Seq<u8>, r: nat, s: nat, q: Seq<u8>) -> Result<
    (),
    Step,
> {
    // Preamble: "The validity of the public key Q should also be checked (see
    // Appendix D.1 of SP 800-186)." (choice 8)
    match decode_public_key(c, q) {
        None => Err(Step::Key),
        Some(qp) =>
        // 1. "Verify that both r and s are integers in the interval
        //    [1, n - 1]. Output 'reject' if verification fails."
        if !(1 <= r && r <= c.n - 1 && 1 <= s && s <= c.n - 1) {
            Err(Step::S1)
        } else {
            // 2. "Compute H = Hash(M) ..." Folded: H is the input (choice 1).
            // 3. "Derive the integer e from H as follows: ..."
            let e = derive_e(c, h);
            // 4. "Compute s^-1 mod n using the routine in Appendix B.1."
            //    (choice 3)
            match inv(c.n, s) {
                None => Err(Step::S4),
                Some(w) => {
                    // 5. "Compute u = e · s^-1 mod n and v = r · s^-1 mod n."
                    let u = e * w % c.n;
                    let v = r * w % c.n;
                    // 6. "Compute R1 = [u]G + [v]Q. Output 'reject' if R1 is
                    //    the identity element (the point at infinity)."
                    match compute_r1(c, u, v, qp) {
                        None => Err(Step::S6),
                        Some(Point::Infinity) => Err(Step::S6),
                        // 7. "Set xR to the x-coordinate of the affine
                        //    representation of R1 = (xR, yR)."
                        Some(Point::Affine { x: x_r, y: y_r }) => {
                            // 8. "Convert the field element xR to the integer
                            //    r1, using the conversion routine in SP
                            //    800-186, Appendix F.1." F.1 step 1: for an
                            //    odd prime q, x = a (choice 11).
                            let r1 = x_r;
                            // 9. "Verify that r = r1 mod n. Output 'reject'
                            //    if verification fails; output 'accept'
                            //    otherwise."
                            if r == r1 % c.n {
                                Ok(())
                            } else {
                                Err(Step::S9)
                            }
                        },
                    }
                },
            }
        },
    }
}

/// Whether FIPS 186-5 §6.4.2 outputs "accept" ([`ecdsa_verify_steps`] is
/// `Ok`).
pub open spec fn ecdsa_verify(c: Curve, h: Seq<u8>, r: nat, s: nat, q: Seq<u8>) -> bool {
    ecdsa_verify_steps(c, h, r, s, q) is Ok
}

} // verus!
