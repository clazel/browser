//! An independent transcription of ECDSA signature verification over a
//! prime-field curve, with the P-384 parameters, from SEC 1 and SP 800-186.
//! Written without reading any other specification of ECDSA in this
//! repository (`spec.rs`, `contract.rs`, `examples.rs` and the P-256 ECDSA
//! spec of `clazel-crypto` were not opened); the equivalence proof against
//! `spec.rs` is a later change by a different session, in `equivalence.rs`
//! ([`crate::equivalence::lemma_independent_equals_spec`]).
//!
//! Sources, read in full for the sections cited (the PDFs were downloaded
//! on 30 October 2026 and hashed with SHA-256):
//! - SEC 1: Elliptic Curve Cryptography, Version 2.0, 21 May 2009
//!   (Certicom Research), <https://www.secg.org/sec1-v2.pdf>,
//!   `54687189af3de645756a30a801b596fd14c6566992c13bfd58eede399f324a89`.
//!   Used: §2.2.1 (the group law), §2.3.1, §2.3.2, §2.3.4, §2.3.6, §2.3.8
//!   and §2.3.9 (conversions), §3.2.2.1 (public key validation) and §4.1.4
//!   (the verifying operation). Page numbers below are those of the
//!   document ("Page N of 138").
//! - NIST SP 800-186, "Recommendations for Discrete Logarithm-based
//!   Cryptography: Elliptic Curve Domain Parameters", February 2023,
//!   <https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-186.pdf>,
//!   `53c7cf3340528aaa0a7bbeaef947f2099568192367d4341a7d4abceb55f78432`.
//!   Used: §3.2.1.4 (P-384: p, n, h, a, b, Gx, Gy). The task named
//!   "§3.2.1"; P-384 is §3.2.1.4. The constants below were typed in hex from
//!   the document's grouped hex, and checked (outside this file, with
//!   arbitrary-precision arithmetic) against the document's decimal values,
//!   against `p = 2^384 - 2^128 - 2^96 + 2^32 - 1`, and for `G` on the
//!   curve.
//! - Hankerson, Menezes, Vanstone, *Guide to Elliptic Curve Cryptography*
//!   (Springer, 2004): **not obtained**. The book is not legitimately
//!   accessible to this session, so nothing here cites §3.1.2 or Algorithm
//!   4.30; the group law is from SEC 1 §2.2.1 and the verification from
//!   SEC 1 §4.1.4 alone. This file is therefore a single-source
//!   transcription (SEC 1), not two-source.
//!
//! Shared with `spec.rs`, not independent (these were given to the author
//! as the common interface, so that the two files are comparable; the
//! equivalence proof relies on them being the same, and a mistake in one of
//! them is therefore not caught by it):
//! 1. The input is the digest `H` (0 to 64 octets), not the message `M`;
//!    §4.1.4 step 2 (the hash) is folded.
//! 2. `r` and `s` are `nat`s. The public key `Q` is an octet string.
//! 3. Division modulo `m` (`m` = `p` or `n`) is `inv(m, a)` below:
//!    `Some(a^(m-2) mod m)` if `a * a^(m-2) mod m = 1`, else `None`. A `None`
//!    anywhere makes the signature invalid.
//! 4. The scalar product `kP` is MSB-first double-and-add over the binary
//!    expansion of `k`.
//! 5. `u1 G + u2 Q` is the sum of two separately computed products.
//! 6. Only the uncompressed form `04 || X || Y` of a public key is accepted:
//!    the point at infinity and the compressed forms are refused. (SEC 1's
//!    "hybrid" forms are not in its §2.3.4 and do not arise.)
//! 7. §3.2.2.1 step 4, `nQ = O`, is omitted: the cofactor is 1 (below).
//! 8. The curve is a value ([`Curve`]) so that a small curve can be used.
//!
//! Modelling choices of this file (the shared ones above are not repeated):
//! - A bit string is a `Seq<bool>`, index 0 leftmost (§2.3.2: "B = B0 B1
//!   ... Bblen-1"), and an octet string a `Seq<u8>`. §4.1.4 step 3 goes
//!   through the bit strings exactly as written ([`octets_to_bits`],
//!   [`bits_to_octets`], [`octets_to_integer`]).
//! - `ceil(log2 x)` is [`ceil_log2`], the least `k` with `2^k >= x`, and
//!   the octet length `ceil((log2 q) / 8)` of a field element is
//!   `ceil(ceil(log2 q) / 8)` ([`field_octets`]), the same number.
//! - The point `O` is the constructor [`EcPoint::O`]; the other points are
//!   `Aff { x, y }` with both coordinates in `[0, p-1]`. The group law
//!   returns `Option<EcPoint>` only because of shared convention 3: it is
//!   `None` exactly when an `inv` is `None`, which cannot happen for a
//!   prime `p` and reduced operands; the type makes the totality visible.
//! - Field elements of Fp are naturals in `[0, p-1]` (§2.3.9 step 1: "no
//!   conversion is required"), subtraction is done in `int` and reduced
//!   with Euclidean `%` ([`fmod`]).
//! - §2.3.4 and §2.3.6 take their input octet string "of length ...";
//!   an input of any other length is outside their domain and is
//!   "invalid" here, as is a field-element input not of length `mlen`.
//! - SEC 1 §2.2.1 rule 3 ("two points with the same x-coordinates when the
//!   points are either distinct or have y-coordinate 0") is written as
//!   stated, with `y1 != y2 || y1 == 0`, not as "y2 = -y1": for points on
//!   the curve the two agree, and [`add`] does not assume its operands lie
//!   on it.
//! - The domain-parameter record also carries `h` (SEC 1's `T = (p, a, b,
//!   G, n, h)`); nothing in verification reads it, other than the omitted
//!   check 7.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Domain parameters (SEC 1 §3.1.1: T = (p, a, b, G, n, h)).
// ---------------------------------------------------------------------

/// Elliptic curve domain parameters over Fp: `p`, the coefficients `a` and
/// `b` of `y^2 = x^3 + a x + b`, the base point `G = (gx, gy)`, its order
/// `n` and the cofactor `h`.
pub struct Curve {
    /// The prime `p` of the field Fp.
    pub p: nat,
    /// The coefficient `a`, in `[0, p-1]`.
    pub a: nat,
    /// The coefficient `b`, in `[0, p-1]`.
    pub b: nat,
    /// The x-coordinate of the base point `G`.
    pub gx: nat,
    /// The y-coordinate of the base point `G`.
    pub gy: nat,
    /// The order `n` of `G`.
    pub n: nat,
    /// The cofactor `h`.
    pub h: nat,
}

/// An elliptic curve point: the point at infinity `O`, or `(x, y)`.
pub enum EcPoint {
    /// The point at infinity.
    O,
    /// The point `(x, y)`, both coordinates in `[0, p-1]`.
    Aff {
        /// The x-coordinate.
        x: nat,
        /// The y-coordinate.
        y: nat,
    },
}

/// SP 800-186 §3.2.1.4, P-384: `h = 1`, `a = -3`, and the hex values of
/// the document. `p = 2^384 - 2^128 - 2^96 + 2^32 - 1`.
pub open spec fn p384() -> Curve {
    Curve {
        p: 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_fffffffe_ffffffff_00000000_00000000_ffffffffnat,
        // a = -3 (mod p), whose hex the document gives as ...fffffffc.
        a: 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_fffffffe_ffffffff_00000000_00000000_fffffffcnat,
        b: 0xb3312fa7_e23ee7e4_988e056b_e3f82d19_181d9c6e_fe814112_0314088f_5013875a_c656398d_8a2ed19d_2a85c8ed_d3ec2aefnat,
        gx: 0xaa87ca22_be8b0537_8eb1c71e_f320ad74_6e1d3b62_8ba79b98_59f741e0_82542a38_5502f25d_bf55296c_3a545e38_72760ab7nat,
        gy: 0x3617de4a_96262c6f_5d9e98bf_9292dc29_f8f41dbd_289a147c_e9da3113_b5f0b8c0_0a60b1ce_1d7e819d_7a431d7c_90ea0e5fnat,
        n: 0xffffffff_ffffffff_ffffffff_ffffffff_ffffffff_ffffffff_c7634d81_f4372ddf_581a0db2_48b0a77a_ecec196a_ccc52973nat,
        h: 1nat,
    }
}

// ---------------------------------------------------------------------
// Arithmetic helpers.
// ---------------------------------------------------------------------

/// `b^e` by its recursive definition (no reduction).
pub open spec fn power(b: nat, e: nat) -> nat
    decreases e,
{
    if e == 0 {
        1
    } else {
        b * power(b, (e - 1) as nat)
    }
}

/// Shared convention 3: division modulo `m`. `Some(a^(m-2) mod m)` if that
/// is the inverse of `a`, else `None`.
pub open spec fn inv(m: nat, a: nat) -> Option<nat> {
    if (a * power(a, (m - 2) as nat)) % m == 1 {
        Some(power(a, (m - 2) as nat) % m)
    } else {
        None
    }
}

/// `v mod p` for an integer `v`, in `[0, p-1]` (`p > 0`).
pub open spec fn fmod(v: int, p: nat) -> nat {
    (v % (p as int)) as nat
}

/// `ceil(log2 x)`: the least `k` with `2^k >= x`. (`ceil(log2 x) = 1 +
/// ceil(log2 ceil(x/2))` for `x >= 2`.)
pub open spec fn ceil_log2(x: nat) -> nat
    decreases x,
{
    if x <= 1 {
        0
    } else {
        1 + ceil_log2(((x + 1) / 2) as nat)
    }
}

/// `mlen = ceil((log2 q) / 8)`, the length in octets of a field element
/// (§2.3.4, §2.3.6) for `q = p`.
pub open spec fn field_octets(c: Curve) -> nat {
    (ceil_log2(c.p) + 7) / 8
}

// ---------------------------------------------------------------------
// §2.3 Data types and conversions.
// ---------------------------------------------------------------------

/// The value of a bit string read as a binary numeral, leftmost bit the
/// most significant: the sum of `2^(blen-1-i) B_i`.
pub open spec fn bits_value(b: Seq<bool>) -> nat
    decreases b.len(),
{
    if b.len() == 0 {
        0
    } else {
        2 * bits_value(b.drop_last()) + (if b.last() { 1nat } else { 0nat })
    }
}

/// §2.3.2 octet-string-to-bit-string conversion (page 10).
/// Input: octet string `M` of `mlen` octets. Output: a bit string `B` of
/// `blen = 8 mlen` bits.
pub open spec fn octets_to_bits(m: Seq<u8>) -> Seq<bool> {
    // 1. "For 0 <= i <= mlen-1, set: B_8i B_8i+1 ... B_8i+7 = M_i." The
    //    octet's bits are written most significant first, so bit j of M_i
    //    (j = 0 leftmost) is set when (M_i div 2^(7-j)) is odd.
    Seq::new(
        8 * m.len(),
        |k: int| (m[k / 8] as nat / power(2, (7 - k % 8) as nat)) % 2 == 1,
    )
    // 2. "Output B."
}

/// §2.3.1 bit-string-to-octet-string conversion (page 9).
/// Input: a bit string `B` of length `blen`. Output: an octet string `M` of
/// length `mlen = ceil(blen / 8)`.
pub open spec fn bits_to_octets(b: Seq<bool>) -> Seq<u8> {
    let blen = b.len();
    let mlen = (blen + 7) / 8;
    // Steps 1 and 2 together: M_i (i > 0) are the octets taken from the
    // right end of B, and M_0 has its leftmost 8 mlen - blen bits 0 and the
    // rest B_0 ... . That is the same as padding B with 8 mlen - blen zero
    // bits on the left ("pad the bit string with 0's on the left", the
    // informal description) and cutting octets of 8 bits.
    let padded = Seq::new((8 * mlen - blen) as nat, |i: int| false) + b;
    // 3. "Output M."
    Seq::new(mlen, |i: int| (bits_value(padded.subrange(8 * i, 8 * i + 8)) % 256) as u8)
}

/// §2.3.8 octet-string-to-integer conversion (page 14).
/// Input: an octet string `M` of `mlen` octets. Output: an integer `x`.
pub open spec fn octets_to_integer(m: Seq<u8>) -> nat
    decreases m.len(),
{
    // 1. "View M_i as an integer in the range [0, 255] and set
    //    x = sum over i of 2^(8 (mlen-1-i)) M_i." The first term is
    //    peeled off.
    if m.len() == 0 {
        0
    } else {
        (m[0] as nat) * power(256, (m.len() - 1) as nat) + octets_to_integer(m.skip(1))
    }
    // 2. "Output x."
}

/// §2.3.6 octet-string-to-field-element conversion (page 13), `q = p`.
/// Input: `M` of `mlen = ceil((log2 q) / 8)` octets. Output: `a` in Fq, or
/// "invalid" (`None`).
pub open spec fn octets_to_field_element(c: Curve, m: Seq<u8>) -> Option<nat> {
    if m.len() != field_octets(c) {
        // Outside the domain of the conversion (header).
        None
    } else {
        // 1. "If q = p is an odd prime, then a needs to be an integer in
        //    the interval [0, p-1]. Convert M to an integer a using ...
        //    Section 2.3.8. Output 'invalid' and stop if a does not lie in
        //    the interval [0, p-1], otherwise output a."
        let a = octets_to_integer(m);
        if a <= c.p - 1 {
            Some(a)
        } else {
            None
        }
        // 2. (q = 2^m: not applicable.)
    }
}

/// §2.3.9 field-element-to-integer conversion (page 14), `q = p`.
pub open spec fn field_element_to_integer(a: nat) -> nat {
    // 1. "If q = p is an odd prime, then a must be an integer in the
    //    interval [0, p-1]. Output x = a."
    a
}

/// A point `(x, y)` satisfies the defining equation of the curve
/// (§2.2.1: `y^2 = x^3 + a x + b (mod p)`).
pub open spec fn on_curve(c: Curve, x: nat, y: nat) -> bool {
    (y * y) % c.p == (x * x * x + c.a * x + c.b) % c.p
}

/// §2.3.4 octet-string-to-elliptic-curve-point conversion (pages 11-12),
/// restricted by shared convention 6. Input: `M`, the single octet 00, an
/// octet string of length `mlen + 1` (compressed) or one of length
/// `2 mlen + 1`. Output: a point `P`, or "invalid" (`None`).
pub open spec fn octets_to_point(c: Curve, m: Seq<u8>) -> Option<EcPoint> {
    let mlen = field_octets(c);
    if m.len() == 1 && m[0] == 0x00u8 {
        // 1. "If M = 00, output P = O." Refused (convention 6): the point at
        //    infinity is not an acceptable public key.
        None
    } else if m.len() == mlen + 1 {
        // 2. The compressed form. Refused (convention 6): 2.1 to 2.5 are
        //    not transcribed.
        None
    } else if m.len() == 2 * mlen + 1 {
        // 3.1. "Parse M = W || X || Y as a single octet W followed by
        //      mlen octets X followed by mlen octets Y."
        let w = m[0];
        let x_oct = m.subrange(1, 1 + mlen as int);
        let y_oct = m.subrange(1 + mlen as int, 1 + 2 * mlen as int);
        // 3.2. "Check that W = 04. If W != 04, output 'invalid' and stop."
        if w != 0x04u8 {
            None
        } else {
            // 3.3. "Convert X to a field element xP of Fq using the
            //      conversion routine specified in Section 2.3.6. Output
            //      'invalid' and stop if the routine outputs 'invalid'."
            match octets_to_field_element(c, x_oct) {
                None => None,
                Some(x_p) => {
                    // 3.4. The same for Y, giving yP.
                    match octets_to_field_element(c, y_oct) {
                        None => None,
                        Some(y_p) => {
                            // 3.5. "Check that P = (xP, yP) satisfies the
                            //      defining equation of the elliptic curve."
                            if !on_curve(c, x_p, y_p) {
                                None
                            } else {
                                // 3.6. "Output P = (xP, yP)."
                                Some(EcPoint::Aff { x: x_p, y: y_p })
                            }
                        },
                    }
                },
            }
        }
    } else {
        // M is not of one of the three permitted forms: outside the domain
        // of the conversion (header).
        None
    }
}

// ---------------------------------------------------------------------
// §2.2.1 Elliptic curves over Fp: the addition rule and kP.
// ---------------------------------------------------------------------

/// The sum of two points, by the addition rules of §2.2.1 (pages 6-7), in
/// the order they are listed. `None` only if an `inv` is `None`
/// (convention 3).
pub open spec fn add(c: Curve, p1: EcPoint, p2: EcPoint) -> Option<EcPoint> {
    match (p1, p2) {
        // 1. "Rule to add the point at infinity to itself: O + O = O."
        (EcPoint::O, EcPoint::O) => Some(EcPoint::O),
        // 2. "Rule to add the point at infinity to any other point:
        //    (x, y) + O = O + (x, y) = (x, y)."
        (EcPoint::O, EcPoint::Aff { x, y }) => Some(EcPoint::Aff { x, y }),
        (EcPoint::Aff { x, y }, EcPoint::O) => Some(EcPoint::Aff { x, y }),
        (EcPoint::Aff { x: x1, y: y1 }, EcPoint::Aff { x: x2, y: y2 }) => {
            if x1 == x2 && (y1 != y2 || y1 == 0) {
                // 3. "Rule to add two points with the same x-coordinates
                //    when the points are either distinct or have
                //    y-coordinate 0: (x, y) + (x, -y) = O."
                Some(EcPoint::O)
            } else if x1 != x2 {
                // 4. "Rule to add two points with different x-coordinates:
                //    x3 = lambda^2 - x1 - x2, y3 = lambda (x1 - x3) - y1
                //    (mod p), lambda = (y2 - y1) / (x2 - x1) (mod p)."
                match inv(c.p, fmod(x2 as int - x1 as int, c.p)) {
                    None => None,
                    Some(d) => {
                        let lambda = (fmod(y2 as int - y1 as int, c.p) * d) % c.p;
                        let x3 = fmod((lambda * lambda) as int - x1 as int - x2 as int, c.p);
                        let y3 = fmod(lambda as int * (x1 as int - x3 as int) - y1 as int, c.p);
                        Some(EcPoint::Aff { x: x3, y: y3 })
                    },
                }
            } else {
                // 5. "Rule to add a point to itself (double a point): let
                //    (x1, y1) be a point with y1 != 0. Then x3 = lambda^2
                //    - 2 x1, y3 = lambda (x1 - x3) - y1 (mod p), lambda =
                //    (3 x1^2 + a) / (2 y1) (mod p)." Here x1 = x2 and
                //    y1 = y2 != 0, by the condition of rule 3 failing.
                match inv(c.p, (2 * y1) % c.p) {
                    None => None,
                    Some(d) => {
                        let lambda = ((3 * x1 * x1 + c.a) * d) % c.p;
                        let x3 = fmod((lambda * lambda) as int - 2 * x1 as int, c.p);
                        let y3 = fmod(lambda as int * (x1 as int - x3 as int) - y1 as int, c.p);
                        Some(EcPoint::Aff { x: x3, y: y3 })
                    },
                }
            }
        },
    }
}

/// Scalar multiplication `kP` (§2.2.1: "adding P to itself k times"),
/// computed as shared convention 4 says: MSB-first double-and-add, i.e. the
/// product for the leading bits of `k` (`k div 2`) is doubled and, if the
/// last bit is 1, `P` is added. `0 P = O`.
pub open spec fn scalar_mul(c: Curve, k: nat, pt: EcPoint) -> Option<EcPoint>
    decreases k,
{
    if k == 0 {
        Some(EcPoint::O)
    } else {
        match scalar_mul(c, k / 2, pt) {
            None => None,
            Some(a) => {
                // double
                match add(c, a, a) {
                    None => None,
                    Some(d) => {
                        if k % 2 == 1 {
                            add(c, d, pt)
                        } else {
                            Some(d)
                        }
                    },
                }
            },
        }
    }
}

// ---------------------------------------------------------------------
// §3.2.2.1 Elliptic curve public key validation primitive.
// ---------------------------------------------------------------------

/// §3.2.2.1 (page 24) for `T` over Fp. Returns true for "valid".
pub open spec fn public_key_validation(c: Curve, q: EcPoint) -> bool {
    match q {
        // 1. "Check that Q != O."
        EcPoint::O => false,
        EcPoint::Aff { x, y } => {
            // 2. "check that xQ and yQ are integers in the interval
            //    [0, p-1], and that y^2 = x^3 + a x + b (mod p)."
            x <= c.p - 1 && y <= c.p - 1 && on_curve(c, x, y)
            // 3. (F2m: not applicable.)
            // 4. "Check that nQ = O." Omitted: h = 1, so it is implied by
            //    steps 1-3 (SEC 1 page 25: "if h = 1, then nQ = O is
            //    implied by the checks in Steps 2 and 3"); header, item 7.
            // 5. "If any of the checks fail, output 'invalid', otherwise
            //    output 'valid'." Folded: the conjunction above.
        },
    }
}

/// The public key `Q_U` as established by the setup and key deployment
/// procedures that §4.1.4 refers to: the octet string converted by §2.3.4
/// and validated by §3.2.2.1. `None` if either fails.
pub open spec fn decode_public_key(c: Curve, q: Seq<u8>) -> Option<EcPoint> {
    match octets_to_point(c, q) {
        None => None,
        Some(pt) => if public_key_validation(c, pt) {
            Some(pt)
        } else {
            None
        },
    }
}

// ---------------------------------------------------------------------
// §4.1.4 Verifying operation.
// ---------------------------------------------------------------------

/// §4.1.4 step 3: "Derive an integer e from H" (page 46).
pub open spec fn derive_e(c: Curve, h: Seq<u8>) -> nat {
    // hashlen is h.len(); 8(hashlen) is the length of the bit string.
    // 3.1. "Convert the octet string H to a bit string H using the
    //      conversion routine specified in Section 2.3.2."
    let h_bits = octets_to_bits(h);
    // 3.2. "Set E = H if ceil(log2 n) >= 8(hashlen), and set E equal to the
    //      leftmost ceil(log2 n) bits of H if ceil(log2 n) < 8(hashlen)."
    let e_bits = if ceil_log2(c.n) >= 8 * h.len() {
        h_bits
    } else {
        h_bits.subrange(0, ceil_log2(c.n) as int)
    };
    // 3.3. "Convert the bit string E to an octet string E using the
    //      conversion routine specified in Section 2.3.1."
    let e_oct = bits_to_octets(e_bits);
    // 3.4. "Convert the octet string E to an integer e using the
    //      conversion routine specified in Section 2.3.8."
    octets_to_integer(e_oct)
}

/// SEC 1 §4.1.4, the verifying operation (pages 46-47), with the digest `H`
/// in place of the message (convention 1). Returns true for "valid".
pub open spec fn ecdsa_verify(c: Curve, h: Seq<u8>, r: nat, s: nat, q: Seq<u8>) -> bool {
    // The public key U's, established before the operation (see
    // `decode_public_key`).
    match decode_public_key(c, q) {
        None => false,
        Some(q_u) => {
            // 1. "If r and s are not both integers in the interval
            //    [1, n-1], output 'invalid' and stop."
            if !(1 <= r && r <= c.n - 1 && 1 <= s && s <= c.n - 1) {
                false
            } else {
                // 2. "compute the hash value H = Hash(M)": folded, H is
                //    the input (convention 1), so "if the hash function
                //    outputs 'invalid'" cannot occur.
                // 3. "Derive an integer e from H."
                let e = derive_e(c, h);
                // 4. "Compute u1 = e s^-1 mod n and u2 = r s^-1 mod n."
                match inv(c.n, s) {
                    None => false,
                    Some(s_inv) => {
                        let u1 = (e * s_inv) % c.n;
                        let u2 = (r * s_inv) % c.n;
                        // 5. "Compute R = (xR, yR) = u1 G + u2 QU. If R = O,
                        //    output 'invalid' and stop." (Convention 5: the
                        //    two products are computed separately.)
                        let g = EcPoint::Aff { x: c.gx, y: c.gy };
                        match scalar_mul(c, u1, g) {
                            None => false,
                            Some(a) => match scalar_mul(c, u2, q_u) {
                                None => false,
                                Some(b) => match add(c, a, b) {
                                    None => false,
                                    Some(EcPoint::O) => false,
                                    Some(EcPoint::Aff { x: x_r, y: y_r }) => {
                                        // 6. "Convert the field element xR
                                        //    to an integer xR using the
                                        //    conversion routine specified
                                        //    in Section 2.3.9."
                                        let x_r_int = field_element_to_integer(x_r);
                                        // 7. "Set v = xR mod n."
                                        let v = x_r_int % c.n;
                                        // 8. "Compare v and r - if v = r,
                                        //    output 'valid', and if v != r,
                                        //    output 'invalid'."
                                        v == r
                                    },
                                },
                            },
                        }
                    },
                }
            }
        },
    }
}

// ---------------------------------------------------------------------
// Sanity checks on a tiny curve chosen by this author (not taken from any
// other file of the repository): y^2 = x^3 + 2x + 2 over F17, G = (5, 1) of
// prime order 19, h = 1. Its multiples of G, computed by hand and
// re-checked with arbitrary-precision arithmetic: G = (5,1), 2G = (6,3),
// 3G = (10,6), 7G = (0,6), 18G = (5,16), 19G = O.
// ---------------------------------------------------------------------

/// The tiny curve of the checks below.
pub open spec fn tiny() -> Curve {
    Curve { p: 17, a: 2, b: 2, gx: 5, gy: 1, n: 19, h: 1 }
}

/// A curve point conversion: 3 octets `04 || X || Y`, `mlen = 1`.
proof fn tiny_field_octets()
    ensures
        field_octets(tiny()) == 1,
        ceil_log2(17) == 5,
        ceil_log2(19) == 5,
{
    assert(field_octets(tiny()) == 1) by (compute);
    assert(ceil_log2(17) == 5) by (compute);
    assert(ceil_log2(19) == 5) by (compute);
}

/// The base point is on the curve, for both curves.
proof fn base_points_on_curve()
    ensures
        on_curve(tiny(), 5, 1),
        on_curve(p384(), p384().gx, p384().gy),
{
    assert(on_curve(tiny(), 5, 1)) by (compute);
    assert(on_curve(p384(), p384().gx, p384().gy)) by (compute);
}

/// G + G = 2G = (6, 3) (rule 5), 2G + G = 3G = (10, 6) (rule 4),
/// G + (5, 16) = O (rule 3), and O + G = G (rule 2).
proof fn tiny_group_law()
    ensures
        add(tiny(), EcPoint::Aff { x: 5, y: 1 }, EcPoint::Aff { x: 5, y: 1 })
            == Some(EcPoint::Aff { x: 6, y: 3 }),
        add(tiny(), EcPoint::Aff { x: 6, y: 3 }, EcPoint::Aff { x: 5, y: 1 })
            == Some(EcPoint::Aff { x: 10, y: 6 }),
        add(tiny(), EcPoint::Aff { x: 5, y: 1 }, EcPoint::Aff { x: 5, y: 16 })
            == Some(EcPoint::O),
        add(tiny(), EcPoint::O, EcPoint::Aff { x: 5, y: 1 })
            == Some(EcPoint::Aff { x: 5, y: 1 }),
        scalar_mul(tiny(), 7, EcPoint::Aff { x: 5, y: 1 })
            == Some(EcPoint::Aff { x: 0, y: 6 }),
        scalar_mul(tiny(), 19, EcPoint::Aff { x: 5, y: 1 }) == Some(EcPoint::O),
{
    assert(add(tiny(), EcPoint::Aff { x: 5, y: 1 }, EcPoint::Aff { x: 5, y: 1 })
        == Some(EcPoint::Aff { x: 6, y: 3 })) by (compute);
    assert(add(tiny(), EcPoint::Aff { x: 6, y: 3 }, EcPoint::Aff { x: 5, y: 1 })
        == Some(EcPoint::Aff { x: 10, y: 6 })) by (compute);
    assert(add(tiny(), EcPoint::Aff { x: 5, y: 1 }, EcPoint::Aff { x: 5, y: 16 })
        == Some(EcPoint::O)) by (compute);
    assert(add(tiny(), EcPoint::O, EcPoint::Aff { x: 5, y: 1 })
        == Some(EcPoint::Aff { x: 5, y: 1 })) by (compute);
    assert(scalar_mul(tiny(), 7, EcPoint::Aff { x: 5, y: 1 })
        == Some(EcPoint::Aff { x: 0, y: 6 })) by (compute);
    assert(scalar_mul(tiny(), 19, EcPoint::Aff { x: 5, y: 1 }) == Some(EcPoint::O)) by (compute);
}

/// Step 3 on the tiny curve: `ceil(log2 19) = 5`, so a one-octet digest
/// 0x58 = 0101 1000 is cut to its leftmost 5 bits 01011 = 11.
proof fn tiny_derive_e()
    ensures
        derive_e(tiny(), seq![0x58u8]) == 11,
        derive_e(tiny(), seq![]) == 0,
{
    assert(derive_e(tiny(), seq![0x58u8]) == 11) by (compute);
    assert(derive_e(tiny(), seq![]) == 0) by (compute);
}

/// A signature worked by hand: private key d = 7, so Q = 7G = (0, 6); digest
/// H = 58 (e = 11); nonce k = 3, R = 3G = (10, 6), r = 10; s = k^-1 (e + r
/// d) = 13 * 81 = 13 * 5 = 65 = 8 (mod 19). It is valid; s + 1 and r + 1
/// are not; neither is the same signature under a one-bit-different
/// digest, or with a compressed public key.
proof fn tiny_signature()
    ensures
        ecdsa_verify(tiny(), seq![0x58u8], 10, 8, seq![0x04u8, 0x00u8, 0x06u8]),
        !ecdsa_verify(tiny(), seq![0x58u8], 10, 9, seq![0x04u8, 0x00u8, 0x06u8]),
        !ecdsa_verify(tiny(), seq![0x58u8], 11, 8, seq![0x04u8, 0x00u8, 0x06u8]),
        !ecdsa_verify(tiny(), seq![0x60u8], 10, 8, seq![0x04u8, 0x00u8, 0x06u8]),
        !ecdsa_verify(tiny(), seq![0x58u8], 10, 8, seq![0x02u8, 0x00u8]),
        !ecdsa_verify(tiny(), seq![0x58u8], 10, 8, seq![0x00u8]),
        !ecdsa_verify(tiny(), seq![0x58u8], 10, 0, seq![0x04u8, 0x00u8, 0x06u8]),
{
    assert(ecdsa_verify(tiny(), seq![0x58u8], 10, 8, seq![0x04u8, 0x00u8, 0x06u8])) by (compute);
    assert(!ecdsa_verify(tiny(), seq![0x58u8], 10, 9, seq![0x04u8, 0x00u8, 0x06u8])) by (compute);
    assert(!ecdsa_verify(tiny(), seq![0x58u8], 11, 8, seq![0x04u8, 0x00u8, 0x06u8])) by (compute);
    assert(!ecdsa_verify(tiny(), seq![0x60u8], 10, 8, seq![0x04u8, 0x00u8, 0x06u8])) by (compute);
    assert(!ecdsa_verify(tiny(), seq![0x58u8], 10, 8, seq![0x02u8, 0x00u8])) by (compute);
    assert(!ecdsa_verify(tiny(), seq![0x58u8], 10, 8, seq![0x00u8])) by (compute);
    assert(!ecdsa_verify(tiny(), seq![0x58u8], 10, 0, seq![0x04u8, 0x00u8, 0x06u8])) by (compute);
}

} // verus!
