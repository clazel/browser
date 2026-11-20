//! SubjectPublicKeyInfo decoding and key classification, transcribed for the
//! independent decoder from these texts, each fetched from rfc-editor.org as
//! plain text (SHA-256 of the `.txt` file):
//!
//! - RFC 5280 (May 2008), §4.1, §4.1.1.2 and §4.1.2.7:
//!   `a2f2628c0a83b873fc4786abd921f9b2c02395954b655d190bf16b831633345d`.
//! - RFC 3279 (April 2002), §2.3 and §2.3.1:
//!   `6d3f19f18e17fa1c68da5aaf4021327748fabca840d7300443b77357a1fc1614`.
//! - RFC 4055 (June 2005), §1.2 and §3.1:
//!   `b8a1ef3fb135c32aed4eee121264f3ec83a46def746c8fe68e05bd1b60324e9a`.
//! - RFC 5480 (March 2009), §2, §2.1, §2.1.1, §2.1.1.1, §2.1.2 and §2.2:
//!   `593bf29fd0da2ff8b903c3ebf1c9d189a770039159e2ba46a0c3b91355037f26`.
//! - RFC 8410 (August 2018), §3 and §4:
//!   `90a0ff0b3dd661d3e26e1873f40f2ca8b41709a7bbd755a1ed3599c4746313d2`.
//! - RFC 8017 (November 2016), §3.1 and Appendix A.1.1, for what an RSA
//!   public key is: `1e72dc473d18df3fc5598cdc12795a9f18f36f1aef15abc23a55eb0d58151d11`.
//! - RFC 7748 (January 2016), §5, and RFC 8032 (January 2017), §5.1.2,
//!   §5.1.5, §5.2.2 and §5.2.5, for the key lengths RFC 8410 leaves to them:
//!   `279ca0ecc5e92e2962e27b846986aeb74729d9dd34bd4a04a362f80dcb596ad3` and
//!   `ed63657ff389301282b169b0abde9b5dd2c7e4d524fdfa5da6ff3094fc93c4c3`.
//!
//! The X.690 layer is `der.rs`, and the ASN.1 types `SubjectPublicKeyInfo`
//! and `AlgorithmIdentifier` are `structures.rs`'s, both reused unchanged.
//!
//! **Not read while writing this file.** Everything the list in
//! `independent/mod.rs` names, and in particular: everything under
//! `crates/clazel-x509/src/spki/` and `src/signature_algorithm/`; every
//! `spec.rs`, `contract.rs`, `lemmas.rs`, `exec.rs`, `examples.rs`,
//! `certificates.rs` and `theorems.rs` outside `src/independent/`;
//! `crates/clazel-x509/mutations.json`; `crates/clazel-x509/tests/`;
//! `crates/clazel-crypto/src/`; `crates/clazel-der/src/`; sections 3.5a and
//! 3.5b of `docs/phases/phase-3.md`. None of these was grepped either. SEC 1,
//! ANSI X9.62 and FIPS 186 were not read (none is an RFC); where they matter
//! the choice below says so.
//!
//! **Read.** `CLAUDE.md`; `docs/VERIFICATION.md` ("Trust without
//! reviewers"); `docs/SPEC-STYLE.md`; this crate's `lib.rs`, `Cargo.toml`
//! and `independent/mod.rs`; in `independent/`, `der.rs` (its header and
//! clauses 8.1 to 8.19), `structures.rs` (its header, the types, and the
//! decoders of `AlgorithmIdentifier` and `SubjectPublicKeyInfo`), the first
//! 200 lines of `examples.rs`, the header of `requirements.rs` and the enum
//! declarations of `extensions.rs`; and, in `xtask/src/`, the part of
//! `verus.rs` that starts Verus and the lines of `main.rs` that name it.
//!
//! Modelling choices:
//! - A refusal is `None`. [`subject_public_key`] answers "is this a
//!   SubjectPublicKeyInfo, DER-encoded, carrying a key of an algorithm in
//!   scope, encoded as its RFC says", and returns the key's classification.
//!   [`valid_subject_public_key`] adds [`public_key_requirements`], the parts
//!   of RFC 8017 §3.1's "valid RSA public key" that can be checked without
//!   factoring.
//! - The input is exactly one encoding (`parse_single`): octets after the
//!   SubjectPublicKeyInfo are refused.
//! - RFC 5280's modules use the 1988 syntax, in which neither
//!   `SubjectPublicKeyInfo` nor `AlgorithmIdentifier` has an extension
//!   marker. So `structures.rs`'s `additions` must be empty in both; a third
//!   component is refused.
//! - Algorithms in scope: `rsaEncryption` (RFC 3279 §2.3.1, RFC 4055 §1.2),
//!   `id-ecPublicKey` (RFC 5480 §2.1.1), and `id-X25519`, `id-X448`,
//!   `id-Ed25519`, `id-Ed448` (RFC 8410 §3). Every other algorithm is
//!   refused, among them `id-RSASSA-PSS` and `id-RSAES-OAEP` (RFC 4055 §1.2:
//!   decoding `RSASSA-PSS-params` with its DEFAULTs and the hash and MGF
//!   tables of RFC 4055 §2 is a separate job, left out here and named in
//!   [`classify_key`]), `id-ecDH` and `id-ecMQV` (RFC 5480 §2.1.2: "MAY be
//!   supported"), DSA and Diffie-Hellman (RFC 3279 §2.3.2 to §2.3.4).
//! - Curves in scope: secp256r1, secp384r1 and secp521r1 (P-256, P-384,
//!   P-521) of RFC 5480 §2.1.1.1. Its twelve other NIST curves, and every
//!   other named curve, are refused as unknown.
//! - `ECParameters` is a CHOICE whose only uncommented alternative is
//!   `namedCurve OBJECT IDENTIFIER`; "implicitCurve and specifiedCurve MUST
//!   NOT be used in PKIX". So the parameters must be one OBJECT IDENTIFIER
//!   (X.690 8.13: a CHOICE is encoded as its alternative); a NULL or a
//!   SEQUENCE there is refused, as is an absent one ("MUST always be
//!   present").
//! - Point forms (RFC 5480 §2.2): uncompressed (first octet 04) "MUST" be
//!   supported and compressed (02 or 03) "MAY" be. Both are accepted, and the
//!   classification records which, so that a caller that supports only the
//!   uncompressed form can refuse the other. "The hybrid form ... MUST NOT be
//!   used" and "The public key MUST be rejected if any other value is
//!   included in the first octet": every other first octet, the hybrid 06
//!   and 07 and SEC 1's single-octet 00 for the point at infinity included,
//!   is refused.
//! - Point lengths. SEC 1 §2.3.3 was not read. Its octet-string form, as the
//!   author knows it, is the first octet followed by x (compressed), or by x
//!   then y (uncompressed), each coordinate in ceil(log2(p)/8) octets. The
//!   field primes of P-256, P-384 and P-521 have 256, 384 and 521 bits (the
//!   numbers in the curves' FIPS 186 names, which RFC 5480 §2.1.1.1 quotes),
//!   so a coordinate takes 32, 48 and 66 octets: [`field_octets`]. A point of
//!   any other length is refused. That a coordinate is below p, and that the
//!   point is on the curve, are not checked: SEC 1 §2.3.4's conversion and
//!   the curve arithmetic belong to the cryptography, not to the decoding.
//! - Bit string to octets. Every algorithm in scope fills `subjectPublicKey`
//!   with whole octets: RSA (RFC 3279 §2.3.1: "The DER encoded RSAPublicKey
//!   is the value of the BIT STRING"), EC (RFC 5480 §2.2: the OCTET STRING's
//!   bits are the BIT STRING's bits, in order) and RFC 8410 §4 ("always
//!   encode the public key as an exact multiple of 8 bits"). So a non-zero
//!   unused-bits count is refused for all of them, even when DER allows it.
//! - RSA parameters. RFC 3279 §2.3.1 says "The parameters field MUST have
//!   ASN.1 type NULL", and RFC 4055 §1.2 "the parameters field MUST contain
//!   NULL". An absent field is refused, as is any field but the NULL value
//!   (X.690 8.8: universal 5, primitive, no contents octets).
//! - RSAPublicKey is decoded as DER, as one encoding filling the bit string,
//!   a SEQUENCE of exactly two INTEGERs. The INTEGERs follow X.690 8.3.2:
//!   a leading 00 octet is allowed only before an octet whose bit 8 is set,
//!   so a modulus with a leading 00 that is not needed is refused, and one
//!   whose leading octet has bit 8 set and no 00 before it is negative.
//! - RFC 8017 §3.1 defines an RSA public key's "n the RSA modulus, a
//!   positive integer" and "e the RSA public exponent, a positive integer".
//!   A modulus or exponent that is zero or negative is therefore not an RSA
//!   public key, and [`subject_public_key`] refuses it. The rest of §3.1 is
//!   about a *valid* key: [`public_key_requirements`].
//! - RFC 8410 parameters: "For all of the OIDs, the parameters MUST be
//!   absent." A present field, NULL included, is refused, although §3 notes
//!   that some systems send one.
//! - RFC 8410 key lengths. §4 leaves the key to RFC 7748 and RFC 8032:
//!   X25519 32 octets and X448 56 (RFC 7748 §5: "32-byte strings (for
//!   X25519) or 56-byte strings (for X448)"), Ed25519 32 and Ed448 57 (RFC
//!   8032 §5.1.2 and §5.2.2). Any other length is refused. The keys' own
//!   contents (RFC 8032's point decoding, RFC 7748's masking) are not checked.
//! - No minimum RSA modulus size and no curve preference: those are policy,
//!   and none of these RFCs states one as a requirement on the encoding.
//! - The key's encoded bits are kept as the bit string's octets (for RSA,
//!   the whole DER RSAPublicKey; for EC, the point with its first octet; for
//!   RFC 8410, the raw key).

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der::*;
#[cfg(verus_only)]
use super::structures::*;

verus! {

// ---------------------------------------------------------------------------
// Results
// ---------------------------------------------------------------------------

/// The named curves in scope, RFC 5480 §2.1.1.1.
pub enum NamedCurve {
    /// `secp256r1`, FIPS 186's P-256.
    P256,
    /// `secp384r1`, FIPS 186's P-384.
    P384,
    /// `secp521r1`, FIPS 186's P-521.
    P521,
}

/// The form of an elliptic curve point, RFC 5480 §2.2.
pub enum PointForm {
    /// First octet 04: x and y.
    Uncompressed,
    /// First octet 02 or 03: x, and the parity of y in the first octet.
    Compressed,
}

/// A classified subject public key.
pub enum PublicKey {
    /// `rsaEncryption`, RFC 3279 §2.3.1.
    Rsa {
        /// `modulus`, the RSA modulus n.
        modulus: int,
        /// `publicExponent`, the RSA public exponent e.
        public_exponent: int,
        /// The bit string's octets: the DER RSAPublicKey.
        key: Seq<u8>,
    },
    /// `id-ecPublicKey` with a `namedCurve`, RFC 5480 §2.1.1.
    Ec {
        /// The `namedCurve`.
        curve: NamedCurve,
        /// Which form the point is in.
        form: PointForm,
        /// The bit string's octets: the ECPoint, first octet included.
        point: Seq<u8>,
    },
    /// `id-Ed25519`, RFC 8410 §3.
    Ed25519 {
        /// The 32-octet key.
        key: Seq<u8>,
    },
    /// `id-Ed448`, RFC 8410 §3.
    Ed448 {
        /// The 57-octet key.
        key: Seq<u8>,
    },
    /// `id-X25519`, RFC 8410 §3.
    X25519 {
        /// The 32-octet key.
        key: Seq<u8>,
    },
    /// `id-X448`, RFC 8410 §3.
    X448 {
        /// The 56-octet key.
        key: Seq<u8>,
    },
}

// ---------------------------------------------------------------------------
// Object identifiers
// ---------------------------------------------------------------------------

/// RFC 3279 §2.3.1: `rsaEncryption ::= { pkcs-1 1 }`, with
/// `pkcs-1 ::= { iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1) 1 }`.
pub open spec fn id_rsa_encryption() -> Seq<nat> {
    seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 1nat]
}

/// RFC 4055 §3.1: `id-RSASSA-PSS ::= { pkcs-1 10 }`. Out of scope; named so
/// that its refusal is visible.
pub open spec fn id_rsassa_pss() -> Seq<nat> {
    seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 10nat]
}

/// RFC 5480 §2.1.1: `id-ecPublicKey ::= { iso(1) member-body(2) us(840)
/// ansi-X9-62(10045) keyType(2) 1 }`.
pub open spec fn id_ec_public_key() -> Seq<nat> {
    seq![1nat, 2nat, 840nat, 10045nat, 2nat, 1nat]
}

/// RFC 5480 §2.1.1.1: `secp256r1 ::= { iso(1) member-body(2) us(840)
/// ansi-X9-62(10045) curves(3) prime(1) 7 }`.
pub open spec fn id_secp256r1() -> Seq<nat> {
    seq![1nat, 2nat, 840nat, 10045nat, 3nat, 1nat, 7nat]
}

/// RFC 5480 §2.1.1.1: `secp384r1 ::= { iso(1) identified-organization(3)
/// certicom(132) curve(0) 34 }`.
pub open spec fn id_secp384r1() -> Seq<nat> {
    seq![1nat, 3nat, 132nat, 0nat, 34nat]
}

/// RFC 5480 §2.1.1.1: `secp521r1 ::= { iso(1) identified-organization(3)
/// certicom(132) curve(0) 35 }`.
pub open spec fn id_secp521r1() -> Seq<nat> {
    seq![1nat, 3nat, 132nat, 0nat, 35nat]
}

/// RFC 8410 §3: `id-X25519 ::= { 1 3 101 110 }`.
pub open spec fn id_x25519() -> Seq<nat> {
    seq![1nat, 3nat, 101nat, 110nat]
}

/// RFC 8410 §3: `id-X448 ::= { 1 3 101 111 }`.
pub open spec fn id_x448() -> Seq<nat> {
    seq![1nat, 3nat, 101nat, 111nat]
}

/// RFC 8410 §3: `id-Ed25519 ::= { 1 3 101 112 }`.
pub open spec fn id_ed25519() -> Seq<nat> {
    seq![1nat, 3nat, 101nat, 112nat]
}

/// RFC 8410 §3: `id-Ed448 ::= { 1 3 101 113 }`.
pub open spec fn id_ed448() -> Seq<nat> {
    seq![1nat, 3nat, 101nat, 113nat]
}

// ---------------------------------------------------------------------------
// RFC 5280 §4.1.2.7 and §4.1.1.2: the structure
// ---------------------------------------------------------------------------

/// X.690 8.8 with X.680 Table 1: `t` is the NULL value. 8.8.1 "primitive";
/// 8.8.2 "The contents octets shall not contain any octets."
pub open spec fn is_null(t: Tlv) -> bool {
    has_tag(t, class_universal(), 5, false) && t.contents.len() == 0
}

/// RFC 5280 §4.1 `SubjectPublicKeyInfo ::= SEQUENCE { algorithm
/// AlgorithmIdentifier, subjectPublicKey BIT STRING }`, with §4.1.1.2's
/// `AlgorithmIdentifier ::= SEQUENCE { algorithm OBJECT IDENTIFIER,
/// parameters ANY DEFINED BY algorithm OPTIONAL }`, as the whole of `input`
/// in DER. Neither type has an extension marker in RFC 5280's 1988 module,
/// so no component may follow the known ones.
pub open spec fn decode_spki(input: Seq<u8>) -> Option<SubjectPublicKeyInfo> {
    match parse_single(input) {
        None => None,
        Some(t) => match decode_subject_public_key_info(t) {
            None => None,
            Some(spki) => {
                if spki.additions.len() != 0 || spki.algorithm.additions.len() != 0 {
                    None
                } else {
                    Some(spki)
                }
            },
        },
    }
}

/// The octets of a bit string that holds whole octets (unused bits 0); see
/// "Bit string to octets" at the top of this file.
pub open spec fn whole_octets(b: BitString) -> Option<Seq<u8>> {
    if b.unused != 0 {
        None
    } else {
        Some(b.octets)
    }
}

// ---------------------------------------------------------------------------
// RFC 3279 §2.3.1 and RFC 4055 §1.2: RSA
// ---------------------------------------------------------------------------

/// RFC 3279 §2.3.1 `RSAPublicKey ::= SEQUENCE { modulus INTEGER,
/// publicExponent INTEGER }`, as the whole of `octets` in DER: (modulus,
/// publicExponent).
pub open spec fn decode_rsa_public_key(octets: Seq<u8>) -> Option<(int, int)> {
    match parse_single(octets) {
        None => None,
        Some(t) => match sequence_elements(t) {
            None => None,
            Some(e) => {
                // Exactly the two components; no extension marker.
                if e.len() != 2 {
                    None
                } else {
                    match (decode_integer(e[0]), decode_integer(e[1])) {
                        (Some(modulus), Some(public_exponent)) => Some((modulus, public_exponent)),
                        _ => None,
                    }
                }
            },
        },
    }
}

/// RFC 3279 §2.3.1, an `rsaEncryption` key from its parameters and bit
/// string.
pub open spec fn rsa_key(parameters: Option<Tlv>, subject_public_key: BitString) -> Option<
    PublicKey,
> {
    // "The parameters field MUST have ASN.1 type NULL for this algorithm
    // identifier." (RFC 4055 §1.2: "the parameters field MUST contain
    // NULL".)
    match parameters {
        None => None,
        Some(p) => {
            if !is_null(p) {
                None
            } else {
                // "The DER encoded RSAPublicKey is the value of the BIT
                // STRING subjectPublicKey."
                match whole_octets(subject_public_key) {
                    None => None,
                    Some(key) => match decode_rsa_public_key(key) {
                        None => None,
                        Some((modulus, public_exponent)) => {
                            // RFC 8017 §3.1: "n the RSA modulus, a positive
                            // integer"; "e the RSA public exponent, a
                            // positive integer".
                            if modulus <= 0 || public_exponent <= 0 {
                                None
                            } else {
                                Some(PublicKey::Rsa { modulus, public_exponent, key })
                            }
                        },
                    },
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// RFC 5480 §2.1.1 and §2.2: elliptic curve keys
// ---------------------------------------------------------------------------

/// RFC 5480 §2.1.1.1: the curve a `namedCurve` names, among those in scope.
pub open spec fn named_curve(oid: Seq<nat>) -> Option<NamedCurve> {
    if oid == id_secp256r1() {
        Some(NamedCurve::P256)
    } else if oid == id_secp384r1() {
        Some(NamedCurve::P384)
    } else if oid == id_secp521r1() {
        Some(NamedCurve::P521)
    } else {
        None
    }
}

/// Octets of one coordinate: ceil(log2(p)/8) for the curve's field prime p
/// of 256, 384 and 521 bits (see "Point lengths" at the top of this file).
pub open spec fn field_octets(curve: NamedCurve) -> nat {
    match curve {
        NamedCurve::P256 => 32,
        NamedCurve::P384 => 48,
        NamedCurve::P521 => 66,
    }
}

/// RFC 5480 §2.2, the form of `point` on `curve`, or refusal.
pub open spec fn point_form(curve: NamedCurve, point: Seq<u8>) -> Option<PointForm> {
    let size = field_octets(curve);
    if point.len() == 0 {
        // No first octet to say the form.
        None
    } else if point[0] == 0x04 {
        // "The uncompressed form is indicated by 0x04": x then y.
        if point.len() == 1 + 2 * size {
            Some(PointForm::Uncompressed)
        } else {
            None
        }
    } else if point[0] == 0x02 || point[0] == 0x03 {
        // "the compressed form is indicated by either 0x02 or 0x03": x.
        if point.len() == 1 + size {
            Some(PointForm::Compressed)
        } else {
            None
        }
    } else {
        // "The public key MUST be rejected if any other value is included in
        // the first octet."
        None
    }
}

/// RFC 5480 §2.1.1 and §2.2, an `id-ecPublicKey` key from its parameters and
/// bit string.
pub open spec fn ec_key(parameters: Option<Tlv>, subject_public_key: BitString) -> Option<
    PublicKey,
> {
    // §2.1.1 "The parameter for id-ecPublicKey is as follows and MUST always
    // be present"; "If the elliptic curve domain parameters are not present,
    // then clients MUST reject the certificate."
    match parameters {
        None => None,
        // `ECParameters ::= CHOICE { namedCurve OBJECT IDENTIFIER }`:
        // "implicitCurve and specifiedCurve MUST NOT be used in PKIX".
        Some(p) => match decode_object_identifier(p) {
            None => None,
            // §2.1.1.1, the curves in scope.
            Some(oid) => match named_curve(oid) {
                None => None,
                Some(curve) => {
                    // §2.2: the ECPoint OCTET STRING's bits are the BIT
                    // STRING's bits.
                    match whole_octets(subject_public_key) {
                        None => None,
                        Some(point) => match point_form(curve, point) {
                            None => None,
                            Some(form) => Some(PublicKey::Ec { curve, form, point }),
                        },
                    }
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// RFC 8410 §3 and §4: Curve25519 and Curve448
// ---------------------------------------------------------------------------

/// RFC 8410 §3 and §4, the key of one of its four algorithms, whose key is
/// `length` octets long, or refusal.
pub open spec fn rfc8410_key(
    parameters: Option<Tlv>,
    subject_public_key: BitString,
    length: nat,
) -> Option<Seq<u8>> {
    // §3 "For all of the OIDs, the parameters MUST be absent."
    if parameters is Some {
        None
    } else {
        // §4 "The algorithms defined in this document always encode the
        // public key as an exact multiple of 8 bits."
        match whole_octets(subject_public_key) {
            None => None,
            Some(key) => {
                // RFC 7748 §5 and RFC 8032 §5.1.2 and §5.2.2.
                if key.len() != length {
                    None
                } else {
                    Some(key)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Classification
// ---------------------------------------------------------------------------

/// RFC 5280 §4.1.2.7: "The object identifiers for the supported algorithms
/// and the methods for encoding the public key materials (public key and
/// parameters) are specified in [RFC3279], [RFC4055], and [RFC4491]", with
/// RFC 5480 and RFC 8410 for the curves. An algorithm not in scope is
/// refused (see the modelling choices).
pub open spec fn classify_key(spki: SubjectPublicKeyInfo) -> Option<PublicKey> {
    let algorithm = spki.algorithm.algorithm;
    let parameters = spki.algorithm.parameters;
    let subject_public_key = spki.subject_public_key;
    if algorithm == id_rsa_encryption() {
        // RFC 3279 §2.3.1.
        rsa_key(parameters, subject_public_key)
    } else if algorithm == id_rsassa_pss() {
        // RFC 4055 §1.2 and §3.1: out of scope.
        None
    } else if algorithm == id_ec_public_key() {
        // RFC 5480 §2.1.1.
        ec_key(parameters, subject_public_key)
    } else if algorithm == id_x25519() {
        // RFC 7748 §5: "32-byte strings (for X25519)".
        match rfc8410_key(parameters, subject_public_key, 32) {
            None => None,
            Some(key) => Some(PublicKey::X25519 { key }),
        }
    } else if algorithm == id_x448() {
        // RFC 7748 §5: "56-byte strings (for X448)".
        match rfc8410_key(parameters, subject_public_key, 56) {
            None => None,
            Some(key) => Some(PublicKey::X448 { key }),
        }
    } else if algorithm == id_ed25519() {
        // RFC 8032 §5.1.2: "a 32-octet string".
        match rfc8410_key(parameters, subject_public_key, 32) {
            None => None,
            Some(key) => Some(PublicKey::Ed25519 { key }),
        }
    } else if algorithm == id_ed448() {
        // RFC 8032 §5.2.2: "a 57-octet string".
        match rfc8410_key(parameters, subject_public_key, 57) {
            None => None,
            Some(key) => Some(PublicKey::Ed448 { key }),
        }
    } else {
        None
    }
}

/// The DER SubjectPublicKeyInfo `input`, classified, or refusal.
pub open spec fn subject_public_key(input: Seq<u8>) -> Option<PublicKey> {
    match decode_spki(input) {
        None => None,
        Some(spki) => classify_key(spki),
    }
}

// ---------------------------------------------------------------------------
// RFC 8017 §3.1: a valid RSA public key
// ---------------------------------------------------------------------------

/// RFC 8017 §3.1, the parts that can be checked without factoring n: "the
/// RSA modulus n is a product of u distinct odd primes r_i, ..., where u >=
/// 2, and the RSA public exponent e is an integer between 3 and n - 1
/// satisfying GCD(e,\lambda(n)) = 1". So n is odd and at least 3 * 5; e is
/// between 3 and n - 1; and e is odd, because each r_i - 1 is even, so
/// \lambda(n) is even and shares the factor 2 with any even e.
pub open spec fn rsa_public_key_requirements(n: int, e: int) -> bool {
    n % 2 == 1 && n >= 15 && 3 <= e && e <= n - 1 && e % 2 == 1
}

/// The "shall" clauses on a classified key's value. Only RSA has any beyond
/// what [`subject_public_key`] already refuses.
pub open spec fn public_key_requirements(k: PublicKey) -> bool {
    match k {
        PublicKey::Rsa { modulus, public_exponent, .. } => rsa_public_key_requirements(
            modulus,
            public_exponent,
        ),
        _ => true,
    }
}

/// [`subject_public_key`], refusing also a key that breaks
/// [`public_key_requirements`].
pub open spec fn valid_subject_public_key(input: Seq<u8>) -> Option<PublicKey> {
    match subject_public_key(input) {
        None => None,
        Some(k) => {
            if public_key_requirements(k) {
                Some(k)
            } else {
                None
            }
        },
    }
}

} // verus!
