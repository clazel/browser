//! `spki/spec.rs`'s key classification against the clean-room transcription
//! `independent/spki.rs` (written without reading `src/spki/`; this proof is
//! by a different author).
//!
//! `equivalence_structures.rs`'s `theorem_spki_fwd` and `theorem_spki_back`
//! already prove the two read the same SubjectPublicKeyInfo *structure*. This
//! file proves they classify the same *keys*:
//!
//! - [`theorem_spki_classification_fwd`]: every key the crate classifies
//!   (`Rsa`, `EcP256`, `EcP384`) the transcription accepts as the same key:
//!   the same RSAPublicKey octets with the same modulus and exponent values,
//!   or the same curve and uncompressed point.
//! - [`theorem_spki_classification_back`]: every key the transcription
//!   accepts as RSA, or as an uncompressed P-256 or P-384 point, the crate
//!   classifies the same way.
//!
//! So on RSA and on uncompressed P-256 and P-384 keys the two agree exactly,
//! with no domain condition beyond an input shorter than 2^64 octets.
//!
//! **Where they differ, and why each is not a defect** (not proven; listed so
//! that nobody reads the theorems as more):
//! - **Keys the crate leaves `Unsupported`.** The crate returns every
//!   well-framed SubjectPublicKeyInfo whose key it does not classify as
//!   `Unsupported` (its header: "the set of inputs that parse is
//!   unchanged"); the transcription classifies or refuses. Those are:
//!   P-521; compressed points (RFC 5480 §2.2 "MAY" support them); Ed25519,
//!   Ed448, X25519 and X448 (RFC 8410); and any other algorithm. An
//!   `Unsupported` key verifies no signature (`clazel-crypto`'s
//!   `signature/spec.rs` and `chain/spec.rs` use only `Rsa`, `EcP256` and
//!   `EcP384`), so a certificate signed with one is refused later, at the
//!   signature, not here.
//! - **Malformed keys of an unclassified algorithm.** The same `Unsupported`
//!   covers an `id-ecPublicKey` key the transcription refuses (a hybrid
//!   point, absent or implicitCurve parameters, a wrong length). Same reason:
//!   no signature verifies with it.
//! - **RFC 8017 §3.1's "valid RSA public key"** (`valid_subject_public_key`):
//!   the crate does not check n odd, n >= 15, 3 <= e <= n - 1, e odd. Its
//!   header says so ("not RSA key validation"); the signature check does the
//!   arithmetic and fails on a key that is not one.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_name::{lemma_sequence_back, lemma_sequence_fwd};
#[cfg(verus_only)]
use super::equivalence_signature::lemma_element_reads;
#[cfg(verus_only)]
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::equivalence_tbs::lemma_read_integer;
#[cfg(verus_only)]
use super::equivalence_values::lemma_integer_magnitude;
#[cfg(verus_only)]
use super::spki as sp;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::spki::spec as k;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

/// The crate's classification `a`, of a key whose BIT STRING octets are
/// `bits`, is the transcription's `y`.
pub open spec fn classification_agrees(a: k::PublicKey, bits: Seq<u8>, y: sp::PublicKey) -> bool {
    match a {
        k::PublicKey::Rsa(r) => match y {
            sp::PublicKey::Rsa { modulus, public_exponent, key } => {
                &&& key == r.encoded_der
                &&& key == bits
                &&& modulus == d::be_value(r.modulus_octets) as int
                &&& public_exponent == d::be_value(r.public_exponent_octets) as int
            },
            _ => false,
        },
        k::PublicKey::EcP256(xy) => {
            &&& y == (sp::PublicKey::Ec {
                curve: sp::NamedCurve::P256,
                form: sp::PointForm::Uncompressed,
                point: bits,
            })
            &&& bits.len() == 65
            &&& xy == bits.subrange(1, 65)
        },
        k::PublicKey::EcP384(p) => {
            &&& y == (sp::PublicKey::Ec {
                curve: sp::NamedCurve::P384,
                form: sp::PointForm::Uncompressed,
                point: bits,
            })
            &&& p == bits
        },
        k::PublicKey::Unsupported => false,
    }
}

/// The transcription's keys the crate classifies: RSA, and an uncompressed
/// point on P-256 or P-384.
pub open spec fn crate_classifies(y: sp::PublicKey) -> bool {
    match y {
        sp::PublicKey::Rsa { .. } => true,
        sp::PublicKey::Ec { curve, form, .. } => {
            &&& form == sp::PointForm::Uncompressed
            &&& (curve == sp::NamedCurve::P256 || curve == sp::NamedCurve::P384)
        },
        _ => false,
    }
}

// ---------------------------------------------------------------------
// Sizes and elements of `der.rs`'s encodings.
// ---------------------------------------------------------------------

/// An encoding is no longer than its input, and its contents no longer than
/// it.
pub proof fn lemma_tlv_size(v: Seq<u8>)
    requires
        i::parse_tlv(v) is Some,
    ensures
        i::parse_tlv(v)->Some_0.contents.len() <= i::parse_tlv(v)->Some_0.encoding.len() <= v.len(),
{
}

/// An element of a list of encodings is no longer than the list.
pub proof fn lemma_tlvs_size(v: Seq<u8>, l: Seq<i::Tlv>, m: int)
    requires
        i::parse_tlvs(v) == Some(l),
        0 <= m < l.len(),
    ensures
        l[m].contents.len() <= l[m].encoding.len() <= v.len(),
    decreases v.len(),
{
    let u = i::parse_tlv(v)->Some_0;
    lemma_tlv_size(v);
    let size = u.encoding.len();
    let tail = v.subrange(size as int, v.len() as int);
    let rest = i::parse_tlvs(tail)->Some_0;
    assert(l =~= seq![u] + rest);
    if m > 0 {
        assert(l[m] == rest[m - 1]);
        lemma_tlvs_size(tail, rest, m - 1);
    } else {
        assert(l[0] == u);
    }
}

/// The parts of a SubjectPublicKeyInfo the transcription decodes: the key
/// octets are no longer than the input, and the parameters read alone.
pub proof fn lemma_spki_parts(input: Seq<u8>, x: s::SubjectPublicKeyInfo)
    requires
        input.len() < two64(),
        sp::decode_spki(input) == Some(x),
    ensures
        x.subject_public_key.octets.len() <= input.len(),
        match x.algorithm.parameters {
            Some(q) => tag_fits(q) ==> {
                &&& i::parse_single(q.encoding) == Some(q)
                &&& q.encoding.len() <= input.len()
            },
            None => true,
        },
{
    let u = i::parse_single(input)->Some_0;
    lemma_tlv_size(input);
    let e = s::sequence_elements(u)->Some_0;
    lemma_tlvs_size(u.contents, e, 0);
    lemma_tlvs_size(u.contents, e, 1);
    let l = s::sequence_elements(e[0])->Some_0;
    if l.len() > 1 {
        let q = l[1];
        assert(x.algorithm.parameters == Some(q));
        lemma_tlvs_size(e[0].contents, l, 1);
        if tag_fits(q) {
            lemma_element_reads(e[0].contents, l, 1);
        }
    }
}

// ---------------------------------------------------------------------
// The parameters: NULL and a named curve.
// ---------------------------------------------------------------------

/// `05 00` is the NULL value's one encoding.
pub proof fn lemma_encode_null()
    ensures
        d::encode_null() == seq![0x05u8, 0x00u8],
{
    assert(d::encode_identifier(d::universal_primitive(d::NULL)) =~= seq![5u8]);
    assert(d::encode_length(0) =~= seq![0u8]);
    assert(d::encode_null() =~= seq![0x05u8, 0x00u8]);
}

/// A parameters encoding is the NULL value exactly when its octets are
/// `05 00` (DER: one encoding per value).
pub proof fn lemma_null_parameter(q: i::Tlv)
    requires
        i::parse_single(q.encoding) == Some(q),
        q.encoding.len() < two64(),
        tag_fits(q),
    ensures
        sp::is_null(q) == (q.encoding == seq![0x05u8, 0x00u8]),
{
    let b = q.encoding;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_single_back(b, 0, len, q);
    let t = d::read_tlv(b, 0, len)->Some_0;
    lemma_has_universal_tag(b, 0, t, q, d::NULL, false);
    lemma_encode_null();
    if sp::is_null(q) {
        assert(t.cstart == t.cend);
        assert(d::read_null(b, 0, len) == Some(len));
        clazel_der::lemmas_typed::lemma_encode_null_read_null(b, 0, len);
        assert(b =~= seq![0x05u8, 0x00u8]);
    }
    if b == seq![0x05u8, 0x00u8] {
        assert(b.subrange(0, 2) =~= d::encode_null());
        clazel_der::lemmas_typed::lemma_read_null_encode_null(b, 0, len);
        assert(q.contents.len() == 0);
    }
}

/// A parameters encoding decodes to the object identifier `arcs` exactly
/// when its octets are `arcs`'s one DER encoding.
pub proof fn lemma_oid_parameter(q: i::Tlv, arcs: Seq<nat>)
    requires
        i::parse_single(q.encoding) == Some(q),
        q.encoding.len() < two64(),
        tag_fits(q),
        d::oid_valid(arcs),
        oid_fits(arcs),
        d::oid_contents(arcs).len() < d::pow256(8),
    ensures
        (i::decode_object_identifier(q) == Some(arcs)) == (q.encoding == d::encode_oid(arcs)),
{
    let b = q.encoding;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_single_back(b, 0, len, q);
    lemma_read_oid(b, 0, len);
    clazel_der::lemmas_typed::lemma_encode_oid_read_oid(b, 0, len);
    if b == d::encode_oid(arcs) {
        assert(b.subrange(0, (0 + d::encode_oid(arcs).len()) as int) =~= d::encode_oid(arcs));
        clazel_der::lemmas_typed::lemma_read_oid_encode_oid(arcs, b, 0, len);
    }
    if i::decode_object_identifier(q) == Some(arcs) {
        assert(d::read_oid(b, 0, len) is Some);
        let (o, n) = d::read_oid(b, 0, len)->Some_0;
        assert(o == arcs);
        assert(n == len);
        assert(b =~= b.subrange(0, n as int));
    }
}

/// The two named curves, both ways: the arcs, and the DER the crate
/// compares.
pub proof fn lemma_curves()
    ensures
        d::encode_oid(sp::id_secp256r1()) == k::secp256r1_parameter(),
        d::encode_oid(sp::id_secp384r1()) == k::secp384r1_parameter(),
        d::oid_valid(sp::id_secp256r1()),
        d::oid_valid(sp::id_secp384r1()),
        oid_fits(sp::id_secp256r1()),
        oid_fits(sp::id_secp384r1()),
        d::oid_contents(sp::id_secp256r1()).len() < d::pow256(8),
        d::oid_contents(sp::id_secp384r1()).len() < d::pow256(8),
        sp::id_secp256r1() != sp::id_secp384r1(),
        sp::id_secp256r1() != sp::id_secp521r1(),
        sp::id_secp384r1() != sp::id_secp521r1(),
        k::secp256r1_parameter() != k::secp384r1_parameter(),
{
    assert(d::encode_oid(sp::id_secp256r1()) =~= k::secp256r1_parameter()) by (compute_only);
    assert(d::encode_oid(sp::id_secp384r1()) =~= k::secp384r1_parameter()) by (compute_only);
    assert(d::oid_contents(sp::id_secp256r1()).len() == 8) by (compute_only);
    assert(d::oid_contents(sp::id_secp384r1()).len() == 5) by (compute_only);
    clazel_der::lemmas::lemma_pow256_8();
    let p = sp::id_secp256r1();
    assert(p.len() == 7);
    assert(p[4] == 3);
    assert(p[0] == 1 && p[1] == 2 && p[2] == 840 && p[3] == 10045 && p[5] == 1 && p[6] == 7);
    assert forall|j: int| 2 <= j < p.len() implies #[trigger] p[j] < two64() by {
        assert(j == 2 || j == 3 || j == 4 || j == 5 || j == 6);
    }
    assert forall|j: int| 2 <= j < p.len() implies #[trigger] p[j] < 0x1_0000_0000_0000_0000 by {
        assert(j == 2 || j == 3 || j == 4 || j == 5 || j == 6);
    }
    let r = sp::id_secp384r1();
    assert(r.len() == 5);
    assert(r[0] == 1 && r[1] == 3 && r[2] == 132 && r[3] == 0 && r[4] == 34);
    assert forall|j: int| 2 <= j < r.len() implies #[trigger] r[j] < two64() by {
        assert(j == 2 || j == 3 || j == 4);
    }
    assert forall|j: int| 2 <= j < r.len() implies #[trigger] r[j] < 0x1_0000_0000_0000_0000 by {
        assert(j == 2 || j == 3 || j == 4);
    }
    let w = sp::id_secp521r1();
    assert(w[4] == 35);
    assert(k::secp256r1_parameter().len() == 10);
    assert(k::secp384r1_parameter().len() == 7);
}

/// The algorithm identifiers: the transcription's are the crate's, and
/// distinct.
pub proof fn lemma_algorithms()
    ensures
        k::is_rsa_encryption(sp::id_rsa_encryption()),
        k::is_id_ec_public_key(sp::id_ec_public_key()),
        forall|o: Seq<nat>| k::is_rsa_encryption(o) ==> o == sp::id_rsa_encryption(),
        forall|o: Seq<nat>| k::is_id_ec_public_key(o) ==> o == sp::id_ec_public_key(),
        sp::id_ec_public_key() != sp::id_rsa_encryption(),
        sp::id_ec_public_key() != sp::id_rsassa_pss(),
        sp::id_rsa_encryption() != sp::id_rsassa_pss(),
        oid_fits(sp::id_rsa_encryption()),
        oid_fits(sp::id_ec_public_key()),
{
    assert forall|o: Seq<nat>| k::is_rsa_encryption(o) implies o == sp::id_rsa_encryption() by {
        assert(o =~= sp::id_rsa_encryption());
    }
    assert forall|o: Seq<nat>| k::is_id_ec_public_key(o) implies o == sp::id_ec_public_key() by {
        assert(o =~= sp::id_ec_public_key());
    }
    assert(sp::id_rsa_encryption() =~= seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 1nat]);
    assert(sp::id_ec_public_key() =~= seq![1nat, 2nat, 840nat, 10045nat, 2nat, 1nat]);
    assert(sp::id_ec_public_key().len() == 6);
    assert(sp::id_rsa_encryption().len() == 7);
    assert(sp::id_rsassa_pss().len() == 7);
    assert(sp::id_rsa_encryption()[6] == 1);
    assert(sp::id_rsassa_pss()[6] == 10);
    let a = sp::id_rsa_encryption();
    assert(a[0] == 1 && a[1] == 2 && a[2] == 840 && a[3] == 113549 && a[4] == 1 && a[5] == 1);
    assert forall|j: int| 2 <= j < a.len() implies #[trigger] a[j] < two64() by {
        assert(j == 2 || j == 3 || j == 4 || j == 5 || j == 6);
    }
    let c = sp::id_ec_public_key();
    assert(c[0] == 1 && c[1] == 2 && c[2] == 840 && c[3] == 10045 && c[4] == 2 && c[5] == 1);
    assert forall|j: int| 2 <= j < c.len() implies #[trigger] c[j] < two64() by {
        assert(j == 2 || j == 3 || j == 4 || j == 5);
    }
}

// ---------------------------------------------------------------------
// RSAPublicKey.
// ---------------------------------------------------------------------

/// `positive_integer_value` is a nonzero value of the magnitude octets.
pub proof fn lemma_positive_value(b: Seq<u8>, s: nat, e: nat)
    requires
        s <= e <= b.len(),
    ensures
        k::positive_integer_value(b, s, e) == (d::be_value(sl(b, s, e)) > 0),
    decreases e - s,
{
    let r = sl(b, s, e);
    if s == e {
        assert(r.len() == 0);
    } else {
        lemma_positive_value(b, s, (e - 1) as nat);
        assert(r.drop_last() =~= sl(b, s, (e - 1) as nat));
        assert(r.last() == b[e - 1]);
    }
}

/// An RSAPublicKey the crate reads, the transcription reads to the values of
/// its magnitude octets, both positive.
pub proof fn lemma_rsa_fwd(key: Seq<u8>)
    requires
        key.len() < two64(),
        k::parse_rsa_public_key(key) is Some,
    ensures
        sp::decode_rsa_public_key(key) == Some(
            (
                d::be_value(k::parse_rsa_public_key(key)->Some_0.modulus_octets) as int,
                d::be_value(k::parse_rsa_public_key(key)->Some_0.public_exponent_octets) as int,
            ),
        ),
        d::be_value(k::parse_rsa_public_key(key)->Some_0.modulus_octets) > 0,
        d::be_value(k::parse_rsa_public_key(key)->Some_0.public_exponent_octets) > 0,
        k::parse_rsa_public_key(key)->Some_0.encoded_der == key,
{
    let b = key;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let t = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, end) = (t.cstart, t.cend);
    let (neg1, ms, me, am) = d::read_integer(b, start, end)->Some_0;
    lemma_read_integer(b, start, end);
    lemma_integer_magnitude(b, start, end);
    lemma_positive_value(b, ms, me);
    let (neg2, es, ee, ae) = d::read_integer(b, am, end)->Some_0;
    lemma_read_integer(b, am, end);
    lemma_integer_magnitude(b, am, end);
    lemma_positive_value(b, es, ee);
    let none = Seq::<i::Tlv>::empty();
    lemma_tlvs_empty(b, end);
    lemma_tlvs_cons(b, am, end, none);
    let iu2 = i::parse_tlv(sl(b, am, end))->Some_0;
    lemma_tlvs_cons(b, start, end, seq![iu2] + none);
    let iu1 = i::parse_tlv(sl(b, start, end))->Some_0;
    let l = seq![iu1] + (seq![iu2] + none);
    lemma_sequence_fwd(b, 0, len, l);
    lemma_single(b, 0, len);
    assert(l[0] == iu1);
    assert(l[1] == iu2);
    assert(l.len() == 2);
}

/// An RSAPublicKey the transcription reads to two positive values, the crate
/// reads.
pub proof fn lemma_rsa_back(key: Seq<u8>)
    requires
        key.len() < two64(),
        sp::decode_rsa_public_key(key) is Some,
        sp::decode_rsa_public_key(key)->Some_0.0 > 0,
        sp::decode_rsa_public_key(key)->Some_0.1 > 0,
    ensures
        k::parse_rsa_public_key(key) is Some,
{
    let b = key;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let u = i::parse_single(b)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    lemma_sequence_back(b, 0, len, u, l);
    let t = d::read_tlv(b, 0, len)->Some_0;
    let (start, finish) = (t.cstart, t.cend);
    assert(l.len() == 2);
    assert(tag_fits(l[0]));
    lemma_tlvs_head(b, start, finish, l);
    lemma_read_integer(b, start, finish);
    let first = d::read_tlv(b, start, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, finish);
    assert(d::read_integer(b, start, finish) is Some);
    let con1 = sl(b, first.cstart, first.cend);
    lemma_integer_sign(con1);
    lemma_integer_magnitude(b, start, finish);
    let (neg1, ms, me, am) = d::read_integer(b, start, finish)->Some_0;
    lemma_positive_value(b, ms, me);
    let rest = l.skip(1);
    assert(rest[0] == l[1]);
    assert(tag_fits(rest[0]));
    lemma_tlvs_head(b, am, finish, rest);
    lemma_read_integer(b, am, finish);
    let second = d::read_tlv(b, am, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, am, finish);
    assert(d::read_integer(b, am, finish) is Some);
    let con2 = sl(b, second.cstart, second.cend);
    lemma_integer_sign(con2);
    lemma_integer_magnitude(b, am, finish);
    let (neg2, es, ee, ae) = d::read_integer(b, am, finish)->Some_0;
    lemma_positive_value(b, es, ee);
    lemma_tlvs_none_left(b, second.cend, finish, rest.skip(1));
    assert(rest.skip(1).len() == 0);
    assert(ae == finish);
}

// ---------------------------------------------------------------------
// The two classifications, case by case.
// ---------------------------------------------------------------------

/// What `parse_subject_public_key_info` classifies, and how.
pub proof fn lemma_crate_shape(input: Seq<u8>)
    requires
        k::parse_subject_public_key_info(input) is Some,
    ensures
        ({
            let a = k::parse_subject_public_key_info(input)->Some_0;
            &&& k::is_rsa_encryption(a.algorithm.oid) ==> {
                &&& a.algorithm.parameters_der == Some(seq![0x05u8, 0x00u8])
                &&& a.subject_public_key_unused_bits == 0
                &&& k::parse_rsa_public_key(a.subject_public_key_bits) is Some
                &&& a.public_key == k::PublicKey::Rsa(
                    k::parse_rsa_public_key(a.subject_public_key_bits)->Some_0,
                )
            }
            &&& !k::is_rsa_encryption(a.algorithm.oid) ==> a.public_key == k::classify_ec_public_key(
                a.algorithm,
                a.subject_public_key_unused_bits,
                a.subject_public_key_bits,
            )
        }),
{
}

/// `subject_public_key` is `classify_key` of what `decode_spki` read.
pub proof fn lemma_subject_public_key(input: Seq<u8>, x: s::SubjectPublicKeyInfo)
    requires
        sp::decode_spki(input) == Some(x),
    ensures
        sp::subject_public_key(input) == sp::classify_key(x),
{
}

/// An RSA key, from the crate.
pub proof fn lemma_fwd_rsa(input: Seq<u8>, a: k::SubjectPublicKeyInfo, x: s::SubjectPublicKeyInfo)
    requires
        input.len() < two64(),
        sp::decode_spki(input) == Some(x),
        spki_agree(a, x),
        algorithm_in_domain(x.algorithm),
        k::is_rsa_encryption(a.algorithm.oid),
        a.algorithm.parameters_der == Some(seq![0x05u8, 0x00u8]),
        a.subject_public_key_unused_bits == 0,
        k::parse_rsa_public_key(a.subject_public_key_bits) is Some,
        a.public_key == k::PublicKey::Rsa(k::parse_rsa_public_key(a.subject_public_key_bits)->Some_0),
    ensures
        sp::classify_key(x) is Some,
        crate_classifies(sp::classify_key(x)->Some_0),
        classification_agrees(a.public_key, a.subject_public_key_bits, sp::classify_key(x)->Some_0),
{
    hide(sp::decode_spki);
    hide(k::parse_rsa_public_key);
    hide(sp::decode_rsa_public_key);
    lemma_algorithms();
    lemma_spki_parts(input, x);
    let q = x.algorithm.parameters->Some_0;
    assert(q.encoding == seq![0x05u8, 0x00u8]);
    lemma_null_parameter(q);
    lemma_rsa_fwd(a.subject_public_key_bits);
    assert(x.algorithm.algorithm == sp::id_rsa_encryption());
}

/// An EC key, from the crate.
pub proof fn lemma_fwd_ec(input: Seq<u8>, a: k::SubjectPublicKeyInfo, x: s::SubjectPublicKeyInfo)
    requires
        input.len() < two64(),
        sp::decode_spki(input) == Some(x),
        spki_agree(a, x),
        algorithm_in_domain(x.algorithm),
        !k::is_rsa_encryption(a.algorithm.oid),
        a.public_key == k::classify_ec_public_key(
            a.algorithm,
            a.subject_public_key_unused_bits,
            a.subject_public_key_bits,
        ),
        !(a.public_key is Unsupported),
    ensures
        sp::classify_key(x) is Some,
        crate_classifies(sp::classify_key(x)->Some_0),
        classification_agrees(a.public_key, a.subject_public_key_bits, sp::classify_key(x)->Some_0),
{
    hide(sp::decode_spki);
    hide(i::decode_object_identifier);
    lemma_algorithms();
    lemma_curves();
    lemma_spki_parts(input, x);
    let q = x.algorithm.parameters->Some_0;
    let bits = a.subject_public_key_bits;
    assert(x.algorithm.algorithm == sp::id_ec_public_key());
    if a.algorithm.parameters_der == Some(k::secp256r1_parameter()) && bits.len() == 65 {
        lemma_oid_parameter(q, sp::id_secp256r1());
    } else {
        lemma_oid_parameter(q, sp::id_secp384r1());
        assert(bits.len() == 97);
    }
}

/// An RSA key, from the transcription.
pub proof fn lemma_back_rsa(input: Seq<u8>, x: s::SubjectPublicKeyInfo)
    requires
        input.len() < two64(),
        sp::decode_spki(input) == Some(x),
        x.algorithm.algorithm == sp::id_rsa_encryption(),
        sp::classify_key(x) is Some,
    ensures
        k::parse_subject_public_key_info(input) is Some,
        classification_agrees(
            k::parse_subject_public_key_info(input)->Some_0.public_key,
            k::parse_subject_public_key_info(input)->Some_0.subject_public_key_bits,
            sp::classify_key(x)->Some_0,
        ),
{
    hide(k::parse_subject_public_key_info);
    hide(k::parse_rsa_public_key);
    hide(sp::decode_rsa_public_key);
    lemma_algorithms();
    lemma_spki_parts(input, x);
    let u = i::parse_single(input)->Some_0;
    assert(s::decode_subject_public_key_info(u) == Some(x)) by {
        reveal(sp::decode_spki);
    }
    let q = x.algorithm.parameters->Some_0;
    assert(sp::is_null(q));
    assert(tag_fits(q));
    lemma_null_parameter(q);
    lemma_rsa_back(x.subject_public_key.octets);
    assert(spki_in_domain(x));
    theorem_spki_back(input, u, x);
    lemma_crate_shape(input);
    let a = k::parse_subject_public_key_info(input)->Some_0;
    lemma_rsa_fwd(a.subject_public_key_bits);
}

/// An EC key, from the transcription.
pub proof fn lemma_back_ec(input: Seq<u8>, x: s::SubjectPublicKeyInfo)
    requires
        input.len() < two64(),
        sp::decode_spki(input) == Some(x),
        x.algorithm.algorithm == sp::id_ec_public_key(),
        sp::classify_key(x) is Some,
        crate_classifies(sp::classify_key(x)->Some_0),
    ensures
        k::parse_subject_public_key_info(input) is Some,
        classification_agrees(
            k::parse_subject_public_key_info(input)->Some_0.public_key,
            k::parse_subject_public_key_info(input)->Some_0.subject_public_key_bits,
            sp::classify_key(x)->Some_0,
        ),
{
    hide(k::parse_subject_public_key_info);
    hide(i::decode_object_identifier);
    lemma_algorithms();
    lemma_curves();
    lemma_spki_parts(input, x);
    let u = i::parse_single(input)->Some_0;
    assert(s::decode_subject_public_key_info(u) == Some(x)) by {
        reveal(sp::decode_spki);
    }
    let y = sp::classify_key(x)->Some_0;
    let q = x.algorithm.parameters->Some_0;
    assert(tag_fits(q)) by {
        reveal(i::decode_object_identifier);
    }
    if y->Ec_curve == sp::NamedCurve::P256 {
        assert(i::decode_object_identifier(q) == Some(sp::id_secp256r1()));
        lemma_oid_parameter(q, sp::id_secp256r1());
    } else {
        assert(i::decode_object_identifier(q) == Some(sp::id_secp384r1()));
        lemma_oid_parameter(q, sp::id_secp384r1());
    }
    assert(spki_in_domain(x));
    theorem_spki_back(input, u, x);
    lemma_crate_shape(input);
}

/// **From the crate.** A key `spki/spec.rs` classifies, the transcription
/// accepts as the same key.
pub proof fn theorem_spki_classification_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        k::parse_subject_public_key_info(input) is Some,
        !(k::parse_subject_public_key_info(input)->Some_0.public_key is Unsupported),
    ensures
        sp::subject_public_key(input) is Some,
        crate_classifies(sp::subject_public_key(input)->Some_0),
        classification_agrees(
            k::parse_subject_public_key_info(input)->Some_0.public_key,
            k::parse_subject_public_key_info(input)->Some_0.subject_public_key_bits,
            sp::subject_public_key(input)->Some_0,
        ),
{
    hide(k::parse_subject_public_key_info);
    hide(sp::subject_public_key);
    hide(sp::classify_key);
    hide(k::parse_rsa_public_key);
    lemma_crate_shape(input);
    let a = k::parse_subject_public_key_info(input)->Some_0;
    lemma_algorithms();
    lemma_curves();
    if !k::is_rsa_encryption(a.algorithm.oid) {
        assert(a.algorithm.parameters_der == Some(k::secp256r1_parameter())
            || a.algorithm.parameters_der == Some(k::secp384r1_parameter()));
        assert(k::secp256r1_parameter()[0] == 0x06);
        assert(k::secp384r1_parameter()[0] == 0x06);
    }
    assert(parameters_plain(a.algorithm));
    theorem_spki_fwd(input);
    let x = s::decode_subject_public_key_info(i::parse_single(input)->Some_0)->Some_0;
    assert(sp::decode_spki(input) == Some(x));
    lemma_subject_public_key(input, x);
    if k::is_rsa_encryption(a.algorithm.oid) {
        lemma_fwd_rsa(input, a, x);
    } else {
        lemma_fwd_ec(input, a, x);
    }
}

/// **From the transcription.** An RSA key, or an uncompressed P-256 or P-384
/// key, the transcription accepts, `spki/spec.rs` classifies the same way.
pub proof fn theorem_spki_classification_back(input: Seq<u8>)
    requires
        input.len() < two64(),
        sp::subject_public_key(input) is Some,
        crate_classifies(sp::subject_public_key(input)->Some_0),
    ensures
        k::parse_subject_public_key_info(input) is Some,
        classification_agrees(
            k::parse_subject_public_key_info(input)->Some_0.public_key,
            k::parse_subject_public_key_info(input)->Some_0.subject_public_key_bits,
            sp::subject_public_key(input)->Some_0,
        ),
{
    hide(k::parse_subject_public_key_info);
    hide(sp::classify_key);
    let x = sp::decode_spki(input)->Some_0;
    lemma_subject_public_key(input, x);
    let y = sp::classify_key(x)->Some_0;
    lemma_algorithms();
    let alg = x.algorithm.algorithm;
    if alg == sp::id_rsa_encryption() {
        lemma_back_rsa(input, x);
    } else {
        assert(alg == sp::id_ec_public_key()) by {
            reveal(sp::classify_key);
        }
        lemma_back_ec(input, x);
    }
}

} // verus!
