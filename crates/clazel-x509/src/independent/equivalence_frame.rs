//! What every certificate goes through in production, against the
//! transcription. `path/parsed/spec.rs`'s `parse_path_cert` runs
//! `parse_certificate` and `parse_tbs_certificate`, which keep the issuer, the
//! subject and the SubjectPublicKeyInfo as framed octets: `parse_name` and
//! `parse_subject_public_key_info` are not on that path. `crate_decode` in
//! `equivalence.rs` runs them, so its theorems say nothing about a certificate
//! whose Name no one parses.
//!
//! So this file states the transcription's reading of exactly those parts
//! `parse_path_cert` reads: [`decode_certificate_frame`] is
//! `structures.rs`'s `decode_certificate` with its three calls of `decode_name`
//! and `decode_subject_public_key_info` left out, each replaced by the test the
//! crate makes of that component (one SEQUENCE, the issuer not empty).
//!
//! - [`theorem_frame_fwd`]: what the crate's two outer decoders read, the frame
//!   reads to the same values. **It asks nothing of the Names or the key.**
//! - [`theorem_frame_completes`]: the frame with the three left-out decoders
//!   put back is `decode_certificate`. So the frame is that function, not a
//!   weaker thing of its own, and what the frame leaves unsaid is exactly
//!   whether those three components decode.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_name::*;
#[cfg(verus_only)]
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::equivalence_tbs::*;
#[cfg(verus_only)]
use super::equivalence_time::*;
#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::requirements as r;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::certificate::spec as c;
#[cfg(verus_only)]
use crate::tbs::spec as t;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

/// The transcription's reading of a TBSCertificate, with the two Names and the
/// key left as encodings.
pub struct TbsFrame {
    /// `version`.
    pub version: int,
    /// `serialNumber`.
    pub serial_number: int,
    /// `signature`.
    pub signature: super::structures::AlgorithmIdentifier,
    /// The encoding of `issuer`.
    pub issuer: super::der::Tlv,
    /// `validity`.
    pub validity: super::structures::Validity,
    /// The encoding of `subject`.
    pub subject: super::der::Tlv,
    /// The encoding of `subjectPublicKeyInfo`.
    pub subject_public_key_info: super::der::Tlv,
    /// `issuerUniqueIdentifier`.
    pub issuer_unique_identifier: Option<super::der::BitString>,
    /// `subjectUniqueIdentifier`.
    pub subject_unique_identifier: Option<super::der::BitString>,
    /// `extensions`.
    pub extensions: Option<Seq<super::extensions::Extension>>,
}

/// `decode_tbs_certificate` without `decode_name` and
/// `decode_subject_public_key_info`, and with no addition: the tests that take
/// their place are `tbs/spec.rs`'s, a SEQUENCE each, and an issuer not empty.
pub open spec fn decode_tbs_frame(u: i::Tlv) -> Option<TbsFrame> {
    match s::sequence_elements(u) {
        None => None,
        Some(l) => {
            let m = s::after_version(l);
            if m + 6 > l.len() {
                None
            } else {
                match (
                    s::version_component(l),
                    i::decode_integer(l[m as int]),
                    s::decode_algorithm_identifier(l[(m + 1) as int]),
                    s::decode_validity(l[(m + 3) as int]),
                    tail_of(l.skip((m + 6) as int)),
                ) {
                    (
                        Some(version),
                        Some(serial_number),
                        Some(signature),
                        Some(validity),
                        Some((issuer_unique_identifier, subject_unique_identifier, extensions, used)),
                    ) => {
                        if i::has_tag(l[(m + 2) as int], 0, 16, true) && l[(m + 2) as int].contents.len() > 0
                            && i::has_tag(l[(m + 4) as int], 0, 16, true) && i::has_tag(
                            l[(m + 5) as int],
                            0,
                            16,
                            true,
                        ) && m + 6 + used == l.len() {
                            Some(
                                TbsFrame {
                                    version,
                                    serial_number,
                                    signature,
                                    issuer: l[(m + 2) as int],
                                    validity,
                                    subject: l[(m + 4) as int],
                                    subject_public_key_info: l[(m + 5) as int],
                                    issuer_unique_identifier,
                                    subject_unique_identifier,
                                    extensions,
                                },
                            )
                        } else {
                            None
                        }
                    },
                    _ => None,
                }
            }
        },
    }
}

/// The transcription's reading of a Certificate, with the two Names and the
/// key left as encodings, and neither `altAlgorithmIdentifier` nor
/// `altSignature` (`requirements.rs`'s `one_signature_only`).
pub struct CertificateFrame {
    /// `toBeSigned`.
    pub to_be_signed: TbsFrame,
    /// The encoding of `toBeSigned`.
    pub tbs_encoding: super::der::Tlv,
    /// `algorithmIdentifier`.
    pub algorithm_identifier: super::structures::AlgorithmIdentifier,
    /// `signature`.
    pub signature: super::der::BitString,
}

/// `decode_certificate` of a frame: exactly the three components of a
/// certificate with one signature.
pub open spec fn decode_certificate_frame(der: Seq<u8>) -> Option<CertificateFrame> {
    match i::parse_single(der) {
        None => None,
        Some(u) => match s::sequence_elements(u) {
            None => None,
            Some(l) => {
                if l.len() != 3 {
                    None
                } else {
                    match (decode_tbs_frame(l[0]), s::decode_algorithm_identifier(l[1]), i::decode_bit_string(l[2])) {
                        (Some(to_be_signed), Some(algorithm_identifier), Some(signature)) => Some(
                            CertificateFrame { to_be_signed, tbs_encoding: l[0], algorithm_identifier, signature },
                        ),
                        _ => None,
                    }
                }
            },
        },
    }
}

// ---------------------------------------------------------------------
// Agreement, and what the frame still asks.
// ---------------------------------------------------------------------

/// The fields of a TBSCertificate agree.
pub open spec fn tbs_frame_agree(a: t::TbsCertificate, f: TbsFrame) -> bool {
    &&& a.version as int == f.version
    &&& i::parse_single(a.serial_number_der) is Some
    &&& i::decode_integer(i::parse_single(a.serial_number_der)->Some_0) == Some(f.serial_number)
    &&& algorithm_agree(a.signature, f.signature)
    &&& a.issuer_der == f.issuer.encoding
    &&& a.not_before == moment_time(time_moment(f.validity.not_before))
    &&& a.not_after == moment_time(time_moment(f.validity.not_after))
    &&& a.subject_der == f.subject.encoding
    &&& a.subject_public_key_info_der == f.subject_public_key_info.encoding
    &&& unique_agree(a.issuer_unique_id_der, f.issuer_unique_identifier)
    &&& unique_agree(a.subject_unique_id_der, f.subject_unique_identifier)
    &&& optional_extensions_agree(a.extensions_sequence_der, f.extensions)
}

/// Conditions 1 to 3 of `equivalence.rs`, for the parts production reads.
pub open spec fn tbs_frame_conditions(a: t::TbsCertificate) -> bool {
    &&& parameters_plain(a.signature)
    &&& a.not_before.second != 60
    &&& a.not_after.second != 60
    &&& extensions_decode(a.extensions_sequence_der)
}

// ---------------------------------------------------------------------
// From `tbs/spec.rs`.
// ---------------------------------------------------------------------

/// `signature` and `issuer`, from `tbs/spec.rs`, with the issuer unread.
#[verifier::spinoff_prover]
pub proof fn lemma_signature_issuer_frame(b: Seq<u8>, pos: nat, end: nat, rest: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        t::parse_signature_issuer(b, pos, end) is Some,
        parameters_plain(t::parse_signature_issuer(b, pos, end)->Some_0.0),
        i::parse_tlvs(sl(b, t::parse_signature_issuer(b, pos, end)->Some_0.2, end)) == Some(rest),
    ensures
        i::parse_tlvs(sl(b, pos, end)) is Some,
        ({
            let (algorithm, issuer, next) = t::parse_signature_issuer(b, pos, end)->Some_0;
            let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
            &&& pos < next <= end
            &&& l.len() == rest.len() + 2
            &&& l.skip(2) == rest
            &&& s::decode_algorithm_identifier(l[0]) is Some
            &&& algorithm_agree(algorithm, s::decode_algorithm_identifier(l[0])->Some_0)
            &&& i::has_tag(l[1], 0, 16, true)
            &&& l[1].contents.len() > 0
            &&& l[1].encoding == issuer
        }),
{
    hide(s::decode_algorithm_identifier);
    let (algorithm, issuer, next) = t::parse_signature_issuer(b, pos, end)->Some_0;
    let (a, after) = c::parse_algorithm_identifier(b, pos, end)->Some_0;
    lemma_algorithm_fwd(b, pos, end);
    let w = d::read_tlv(b, after, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, after, end);
    assert(!tag_is_reserved(w.tag));
    lemma_tlv(b, after, end);
    lemma_tlvs_cons(b, after, end, rest);
    let nu = i::parse_tlv(sl(b, after, end))->Some_0;
    lemma_has_universal_tag(b, after, w, nu, d::SEQUENCE, true);
    lemma_tlvs_cons(b, pos, end, seq![nu] + rest);
    let au = i::parse_tlv(sl(b, pos, end))->Some_0;
    let l = seq![au] + (seq![nu] + rest);
    assert(l[0] == au);
    assert(l[1] == nu);
    assert(l.skip(2) =~= rest);
}

/// `subject` and `subjectPublicKeyInfo`, from `tbs/spec.rs`, both unread.
#[verifier::spinoff_prover]
pub proof fn lemma_subject_spki_frame(b: Seq<u8>, pos: nat, end: nat, rest: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        t::parse_subject_spki(b, pos, end) is Some,
        i::parse_tlvs(sl(b, t::parse_subject_spki(b, pos, end)->Some_0.2, end)) == Some(rest),
    ensures
        i::parse_tlvs(sl(b, pos, end)) is Some,
        ({
            let (subject, spki, next) = t::parse_subject_spki(b, pos, end)->Some_0;
            let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
            &&& pos < next <= end
            &&& l.len() == rest.len() + 2
            &&& l.skip(2) == rest
            &&& i::has_tag(l[0], 0, 16, true)
            &&& l[0].encoding == subject
            &&& i::has_tag(l[1], 0, 16, true)
            &&& l[1].encoding == spki
        }),
{
    let (subject, spki, next) = t::parse_subject_spki(b, pos, end)->Some_0;
    let w = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    let v = d::read_tlv(b, w.cend, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, w.cend, end);
    assert(!tag_is_reserved(w.tag));
    assert(!tag_is_reserved(v.tag));
    lemma_tlv(b, w.cend, end);
    lemma_tlvs_cons(b, w.cend, end, rest);
    let ku = i::parse_tlv(sl(b, w.cend, end))->Some_0;
    lemma_has_universal_tag(b, w.cend, v, ku, d::SEQUENCE, true);
    lemma_tlv(b, pos, end);
    lemma_tlvs_cons(b, pos, end, seq![ku] + rest);
    let nu = i::parse_tlv(sl(b, pos, end))->Some_0;
    lemma_has_universal_tag(b, pos, w, nu, d::SEQUENCE, true);
    let l = seq![nu] + (seq![ku] + rest);
    assert(l[0] == nu);
    assert(l[1] == ku);
    assert(l.skip(2) =~= rest);
}

/// From `signature` on, the list of a TBSCertificate, from `tbs/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_tbs_rest_frame(b: Seq<u8>, p: nat, end: nat, a: t::TbsCertificate, version: nat)
    requires
        wf(b, p, end),
        end - p < two64(),
        tbs_frame_conditions(a),
        ({
            match t::parse_signature_issuer(b, p, end) {
                None => false,
                Some((signature, issuer, p4)) => match t::parse_validity(b, p4, end) {
                    None => false,
                    Some((not_before, not_after, p5)) => match t::parse_subject_spki(b, p5, end) {
                        None => false,
                        Some((subject, spki, p7)) => match t::parse_optional_tail(b, p7, end, version) {
                            None => false,
                            Some(tail) => {
                                &&& signature == a.signature
                                &&& issuer == a.issuer_der
                                &&& not_before == a.not_before
                                &&& not_after == a.not_after
                                &&& subject == a.subject_der
                                &&& spki == a.subject_public_key_info_der
                                &&& tail.issuer_unique_id_der == a.issuer_unique_id_der
                                &&& tail.subject_unique_id_der == a.subject_unique_id_der
                                &&& tail.extensions_der == a.extensions_der
                                &&& tail.extensions_sequence_der == a.extensions_sequence_der
                            },
                        },
                    },
                },
            }
        }),
    ensures
        i::parse_tlvs(sl(b, p, end)) is Some,
        ({
            let l = i::parse_tlvs(sl(b, p, end))->Some_0;
            &&& l.len() >= 5
            &&& s::decode_algorithm_identifier(l[0]) is Some
            &&& algorithm_agree(a.signature, s::decode_algorithm_identifier(l[0])->Some_0)
            &&& i::has_tag(l[1], 0, 16, true)
            &&& l[1].contents.len() > 0
            &&& l[1].encoding == a.issuer_der
            &&& s::decode_validity(l[2]) is Some
            &&& a.not_before == moment_time(time_moment(s::decode_validity(l[2])->Some_0.not_before))
            &&& a.not_after == moment_time(time_moment(s::decode_validity(l[2])->Some_0.not_after))
            &&& i::has_tag(l[3], 0, 16, true)
            &&& l[3].encoding == a.subject_der
            &&& i::has_tag(l[4], 0, 16, true)
            &&& l[4].encoding == a.subject_public_key_info_der
            &&& tail_of(l.skip(5)) is Some
            &&& tail_of(l.skip(5))->Some_0.3 == l.skip(5).len()
            &&& unique_agree(a.issuer_unique_id_der, tail_of(l.skip(5))->Some_0.0)
            &&& unique_agree(a.subject_unique_id_der, tail_of(l.skip(5))->Some_0.1)
            &&& optional_extensions_agree(a.extensions_sequence_der, tail_of(l.skip(5))->Some_0.2)
        }),
{
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(tail_of);
    hide(algorithm_agree);
    hide(unique_agree);
    hide(optional_extensions_agree);
    hide(moment_time);
    hide(parameters_plain);
    hide(extensions_decode);
    hide(s::decode_algorithm_identifier);
    hide(s::decode_validity);
    hide(t::parse_signature_issuer);
    hide(t::parse_validity);
    hide(t::parse_subject_spki);
    hide(t::parse_optional_tail);
    let (signature, issuer, p4) = t::parse_signature_issuer(b, p, end)->Some_0;
    lemma_signature_issuer_bound(b, p, end);
    let (not_before, not_after, p5) = t::parse_validity(b, p4, end)->Some_0;
    lemma_validity_fwd(b, p4, end);
    let (subject, spki, p7) = t::parse_subject_spki(b, p5, end)->Some_0;
    lemma_subject_spki_bound(b, p5, end);
    lemma_tail_fwd(b, p7, end, version);
    let l6 = i::parse_tlvs(sl(b, p7, end))->Some_0;
    lemma_subject_spki_frame(b, p5, end, l6);
    let l4 = i::parse_tlvs(sl(b, p5, end))->Some_0;
    lemma_tlvs_cons(b, p4, end, l4);
    let vu = i::parse_tlv(sl(b, p4, end))->Some_0;
    let l3 = seq![vu] + l4;
    lemma_signature_issuer_frame(b, p, end, l3);
    let l = i::parse_tlvs(sl(b, p, end))->Some_0;
    assert(l.skip(2) == l3);
    assert(l3[0] == vu);
    assert(l3[1] == l4[0]);
    assert(l3[2] == l4[1]);
    assert(l[2] == l.skip(2)[0]);
    assert(l[3] == l.skip(2)[1]);
    assert(l[4] == l.skip(2)[2]);
    lemma_skip_skip(l, 2, 3);
    assert(l3.skip(3) =~= l4.skip(2));
    assert(l.skip(5) == l4.skip(2));
}

/// A frame, from the list and what follows `serialNumber`.
#[verifier::spinoff_prover]
pub proof fn lemma_frame_build(u: i::Tlv, l: Seq<i::Tlv>, lr: Seq<i::Tlv>, version: int)
    requires
        s::sequence_elements(u) == Some(l),
        s::after_version(l) + 1 + lr.len() == l.len(),
        l.skip((s::after_version(l) + 1) as int) == lr,
        s::version_component(l) == Some(version),
        i::decode_integer(l[s::after_version(l) as int]) is Some,
        lr.len() >= 5,
        s::decode_algorithm_identifier(lr[0]) is Some,
        i::has_tag(lr[1], 0, 16, true),
        lr[1].contents.len() > 0,
        s::decode_validity(lr[2]) is Some,
        i::has_tag(lr[3], 0, 16, true),
        i::has_tag(lr[4], 0, 16, true),
        tail_of(lr.skip(5)) is Some,
        tail_of(lr.skip(5))->Some_0.3 == lr.skip(5).len(),
    ensures
        decode_tbs_frame(u) is Some,
        ({
            let f = decode_tbs_frame(u)->Some_0;
            &&& f.version == version
            &&& Some(f.serial_number) == i::decode_integer(l[s::after_version(l) as int])
            &&& Some(f.signature) == s::decode_algorithm_identifier(lr[0])
            &&& f.issuer == lr[1]
            &&& Some(f.validity) == s::decode_validity(lr[2])
            &&& f.subject == lr[3]
            &&& f.subject_public_key_info == lr[4]
            &&& f.issuer_unique_identifier == tail_of(lr.skip(5))->Some_0.0
            &&& f.subject_unique_identifier == tail_of(lr.skip(5))->Some_0.1
            &&& f.extensions == tail_of(lr.skip(5))->Some_0.2
        }),
{
    hide(s::decode_algorithm_identifier);
    hide(s::decode_validity);
    hide(tail_of);
    let m = s::after_version(l);
    assert(forall|q: int| 0 <= q < lr.len() ==> #[trigger] lr[q] == l[m as int + 1 + q]);
    assert(lr[0] == l[(m + 1) as int]);
    assert(lr[1] == l[(m + 2) as int]);
    assert(lr[2] == l[(m + 3) as int]);
    assert(lr[3] == l[(m + 4) as int]);
    assert(lr[4] == l[(m + 5) as int]);
    assert(lr.skip(5) =~= l.skip((m + 6) as int));
}

/// **The frame of a TBSCertificate, from `tbs/spec.rs`.**
#[verifier::spinoff_prover]
pub proof fn theorem_tbs_frame_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        t::parse_tbs_certificate(input) is Some,
        tbs_frame_conditions(t::parse_tbs_certificate(input)->Some_0),
    ensures
        i::parse_single(input) is Some,
        decode_tbs_frame(i::parse_single(input)->Some_0) is Some,
        tbs_frame_agree(t::parse_tbs_certificate(input)->Some_0, decode_tbs_frame(i::parse_single(input)->Some_0)->Some_0),
{
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(tail_of);
    hide(algorithm_agree);
    hide(unique_agree);
    hide(optional_extensions_agree);
    hide(moment_time);
    hide(parameters_plain);
    hide(extensions_decode);
    hide(s::decode_algorithm_identifier);
    hide(s::decode_validity);
    hide(t::parse_signature_issuer);
    hide(t::parse_validity);
    hide(t::parse_subject_spki);
    hide(t::parse_optional_tail);
    hide(t::parse_prefix);
    hide(t::parse_version);
    hide(t::parse_serial);
    hide(decode_tbs_frame);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let a = t::parse_tbs_certificate(input)->Some_0;
    let prefix = t::parse_prefix(input)->Some_0;
    lemma_prefix_opens(input);
    let outer = d::read_tlv(b, 0, len)->Some_0;
    let start = outer.cstart;
    let end = len;
    let (version, p1) = t::parse_version(b, start, end)->Some_0;
    let p2 = prefix.pos;
    lemma_tbs_prefix_position(b, start, end);
    lemma_tbs_rest_frame(b, p2, end, a, version);
    let lr = i::parse_tlvs(sl(b, p2, end))->Some_0;
    lemma_tbs_head_fwd(b, start, end, lr);
    let l = i::parse_tlvs(sl(b, start, end))->Some_0;
    let m = s::after_version(l);
    lemma_sequence_fwd(b, 0, len, l);
    lemma_read_is_plain(b, 0, len);
    lemma_single(b, 0, len);
    let u = i::parse_single(input)->Some_0;
    lemma_frame_build(u, l, lr, version as int);
}

/// **`theorem_frame_fwd`.** What `parse_certificate` and
/// `parse_tbs_certificate` read, `decode_certificate_frame` reads to the same
/// values, inside conditions 1 to 3 for those parts. Nothing is asked of the
/// issuer, the subject or the key.
#[verifier::spinoff_prover]
pub proof fn theorem_frame_fwd(der: Seq<u8>, a: c::CertificateEnvelope, tb: t::TbsCertificate)
    requires
        der.len() < two64(),
        c::parse_certificate(der) == Some(a),
        t::parse_tbs_certificate(a.tbs_certificate_der) == Some(tb),
        parameters_plain(a.signature_algorithm),
        tbs_frame_conditions(tb),
    ensures
        decode_certificate_frame(der) is Some,
        ({
            let f = decode_certificate_frame(der)->Some_0;
            &&& tbs_frame_agree(tb, f.to_be_signed)
            &&& algorithm_agree(a.signature_algorithm, f.algorithm_identifier)
            &&& f.signature.octets == a.signature_bits
            &&& f.signature.unused == a.signature_unused_bits as nat
            &&& f.tbs_encoding.encoding == a.tbs_certificate_der
        }),
{
    hide(t::parse_tbs_certificate);
    hide(c::parse_certificate);
    hide(s::decode_algorithm_identifier);
    hide(algorithm_agree);
    hide(tbs_frame_agree);
    hide(tbs_frame_conditions);
    hide(parameters_plain);
    hide(decode_tbs_frame);
    lemma_envelope_fwd(der);
    let input = a.tbs_certificate_der;
    assert(input.len() < two64()) by {
        reveal(c::parse_certificate);
        lemma_envelope_length(der);
    }
    theorem_tbs_frame_fwd(input);
    let u = i::parse_single(der)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    assert(i::parse_single(input) == Some(l[0]));
    lemma_single_is_input(input, l[0]);
}

// ---------------------------------------------------------------------
// The frame is `decode_certificate`.
// ---------------------------------------------------------------------

/// **`theorem_frame_completes`.** A frame whose three left-out components decode
/// is what `decode_certificate` reads, with one signature and no addition at
/// either level.
#[verifier::spinoff_prover]
pub proof fn theorem_frame_completes(der: Seq<u8>, f: CertificateFrame)
    requires
        decode_certificate_frame(der) == Some(f),
        s::decode_name(f.to_be_signed.issuer) is Some,
        s::decode_name(f.to_be_signed.subject) is Some,
        s::decode_subject_public_key_info(f.to_be_signed.subject_public_key_info) is Some,
    ensures
        s::decode_certificate(der) is Some,
        ({
            let y = s::decode_certificate(der)->Some_0;
            let b = y.to_be_signed;
            let g = f.to_be_signed;
            &&& b.version == g.version
            &&& b.serial_number == g.serial_number
            &&& b.signature == g.signature
            &&& Some(b.issuer) == s::decode_name(g.issuer)
            &&& b.validity == g.validity
            &&& Some(b.subject) == s::decode_name(g.subject)
            &&& Some(b.subject_public_key_info) == s::decode_subject_public_key_info(g.subject_public_key_info)
            &&& b.issuer_unique_identifier == g.issuer_unique_identifier
            &&& b.subject_unique_identifier == g.subject_unique_identifier
            &&& b.extensions == g.extensions
            &&& b.additions.len() == 0
            &&& y.additions.len() == 0
            &&& y.algorithm_identifier == f.algorithm_identifier
            &&& y.signature == f.signature
            &&& r::one_signature_only(y)
        }),
{
    hide(s::decode_algorithm_identifier);
    hide(s::decode_validity);
    hide(s::decode_name);
    hide(s::decode_subject_public_key_info);
    let u = i::parse_single(der)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    let t0 = l[0];
    let e0 = s::sequence_elements(t0)->Some_0;
    let m = s::after_version(e0);
    let lr = e0.skip((m + 1) as int);
    let g = f.to_be_signed;
    assert(lr[0] == e0[(m + 1) as int]);
    assert(lr[1] == e0[(m + 2) as int]);
    assert(lr[2] == e0[(m + 3) as int]);
    assert(lr[3] == e0[(m + 4) as int]);
    assert(lr[4] == e0[(m + 5) as int]);
    assert(lr.skip(5) =~= e0.skip((m + 6) as int));
    lemma_tbs_build(t0, e0, lr, g.version);
    let b = s::decode_tbs_certificate(t0)->Some_0;
    lemma_tail_used(e0.skip((m + 6) as int));
    lemma_certificate_closes(der);
    lemma_tbs_opens(t0, b);
    let tail = tail_of(e0.skip((m + 6) as int))->Some_0;
    assert(i::from_index(e0, m + 6 + tail.3).len() == 0);
    assert(s::alternative_signature(l) == Some((None::<s::AlgorithmIdentifier>, None::<i::BitString>, 3nat)));
}

} // verus!
