//! RFC 8446 §4.2 and the RFCs of its table: the bodies of the extensions in
//! EncryptedExtensions, CertificateRequest and a Certificate's entries. The
//! crate's `ext_body_ok` (with `auth/spec.rs`'s §4.2.5 OID rule,
//! `request_filters_distinct`) against the clean-room
//! `transcription::extension_bodies` (#140), extension by extension and then
//! block by block. [`super::auth_flight`] uses these in place of the temporary
//! `all_bodies_ok` domain it had before #140.
//!
//! What is compared:
//! - **CertificateRequest**: every body §4.2's table allows there
//!   (status_request, signature_algorithms, signed_certificate_timestamp,
//!   certificate_authorities, oid_filters, signature_algorithms_cert). A
//!   CertificateRequest's extensions are requests, so no offer is consulted;
//!   the two sides agree on every block ([`lemma_cr_bodies`]).
//! - **EncryptedExtensions**: the two sides agree on every body of the types
//!   this client offers (server_name, supported_groups). Any other type the
//!   table allows in EncryptedExtensions is one the client never offers
//!   (`auth::spec::profile_extensions`, part of the crate's `config_ok`), so
//!   both refuse the message as not offered whatever its body
//!   ([`lemma_ee_bodies`]).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The crate's `profile_extensions` as a membership fact.
pub proof fn lemma_profile_member(offers: Seq<u16>, t: u16)
    requires
        crate::auth::spec::profile_extensions(offers),
        crate::auth::spec::member(offers, t),
    ensures
        t == 0 || t == 10 || t == 13 || t == 43 || t == 44 || t == 50 || t == 51,
    decreases offers.len(),
{
    if offers[0] != t {
        lemma_profile_member(offers.skip(1), t);
    }
}

/// A body of `uint16`s: both sides read it, or neither.
pub proof fn lemma_u16s(body: Seq<u8>)
    ensures
        (crate::spec::read_u16s(body) is Some) == (crate::transcription::presentation::read_uint16_list(body) is Some),
    decreases body.len(),
{
    if body.len() >= 2 {
        assert(body.skip(2) =~= body.subrange(2, body.len() as int));
        lemma_u16s(body.skip(2));
    }
}

/// §4.2.3 SignatureSchemeList, and `signature_algorithms_cert` "with the
/// same syntax".
pub proof fn lemma_schemes(data: Seq<u8>)
    ensures
        (crate::spec::read_signature_schemes(data) is Some)
            == (crate::transcription::extensions::read_signature_scheme_list(data) is Some),
{
    super::messages::lemma_read_vec(data, 2, 0xfffe);
    match crate::spec::read_vec(data, 2, 0xfffe) {
        None => {},
        Some((body, rest)) => { lemma_u16s(body); },
    }
}

/// §4.2.7 NamedGroupList.
pub proof fn lemma_groups(data: Seq<u8>)
    ensures
        (crate::spec::read_named_groups(data) is Some)
            == (crate::transcription::extensions::read_named_group_list(data) is Some),
{
    super::messages::lemma_read_vec(data, 2, 0xffff);
    match crate::spec::read_vec(data, 2, 0xffff) {
        None => {},
        Some((body, rest)) => { lemma_u16s(body); },
    }
}

/// §4.2.4: the DistinguishedNames of a CertificateAuthoritiesExtension.
pub proof fn lemma_names(b: Seq<u8>)
    ensures
        crate::spec::read_list(b, |x: Seq<u8>| crate::spec::read_distinguished_name(x))
            == crate::transcription::extension_bodies::read_distinguished_names(b),
    decreases b.len(),
{
    let f = |x: Seq<u8>| crate::spec::read_distinguished_name(x);
    if b.len() > 0 {
        super::messages::lemma_read_vec(b, 1, 0xffff);
        assert(f(b) == crate::spec::read_vec(b, 1, 0xffff));
        match crate::spec::read_vec(b, 1, 0xffff) {
            None => {},
            Some((name, rest)) => {
                if rest.len() < b.len() {
                    lemma_names(rest);
                }
            },
        }
    }
}

/// §4.2.4 CertificateAuthoritiesExtension.
pub proof fn lemma_authorities(data: Seq<u8>)
    ensures
        crate::spec::read_certificate_authorities(data)
            == crate::transcription::extension_bodies::read_certificate_authorities(data),
{
    super::messages::lemma_read_vec(data, 3, 0xffff);
    match crate::spec::read_vec(data, 3, 0xffff) {
        None => {},
        Some((body, rest)) => { lemma_names(body); },
    }
}

/// §4.2.5: the OIDs of an OIDFilter list.
pub proof fn lemma_filters(b: Seq<u8>)
    ensures
        match crate::transcription::extension_bodies::read_oid_filters(b) {
            None => crate::spec::read_list(b, |x: Seq<u8>| crate::spec::read_oid_filter(x)) is None,
            Some(fs) => crate::spec::read_list(b, |x: Seq<u8>| crate::spec::read_oid_filter(x))
                == Some(crate::transcription::extension_bodies::filter_oids(fs)),
        },
    decreases b.len(),
{
    let f = |x: Seq<u8>| crate::spec::read_oid_filter(x);
    if b.len() == 0 {
        assert(crate::transcription::extension_bodies::filter_oids(Seq::empty()) =~= Seq::<Seq<u8>>::empty());
    } else {
        super::messages::lemma_read_vec(b, 1, 0xff);
        match crate::spec::read_vec(b, 1, 0xff) {
            None => {},
            Some((oid, r)) => {
                super::messages::lemma_read_vec(r, 0, 0xffff);
                match crate::spec::read_vec(r, 0, 0xffff) {
                    None => {},
                    Some((values, rest)) => {
                        assert(f(b) == Some((oid, rest)));
                        if rest.len() < b.len() {
                            lemma_filters(rest);
                            match crate::transcription::extension_bodies::read_oid_filters(rest) {
                                None => {},
                                Some(tail) => {
                                    let first = crate::transcription::extension_bodies::OidFilter {
                                        certificate_extension_oid: oid, certificate_extension_values: values };
                                    let fs = seq![first] + tail;
                                    assert(fs.subrange(1, fs.len() as int) =~= tail);
                                    assert(crate::transcription::extension_bodies::filter_oids(fs)
                                        =~= seq![oid] + crate::transcription::extension_bodies::filter_oids(tail));
                                },
                            }
                        }
                    },
                }
            },
        }
    }
}

/// §4.2.5 OIDFilterExtension: the crate's OIDs are the transcription's
/// filters' OIDs.
pub proof fn lemma_filter_extension(data: Seq<u8>)
    ensures
        match crate::transcription::extension_bodies::read_oid_filter_extension(data) {
            None => crate::spec::read_oid_filters(data) is None,
            Some(fs) => crate::spec::read_oid_filters(data) == Some(crate::transcription::extension_bodies::filter_oids(fs)),
        },
{
    super::messages::lemma_read_vec(data, 0, 0xffff);
    match crate::spec::read_vec(data, 0, 0xffff) {
        None => {},
        Some((body, rest)) => { lemma_filters(body); },
    }
}

/// `list_has` is membership.
pub proof fn lemma_list_has(values: Seq<Seq<u8>>, value: Seq<u8>)
    ensures
        crate::transcription::presentation::list_has(values, value)
            == (exists|k: int| 0 <= k < values.len() && values[k] == value),
    decreases values.len(),
{
    if values.len() > 0 {
        let tail = values.subrange(1, values.len() as int);
        lemma_list_has(tail, value);
        if exists|k: int| 0 <= k < values.len() && values[k] == value {
            let k = choose|k: int| 0 <= k < values.len() && values[k] == value;
            if k > 0 {
                assert(tail[k - 1] == value);
            }
        }
        if exists|k: int| 0 <= k < tail.len() && tail[k] == value {
            let k = choose|k: int| 0 <= k < tail.len() && tail[k] == value;
            assert(values[k + 1] == value);
        }
    }
}

/// §4.2.5's rule: no repeated value, read both ways.
pub proof fn lemma_no_repeats(values: Seq<Seq<u8>>)
    ensures
        crate::transcription::extension_bodies::has_no_repeated_bytes(values)
            == (forall|i: int, j: int| 0 <= i < j < values.len() ==> values[i] != values[j]),
    decreases values.len(),
{
    if values.len() > 0 {
        let tail = values.subrange(1, values.len() as int);
        lemma_no_repeats(tail);
        lemma_list_has(tail, values[0]);
        if forall|i: int, j: int| 0 <= i < j < values.len() ==> values[i] != values[j] {
            assert forall|i: int, j: int| 0 <= i < j < tail.len() implies tail[i] != tail[j] by {
                assert(values[i + 1] != values[j + 1]);
            }
            assert forall|k: int| 0 <= k < tail.len() implies tail[k] != values[0] by {
                assert(values[0] != values[k + 1]);
            }
        }
        if crate::transcription::extension_bodies::has_no_repeated_bytes(values) {
            assert forall|i: int, j: int| 0 <= i < j < values.len() implies values[i] != values[j] by {
                if i == 0 {
                    assert(tail[j - 1] == values[j]);
                } else {
                    assert(tail[i - 1] != tail[j - 1]);
                }
            }
        }
    }
}

/// §4.2.5 on one oid_filters body the crate reads: its distinct-OID rule is
/// the transcription's `body_semantics_valid`.
pub proof fn lemma_filters_distinct(data: Seq<u8>)
    requires
        crate::spec::read_oid_filters(data) is Some,
    ensures
        crate::transcription::extension_bodies::read_oid_filter_extension(data) is Some,
        crate::spec::oid_filters_distinct(data)
            == crate::transcription::extension_bodies::has_no_repeated_bytes(
                crate::transcription::extension_bodies::filter_oids(
                    crate::transcription::extension_bodies::read_oid_filter_extension(data)->0)),
{
    lemma_filter_extension(data);
    lemma_no_repeats(crate::spec::read_oid_filters(data)->0);
    crate::lemmas_ext::lemma_oids_distinct(crate::spec::read_oid_filters(data)->0);
}

/// One extension of a CertificateRequest the crate allows there: its body's
/// failures on the transcription's side, by the crate's two checks.
pub proof fn lemma_cr_body(e: crate::spec::Ext)
    requires
        crate::spec::extension_allowed(e.etype, crate::spec::MsgKind::Cr),
    ensures ({
        let f = crate::transcription::extension_bodies::one_body_failures(seq![], super::messages::ext_view(e),
            crate::transcription::extensions::TableMessage::Cr);
        let ok = crate::spec::ext_body_ok(e, crate::spec::MsgKind::Cr);
        let distinct = e.etype != crate::spec::EXT_OID_FILTERS || crate::spec::oid_filters_distinct(e.data);
        &&& !ok ==> f == seq![crate::transcription::alerts::ClientError::Malformed]
        &&& ok && distinct ==> f.len() == 0
        &&& ok && !distinct ==> f == seq![crate::transcription::alerts::ClientError::ExtensionBodyInvalid(48)]
    }),
{
    super::extensions::lemma_table(e.etype, crate::spec::MsgKind::Cr);
    lemma_schemes(e.data);
    lemma_authorities(e.data);
    lemma_filter_extension(e.data);
    if crate::spec::read_oid_filters(e.data) is Some {
        lemma_filters_distinct(e.data);
    }
}

/// A CertificateRequest's block, its extensions all allowed there: the
/// transcription's body failures are empty exactly when the crate's checks
/// pass, and otherwise hold the crate's alert.
pub proof fn lemma_cr_bodies(es: Seq<crate::spec::Ext>)
    requires
        crate::spec::all_allowed(es, crate::spec::MsgKind::Cr),
    ensures ({
        let f = crate::transcription::extension_bodies::extension_body_failures(seq![], super::messages::exts_view(es),
            crate::transcription::extensions::TableMessage::Cr);
        &&& (f.len() == 0) == (crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Cr)
            && crate::auth::spec::request_filters_distinct(es))
        &&& !crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Cr) ==> super::auth_flight::alert_in(50, f)
        &&& crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Cr) && !crate::auth::spec::request_filters_distinct(es)
            ==> super::auth_flight::alert_in(47, f)
    }),
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    let f = crate::transcription::extension_bodies::extension_body_failures(seq![], v,
        crate::transcription::extensions::TableMessage::Cr);
    if es.len() > 0 {
        let rest = es.skip(1);
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(rest));
        assert(v[0] == super::messages::ext_view(es[0]));
        assert(crate::spec::extension_allowed(es[0].etype, crate::spec::MsgKind::Cr));
        lemma_cr_bodies(rest);
        lemma_cr_body(es[0]);
        let mine = crate::transcription::extension_bodies::one_body_failures(seq![], v[0],
            crate::transcription::extensions::TableMessage::Cr);
        let tail = crate::transcription::extension_bodies::extension_body_failures(seq![], super::messages::exts_view(rest),
            crate::transcription::extensions::TableMessage::Cr);
        assert(f == mine + tail);
        if mine.len() > 0 {
            assert(f[0] == mine[0]);
            assert(crate::transcription::alerts::required_alert(f[0]) == crate::transcription::alerts::required_alert(mine[0]));
        }
        if super::auth_flight::alert_in(50, tail) {
            let i = choose|i: int| 0 <= i < tail.len()
                && #[trigger] crate::transcription::alerts::required_alert(tail[i]) == 50nat;
            assert(f[mine.len() + i] == tail[i]);
        }
        if super::auth_flight::alert_in(47, tail) {
            let i = choose|i: int| 0 <= i < tail.len()
                && #[trigger] crate::transcription::alerts::required_alert(tail[i]) == 47nat;
            assert(f[mine.len() + i] == tail[i]);
        }
    }
}

/// One extension of an EncryptedExtensions the crate allows there.
pub proof fn lemma_ee_body(e: crate::spec::Ext, sent: Seq<crate::transcription::extensions::Extension>)
    requires
        crate::spec::extension_allowed(e.etype, crate::spec::MsgKind::Ee),
    ensures ({
        let f = crate::transcription::extension_bodies::one_body_failures(sent, super::messages::ext_view(e),
            crate::transcription::extensions::TableMessage::Ee);
        let ok = crate::spec::ext_body_ok(e, crate::spec::MsgKind::Ee);
        &&& !ok ==> f == seq![crate::transcription::alerts::ClientError::Malformed]
        &&& f.len() == 0 ==> ok
        &&& ok && (e.etype == 0 || e.etype == 10) ==> f.len() == 0
    }),
{
    super::extensions::lemma_table(e.etype, crate::spec::MsgKind::Ee);
    lemma_groups(e.data);
}

/// An EncryptedExtensions block, its extensions all allowed there: the
/// transcription's body failures are empty only if the crate's checks pass;
/// they hold `decode_error` if the crate's fail; and they are empty if the
/// crate's pass and every extension is of a type this client offers
/// (server_name or supported_groups).
pub proof fn lemma_ee_bodies(es: Seq<crate::spec::Ext>, sent: Seq<crate::transcription::extensions::Extension>)
    requires
        crate::spec::all_allowed(es, crate::spec::MsgKind::Ee),
    ensures ({
        let f = crate::transcription::extension_bodies::extension_body_failures(sent, super::messages::exts_view(es),
            crate::transcription::extensions::TableMessage::Ee);
        &&& f.len() == 0 ==> crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Ee)
        &&& !crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Ee) ==> super::auth_flight::alert_in(50, f)
        &&& crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Ee)
            && (forall|i: int| 0 <= i < es.len() ==> (#[trigger] es[i].etype == 0 || es[i].etype == 10))
            ==> f.len() == 0
    }),
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    let f = crate::transcription::extension_bodies::extension_body_failures(sent, v,
        crate::transcription::extensions::TableMessage::Ee);
    if es.len() > 0 {
        let rest = es.skip(1);
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(rest));
        assert(v[0] == super::messages::ext_view(es[0]));
        assert(crate::spec::extension_allowed(es[0].etype, crate::spec::MsgKind::Ee));
        lemma_ee_bodies(rest, sent);
        lemma_ee_body(es[0], sent);
        let mine = crate::transcription::extension_bodies::one_body_failures(sent, v[0],
            crate::transcription::extensions::TableMessage::Ee);
        let tail = crate::transcription::extension_bodies::extension_body_failures(sent, super::messages::exts_view(rest),
            crate::transcription::extensions::TableMessage::Ee);
        assert(f == mine + tail);
        if mine.len() > 0 {
            assert(f[0] == mine[0]);
            assert(crate::transcription::alerts::required_alert(f[0]) == crate::transcription::alerts::required_alert(mine[0]));
        }
        if super::auth_flight::alert_in(50, tail) {
            let i = choose|i: int| 0 <= i < tail.len()
                && #[trigger] crate::transcription::alerts::required_alert(tail[i]) == 50nat;
            assert(f[mine.len() + i] == tail[i]);
        }
        if forall|i: int| 0 <= i < es.len() ==> (#[trigger] es[i].etype == 0 || es[i].etype == 10) {
            assert(es[0].etype == 0 || es[0].etype == 10);
            assert forall|i: int| 0 <= i < rest.len() implies (#[trigger] rest[i].etype == 0 || rest[i].etype == 10) by {
                assert(rest[i] == es[i + 1]);
            }
        }
    }
}

/// In a block the crate allows in EncryptedExtensions whose extensions were
/// all offered by a client of the crate's profile, every type is server_name
/// or supported_groups.
pub proof fn lemma_ee_offered_types(es: Seq<crate::spec::Ext>, offers: Seq<u16>)
    requires
        crate::spec::all_allowed(es, crate::spec::MsgKind::Ee),
        crate::auth::spec::extensions_offered(es, offers),
        crate::auth::spec::profile_extensions(offers),
    ensures
        forall|i: int| 0 <= i < es.len() ==> (#[trigger] es[i].etype == 0 || es[i].etype == 10),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_ee_offered_types(es.skip(1), offers);
        lemma_profile_member(offers, es[0].etype);
        assert forall|i: int| 0 <= i < es.len() implies (#[trigger] es[i].etype == 0 || es[i].etype == 10) by {
            if i > 0 {
                assert(es[i] == es.skip(1)[i - 1]);
            }
        }
    }
}

/// In a Certificate entry whose extensions the crate allows there and were
/// all offered by a client of the crate's profile, there are none: no type
/// of the profile is allowed in a Certificate entry.
pub proof fn lemma_ct_offered_empty(es: Seq<crate::spec::Ext>, offers: Seq<u16>)
    requires
        crate::spec::all_allowed(es, crate::spec::MsgKind::Ct),
        crate::auth::spec::extensions_offered(es, offers),
        crate::auth::spec::profile_extensions(offers),
    ensures
        es.len() == 0,
{
    if es.len() > 0 {
        lemma_profile_member(offers, es[0].etype);
    }
}

} // verus!
