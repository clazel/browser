//! RFC 8446 §3.4, §4, §4.2 and §4.4.2: the crate's readers of vectors,
//! extension blocks, the handshake header, the `select` on `msg_type` and
//! `Certificate` proven equal to the clean-room transcription's, for every
//! input: [`theorem_certificate_select_equivalence`].
//!
//! How the two are compared: a crate `Ext` is a transcription `Extension`
//! with the type widened from `u16` to `nat` ([`ext_view`]), and so on up to
//! `Certificate` ([`certificate_view`]). A reader agrees when both refuse,
//! or both accept with the same value and the same bytes left over.
//!
//! The `select`. The crate's `parse_handshake_body` refuses a type with no
//! arm (`unexpected_message`) before it reads the body; the transcription's
//! `select_handshake` returns `None` for both a type with no arm and a body
//! that does not parse, and its state machine reports "unexpected in this
//! state" before syntax. So what is compared is the set of types with an
//! arm (the same ten; `message_hash` has none on either side) and, for each
//! of the crate's body readers, the body: here `Certificate`; the others
//! with the area that reads them.
//!
//! What only one side checks: the crate's `parse_handshake_body` also
//! applies §4.2's extension rules to each entry of a Certificate
//! (`certificate_entries_error`); the transcription applies them against
//! the offer in `certificate_failures`. That is the authentication area's
//! comparison, not the syntax's.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A crate extension as the transcription's.
pub open spec fn ext_view(e: crate::spec::Ext) -> crate::transcription::extensions::Extension {
    crate::transcription::extensions::Extension { extension_type: e.etype as nat, extension_data: e.data }
}

/// A crate extension block as the transcription's.
pub open spec fn exts_view(es: Seq<crate::spec::Ext>) -> Seq<crate::transcription::extensions::Extension> {
    es.map_values(|e: crate::spec::Ext| ext_view(e))
}

/// A crate CertificateEntry as the transcription's.
pub open spec fn entry_view(e: crate::spec::CertificateEntry) -> crate::transcription::authentication::CertificateEntry {
    crate::transcription::authentication::CertificateEntry { cert_data: e.cert_data, extensions: exts_view(e.extensions) }
}

/// A crate Certificate as the transcription's.
pub open spec fn certificate_view(c: crate::spec::Certificate) -> crate::transcription::authentication::Certificate {
    crate::transcription::authentication::Certificate {
        certificate_request_context: c.context,
        certificate_list: c.entries.map_values(|e: crate::spec::CertificateEntry| entry_view(e)),
    }
}

/// Whether the transcription's `select` has an arm for `t`.
pub open spec fn has_arm(t: nat) -> bool {
    t == crate::transcription::key_exchange::ht_client_hello()
        || t == crate::transcription::key_exchange::ht_server_hello()
        || t == crate::transcription::key_exchange::ht_end_of_early_data()
        || t == crate::transcription::key_exchange::ht_encrypted_extensions()
        || t == crate::transcription::key_exchange::ht_certificate_request()
        || t == crate::transcription::key_exchange::ht_certificate()
        || t == crate::transcription::key_exchange::ht_certificate_verify()
        || t == crate::transcription::key_exchange::ht_finished()
        || t == crate::transcription::key_exchange::ht_new_session_ticket()
        || t == crate::transcription::key_exchange::ht_key_update()
}

/// §3.4: the crate's `read_vec` is the transcription's `read_vector`, for
/// every ceiling below 2^24.
pub proof fn lemma_read_vec(b: Seq<u8>, floor: nat, ceil: nat)
    requires ceil < 0x100_0000,
    ensures crate::spec::read_vec(b, floor, ceil) == crate::transcription::presentation::read_vector(b, floor, ceil),
{
    let w = crate::spec::len_width(ceil);
    assert(w == crate::transcription::presentation::length_field_width(ceil));
    if b.len() >= w {
        super::record::lemma_read_uint(b, w);
        let n = crate::spec::be_value(b.take(w as int));
        let r = b.skip(w as int);
        if !(n < floor || n > ceil || r.len() < n) {
            assert(r.take(n as int) =~= b.subrange(w as int, (w + n) as int));
            assert(r.skip(n as int) =~= b.subrange((w + n) as int, b.len() as int));
        }
    }
}

/// §4.2: one extension's elements read the same on both sides.
pub proof fn lemma_read_ext_list(b: Seq<u8>)
    ensures
        match crate::spec::read_list(b, |x: Seq<u8>| crate::spec::read_ext(x)) {
            None => crate::transcription::extensions::read_extension_list(b) is None,
            Some(es) => crate::transcription::extensions::read_extension_list(b) == Some(exts_view(es)),
        },
    decreases b.len(),
{
    let f = |x: Seq<u8>| crate::spec::read_ext(x);
    if b.len() == 0 {
        assert(exts_view(Seq::<crate::spec::Ext>::empty()) =~= Seq::<crate::transcription::extensions::Extension>::empty());
    } else if b.len() < 4 {
        if b.len() >= 2 {
            lemma_read_vec(b.skip(2), 0, 65535);
        }
    } else {
        let r = b.skip(2);
        assert(r =~= b.subrange(2, b.len() as int));
        lemma_read_vec(r, 0, 65535);
        super::record::lemma_read_uint(b, 2);
        crate::lemmas_pl::lemma_be_value_bound(b.take(2));
        crate::lemmas_pl::lemma_pow256_widths();
        match crate::transcription::presentation::read_vector(r, 0, 0xffff) {
            None => {},
            Some((data, rest)) => {
                assert(rest =~= b.subrange((4 + data.len()) as int, b.len() as int));
                lemma_read_ext_list(rest);
                match crate::spec::read_list(rest, f) {
                    None => {},
                    Some(es) => {
                        let e = crate::spec::Ext { etype: crate::spec::be_value(b.take(2)) as u16, data };
                        assert(f(b) == Some((e, rest)));
                        assert(crate::spec::read_list(b, f) == Some(seq![e] + es));
                        assert(exts_view(seq![e] + es) =~= seq![ext_view(e)] + exts_view(es));
                    },
                }
            },
        }
    }
}

/// §4.2: an extension block reads the same on both sides.
pub proof fn lemma_read_exts(b: Seq<u8>, floor: nat, ceil: nat)
    requires ceil < 0x100_0000,
    ensures
        match crate::spec::read_exts(b, floor, ceil) {
            None => crate::transcription::extensions::read_extensions(b, floor, ceil) is None,
            Some((es, rest)) => crate::transcription::extensions::read_extensions(b, floor, ceil) == Some((exts_view(es), rest)),
        },
{
    lemma_read_vec(b, floor, ceil);
    match crate::spec::read_vec(b, floor, ceil) {
        None => {},
        Some((c, r)) => { lemma_read_ext_list(c); },
    }
}

/// §4.4.2: the entries of `certificate_list` read the same on both sides.
pub proof fn lemma_read_entries(b: Seq<u8>)
    ensures
        match crate::spec::read_list(b, |x: Seq<u8>| crate::spec::read_certificate_entry(x)) {
            None => crate::transcription::authentication::read_certificate_entries(b) is None,
            Some(es) => crate::transcription::authentication::read_certificate_entries(b)
                == Some(es.map_values(|e: crate::spec::CertificateEntry| entry_view(e))),
        },
    decreases b.len(),
{
    let f = |x: Seq<u8>| crate::spec::read_certificate_entry(x);
    if b.len() == 0 {
        assert(Seq::<crate::spec::CertificateEntry>::empty().map_values(|e: crate::spec::CertificateEntry| entry_view(e))
            =~= Seq::<crate::transcription::authentication::CertificateEntry>::empty());
    } else {
        lemma_read_vec(b, 1, 0xff_ffff);
        match crate::spec::read_vec(b, 1, 0xff_ffff) {
            None => {},
            Some((cert, r1)) => {
                lemma_read_vec(r1, 0, 0xffff);
                lemma_read_exts(r1, 0, 0xffff);
                match crate::spec::read_vec(r1, 0, 0xffff) {
                    None => {},
                    Some((ext_bytes, rest)) => {
                        assert(b.len() >= 3 + cert.len() + 2 + ext_bytes.len());
                        assert(rest =~= b.subrange((3 + cert.len() + 2 + ext_bytes.len()) as int, b.len() as int));
                        lemma_read_ext_list(ext_bytes);
                        lemma_read_entries(rest);
                        match crate::spec::read_list(ext_bytes, |x: Seq<u8>| crate::spec::read_ext(x)) {
                            None => {},
                            Some(exts) => {
                                let e = crate::spec::CertificateEntry { cert_data: cert, extensions: exts };
                                assert(f(b) == Some((e, rest)));
                                match crate::spec::read_list(rest, f) {
                                    None => {},
                                    Some(es) => {
                                        assert(crate::spec::read_list(b, f) == Some(seq![e] + es));
                                        assert((seq![e] + es).map_values(|e: crate::spec::CertificateEntry| entry_view(e))
                                            =~= seq![entry_view(e)] + es.map_values(|e: crate::spec::CertificateEntry| entry_view(e)));
                                    },
                                }
                            },
                        }
                    },
                }
            },
        }
    }
}

/// §4.4.2: a Certificate body reads the same on both sides.
pub proof fn lemma_read_certificate(b: Seq<u8>)
    ensures
        match crate::spec::read_certificate(b) {
            None => crate::transcription::authentication::read_certificate(b) is None,
            Some(c) => crate::transcription::authentication::read_certificate(b) == Some(certificate_view(c)),
        },
{
    lemma_read_vec(b, 0, 255);
    match crate::spec::read_vec(b, 0, 255) {
        None => {},
        Some((ctx, r1)) => {
            lemma_read_vec(r1, 0, 0xff_ffff);
            match crate::spec::read_vec(r1, 0, 0xff_ffff) {
                None => {},
                Some((list, rest)) => { lemma_read_entries(list); },
            }
        },
    }
}

/// §4: the handshake headers read the same on both sides.
pub proof fn lemma_read_handshake_header(b: Seq<u8>)
    ensures
        match crate::spec::read_handshake_header(b) {
            None => crate::transcription::key_exchange::read_handshake_header(b) is None,
            Some((t, len)) => crate::transcription::key_exchange::read_handshake_header(b)
                == Some(crate::transcription::key_exchange::HandshakeHeader { msg_type: t as nat, length: len }),
        },
{
    if b.len() >= 4 {
        super::record::lemma_read_uint(b.subrange(1, 4), 3);
        assert(b.subrange(1, 4).take(3) =~= b.subrange(1, 4));
    }
}

/// RFC 8446 §3.4, §4, §4.2 and §4.4.2, for every input: vectors below
/// 2^24, extension blocks, the handshake header and Certificate read the
/// same on both sides, and the `select` on `msg_type` has an arm for exactly
/// the crate's known types.
pub proof fn theorem_certificate_select_equivalence()
    ensures
        forall|b: Seq<u8>, floor: nat, ceil: nat| ceil < 0x100_0000 ==>
            #[trigger] crate::spec::read_vec(b, floor, ceil) == crate::transcription::presentation::read_vector(b, floor, ceil),
        forall|b: Seq<u8>, floor: nat, ceil: nat| ceil < 0x100_0000 ==>
            match #[trigger] crate::spec::read_exts(b, floor, ceil) {
                None => crate::transcription::extensions::read_extensions(b, floor, ceil) is None,
                Some((es, rest)) => crate::transcription::extensions::read_extensions(b, floor, ceil) == Some((exts_view(es), rest)),
            },
        forall|b: Seq<u8>| match #[trigger] crate::spec::read_certificate(b) {
            None => crate::transcription::authentication::read_certificate(b) is None,
            Some(c) => crate::transcription::authentication::read_certificate(b) == Some(certificate_view(c)),
        },
        forall|b: Seq<u8>| match #[trigger] crate::spec::read_handshake_header(b) {
            None => crate::transcription::key_exchange::read_handshake_header(b) is None,
            Some((t, len)) => crate::transcription::key_exchange::read_handshake_header(b)
                == Some(crate::transcription::key_exchange::HandshakeHeader { msg_type: t as nat, length: len }),
        },
        forall|t: u8| #[trigger] crate::spec::handshake_type_known(t) <==> has_arm(t as nat),
        forall|t: nat, body: Seq<u8>| !has_arm(t) ==> #[trigger] crate::transcription::key_exchange::select_handshake(t, body) is None,
        forall|body: Seq<u8>, hash_len: nat|
            (#[trigger] crate::spec::parse_handshake_body(crate::spec::HS_CERTIFICATE, body, hash_len)) is Ok ==>
                crate::transcription::key_exchange::select_handshake(crate::transcription::key_exchange::ht_certificate(), body)
                    == Some(crate::transcription::key_exchange::HandshakeBody::Certificate(
                        certificate_view(crate::spec::read_certificate(body)->Some_0))),
{
    assert forall|b: Seq<u8>, floor: nat, ceil: nat| ceil < 0x100_0000 implies
        #[trigger] crate::spec::read_vec(b, floor, ceil) == crate::transcription::presentation::read_vector(b, floor, ceil)
    by { lemma_read_vec(b, floor, ceil); }
    assert forall|b: Seq<u8>, floor: nat, ceil: nat| ceil < 0x100_0000 implies
        match #[trigger] crate::spec::read_exts(b, floor, ceil) {
            None => crate::transcription::extensions::read_extensions(b, floor, ceil) is None,
            Some((es, rest)) => crate::transcription::extensions::read_extensions(b, floor, ceil) == Some((exts_view(es), rest)),
        }
    by { lemma_read_exts(b, floor, ceil); }
    assert forall|b: Seq<u8>| match #[trigger] crate::spec::read_certificate(b) {
        None => crate::transcription::authentication::read_certificate(b) is None,
        Some(c) => crate::transcription::authentication::read_certificate(b) == Some(certificate_view(c)),
    } by { lemma_read_certificate(b); }
    assert forall|b: Seq<u8>| match #[trigger] crate::spec::read_handshake_header(b) {
        None => crate::transcription::key_exchange::read_handshake_header(b) is None,
        Some((t, len)) => crate::transcription::key_exchange::read_handshake_header(b)
            == Some(crate::transcription::key_exchange::HandshakeHeader { msg_type: t as nat, length: len }),
    } by { lemma_read_handshake_header(b); }
    assert forall|body: Seq<u8>, hash_len: nat|
        (#[trigger] crate::spec::parse_handshake_body(crate::spec::HS_CERTIFICATE, body, hash_len)) is Ok implies
            crate::transcription::key_exchange::select_handshake(crate::transcription::key_exchange::ht_certificate(), body)
                == Some(crate::transcription::key_exchange::HandshakeBody::Certificate(
                    certificate_view(crate::spec::read_certificate(body)->Some_0)))
    by { lemma_read_certificate(body); }
}

} // verus!
