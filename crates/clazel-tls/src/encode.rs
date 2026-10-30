//! The executable encoders of the messages the client sends (RFC 8446 §4
//! and §6): ClientHello, the Handshake header around any message,
//! Finished, KeyUpdate, the empty Certificate that refuses a
//! CertificateRequest, and alerts. Each is proven to append exactly what
//! the spec's writer writes.

use super::spec::{Alert, ErrKind};
use super::types::{
    Certificate, CertificateRequest, CertificateVerify, ClientHello, Extension, NewSessionTicket,
    ServerHello,
};
use super::writer::{push_be, push_u16, push_vec};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §3.3, §3.4: append a list of `uint16`
/// ([`super::spec::write_u16s`]).
pub fn push_u16s(out: &mut Vec<u8>, vs: &[u16])
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_u16s(vs@),
{
    let mut i: usize = 0;
    proof {
        assert(vs@.take(0) =~= Seq::<u16>::empty());
        assert(old(out)@ + super::spec::write_u16s(Seq::<u16>::empty()) =~= old(out)@);
    }
    while i < vs.len()
        invariant
            i <= vs@.len(),
            out@ =~= old(out)@ + super::spec::write_u16s(vs@.take(i as int)),
        decreases vs@.len() - i,
    {
        let v = match vs.get(i) {
            Some(&v) => v,
            None => 0,
        };
        proof {
            let w = |x: u16| super::spec::write_u16(x);
            super::lemmas_pl::lemma_write_list_push(vs@.take(i as int), v, w);
            assert(vs@.take(i as int + 1) =~= vs@.take(i as int).push(v));
            assert(old(out)@ + super::spec::write_u16s(vs@.take(i as int)) + super::spec::write_u16(v) =~= old(out)@ + (
            super::spec::write_u16s(vs@.take(i as int)) + super::spec::write_u16(v)));
        }
        push_u16(out, v);
        // i < len, so this does not saturate.
        i = i.saturating_add(1);
    }
    proof {
        assert(vs@.take(vs@.len() as int) =~= vs@);
    }
}

/// §4.2: append a list of extensions ([`super::spec::write_ext`] of each).
pub fn push_extensions(out: &mut Vec<u8>, es: &[Extension<'_>])
    requires
        forall|i: int| 0 <= i < es@.len() ==> (#[trigger] es@[i]).data@.len() <= 65535,
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_list(super::types::views(es@), |e: super::spec::Ext| super::spec::write_ext(e)),
{
    let mut i: usize = 0;
    proof {
        assert(super::types::views(es@).take(0) =~= Seq::<super::spec::Ext>::empty());
        assert(old(out)@ + super::spec::write_list(
            Seq::<super::spec::Ext>::empty(),
            |e: super::spec::Ext| super::spec::write_ext(e),
        ) =~= old(out)@);
    }
    while i < es.len()
        invariant
            i <= es@.len(),
            forall|k: int| 0 <= k < es@.len() ==> (#[trigger] es@[k]).data@.len() <= 65535,
            out@ =~= old(out)@ + super::spec::write_list(
                super::types::views(es@).take(i as int),
                |e: super::spec::Ext| super::spec::write_ext(e),
            ),
        decreases es@.len() - i,
    {
        let e = match es.get(i) {
            Some(e) => e,
            None => {
                proof {
                    assert(false);
                }
                return ;
            },
        };
        let t = e.etype;
        let d = e.data;
        proof {
            let w = |e: super::spec::Ext| super::spec::write_ext(e);
            let pre = super::types::views(es@).take(i as int);
            super::lemmas_pl::lemma_write_list_push(pre, super::types::views(es@)[i as int], w);
            assert(super::types::views(es@).take(i as int + 1) =~= pre.push(super::types::views(es@)[i as int]));
            assert(super::types::views(es@)[i as int] == es@[i as int]@);
        }
        push_u16(out, t);
        push_vec(out, d, 65535);
        proof {
            let w = |e: super::spec::Ext| super::spec::write_ext(e);
            let pre = super::types::views(es@).take(i as int);
            assert(super::spec::write_ext(super::types::views(es@)[i as int]) =~= super::spec::write_u16(t) + super::spec::write_vec(
                d@,
                65535,
            ));
            assert(old(out)@ + super::spec::write_list(pre, w) + super::spec::write_u16(t) + super::spec::write_vec(d@, 65535)
                =~= old(out)@ + (super::spec::write_list(pre, w) + super::spec::write_ext(super::types::views(es@)[i as int])));
        }
        // i < len, so this does not saturate.
        i = i.saturating_add(1);
    }
    proof {
        assert(super::types::views(es@).take(super::types::views(es@).len() as int) =~= super::types::views(es@));
    }
}

/// §4.1.2: append a ClientHello's body ([`super::spec::write_client_hello`]).
pub fn write_client_hello(out: &mut Vec<u8>, ch: &ClientHello<'_>)
    requires
        super::contract::client_hello_requires(ch@),
    ensures
        super::contract::write_client_hello_ensures(old(out)@, ch@, final(out)@),
{
    push_u16(out, ch.legacy_version);
    out.extend_from_slice(ch.random);
    push_vec(out, ch.session_id, 32);
    let mut suites: Vec<u8> = Vec::new();
    push_u16s(&mut suites, ch.cipher_suites.as_slice());
    proof {
        super::lemmas_pl::lemma_write_u16s_len(ch.cipher_suites@);
        assert(suites@ =~= Seq::<u8>::empty() + super::spec::write_u16s(ch.cipher_suites@));
    }
    push_vec(out, suites.as_slice(), 65534);
    push_vec(out, ch.compression, 255);
    let mut exts: Vec<u8> = Vec::new();
    proof {
        assert forall|i: int| 0 <= i < ch.extensions@.len() implies (#[trigger] ch.extensions@[i]).data@.len() <= 65535 by {
            assert(super::types::views(ch.extensions@)[i] == ch.extensions@[i]@);
        }
    }
    push_extensions(&mut exts, ch.extensions.as_slice());
    proof {
        assert(exts@ =~= Seq::<u8>::empty() + super::spec::write_list(
            super::types::views(ch.extensions@),
            |e: super::spec::Ext| super::spec::write_ext(e),
        ));
    }
    push_vec(out, exts.as_slice(), 65535);
    proof {
        let ch_spec = ch@;
        assert(out@ =~= old(out)@ + super::spec::write_client_hello(ch_spec));
    }
}

/// §4: append a handshake message of type `t` with body `body`: the type,
/// the length in three bytes, and the body ([`super::spec::write_handshake`]).
pub fn write_handshake(out: &mut Vec<u8>, t: u8, body: &[u8])
    requires
        body.len() < 16777216,
    ensures
        super::contract::write_handshake_ensures(old(out)@, t, body@, final(out)@),
{
    out.push(t);
    proof {
        super::lemmas_pl::lemma_pow256_widths();
    }
    push_be(out, body.len() as u64, 3);
    out.extend_from_slice(body);
    proof {
        assert(out@ =~= old(out)@ + super::spec::write_handshake(t, body@));
    }
}

/// §4.6.3: append a KeyUpdate's body ([`super::spec::write_key_update`]).
pub fn write_key_update(out: &mut Vec<u8>, request_update: u8)
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_key_update(request_update),
{
    out.push(request_update);
}

/// §4.4.2: append the body of the Certificate that refuses a
/// CertificateRequest: its context and no entries (§4.4.2: "the client
/// MUST send a Certificate message containing no certificates")
/// ([`super::spec::write_certificate`] with no entries).
pub fn write_empty_certificate(out: &mut Vec<u8>, context: &[u8])
    requires
        context.len() <= 255,
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_certificate(
            super::spec::Certificate { context: context@, entries: seq![] },
        ),
{
    push_vec(out, context, 255);
    let empty: Vec<u8> = Vec::new();
    push_vec(out, empty.as_slice(), 16777215);
    proof {
        let c = super::spec::Certificate { context: context@, entries: seq![] };
        assert(super::spec::write_list(c.entries, |e: super::spec::CertificateEntry| super::spec::write_certificate_entry(e))
            =~= Seq::<u8>::empty());
        assert(out@ =~= old(out)@ + super::spec::write_certificate(c));
    }
}

/// §6: append an alert ([`super::spec::write_alert`]).
pub fn write_alert(out: &mut Vec<u8>, a: Alert)
    ensures
        super::contract::write_alert_ensures(old(out)@, a, final(out)@),
{
    out.push(a.level);
    out.push(a.description);
    proof {
        assert(out@ =~= old(out)@ + super::spec::write_alert(a));
    }
}

/// §6: read an alert ([`super::spec::read_alert`]).
pub fn read_alert(b: &[u8]) -> (r: Option<Alert>)
    ensures
        super::contract::read_alert_ensures(b@, r),
{
    if b.len() == 2 {
        let level = super::reader::byte_at(b, 0);
        let description = super::reader::byte_at(b, 1);
        Some(Alert { level, description })
    } else {
        None
    }
}

/// §4.2: the bytes of an extension block `Extension extensions<_..ceil>`:
/// the length, then the extensions.
pub fn push_extension_block(out: &mut Vec<u8>, es: &[Extension<'_>], ceil: usize)
    requires
        ceil < 16777216,
        forall|i: int| 0 <= i < es@.len() ==> (#[trigger] es@[i]).data@.len() <= 65535,
        super::spec::write_list(super::types::views(es@), |e: super::spec::Ext| super::spec::write_ext(e)).len() <= ceil,
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_exts(super::types::views(es@), ceil as nat),
{
    let mut exts: Vec<u8> = Vec::new();
    push_extensions(&mut exts, es);
    proof {
        assert(exts@ =~= Seq::<u8>::empty() + super::spec::write_list(
            super::types::views(es@),
            |e: super::spec::Ext| super::spec::write_ext(e),
        ));
    }
    push_vec(out, exts.as_slice(), ceil);
}

/// §4.1.3: append a ServerHello's body ([`super::spec::write_server_hello`]).
pub fn write_server_hello(out: &mut Vec<u8>, sh: &ServerHello<'_>)
    requires
        super::lemmas_hs::server_hello_requires(sh@),
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_server_hello(sh@),
{
    push_u16(out, sh.legacy_version);
    out.extend_from_slice(sh.random);
    push_vec(out, sh.session_id_echo, 32);
    push_u16(out, sh.cipher_suite);
    out.push(sh.compression);
    proof {
        assert forall|i: int| 0 <= i < sh.extensions@.len() implies (#[trigger] sh.extensions@[i]).data@.len() <= 65535 by {
            assert(super::types::views(sh.extensions@)[i] == sh.extensions@[i]@);
        }
    }
    push_extension_block(out, sh.extensions.as_slice(), 65535);
    proof {
        assert(out@ =~= old(out)@ + super::spec::write_server_hello(sh@));
    }
}

/// §4.3.1: append an EncryptedExtensions body
/// ([`super::spec::write_encrypted_extensions`]).
pub fn write_encrypted_extensions(out: &mut Vec<u8>, es: &[Extension<'_>])
    requires
        forall|i: int| 0 <= i < es@.len() ==> (#[trigger] es@[i]).data@.len() <= 65535,
        super::spec::write_list(super::types::views(es@), |e: super::spec::Ext| super::spec::write_ext(e)).len() <= 65535,
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_encrypted_extensions(super::types::views(es@)),
{
    push_extension_block(out, es, 65535);
}

/// §4.3.2: append a CertificateRequest body
/// ([`super::spec::write_certificate_request`]).
pub fn write_certificate_request(out: &mut Vec<u8>, c: &CertificateRequest<'_>)
    requires
        c.context@.len() <= 255,
        forall|i: int| 0 <= i < c.extensions@.len() ==> (#[trigger] c.extensions@[i]).data@.len() <= 65535,
        super::spec::write_list(super::types::views(c.extensions@), |e: super::spec::Ext| super::spec::write_ext(e)).len()
            <= 65535,
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_certificate_request(c@),
{
    push_vec(out, c.context, 255);
    push_extension_block(out, c.extensions.as_slice(), 65535);
    proof {
        assert(out@ =~= old(out)@ + super::spec::write_certificate_request(c@));
    }
}

/// §4.4.3: append a CertificateVerify body
/// ([`super::spec::write_certificate_verify`]).
pub fn write_certificate_verify(out: &mut Vec<u8>, c: &CertificateVerify<'_>)
    requires
        c.signature@.len() <= 65535,
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_certificate_verify(c@),
{
    push_u16(out, c.algorithm);
    push_vec(out, c.signature, 65535);
    proof {
        assert(out@ =~= old(out)@ + super::spec::write_certificate_verify(c@));
    }
}

/// §4.6.1: append a NewSessionTicket body
/// ([`super::spec::write_new_session_ticket`]).
pub fn write_new_session_ticket(out: &mut Vec<u8>, n: &NewSessionTicket<'_>)
    requires
        n.ticket_nonce@.len() <= 255,
        n.ticket@.len() <= 65535,
        forall|i: int| 0 <= i < n.extensions@.len() ==> (#[trigger] n.extensions@[i]).data@.len() <= 65535,
        super::spec::write_list(super::types::views(n.extensions@), |e: super::spec::Ext| super::spec::write_ext(e)).len()
            <= 65534,
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_new_session_ticket(n@),
{
    proof {
        super::lemmas_pl::lemma_pow256_widths();
    }
    push_be(out, n.ticket_lifetime as u64, 4);
    push_be(out, n.ticket_age_add as u64, 4);
    push_vec(out, n.ticket_nonce, 255);
    push_vec(out, n.ticket, 65535);
    push_extension_block(out, n.extensions.as_slice(), 65534);
    proof {
        assert(out@ =~= old(out)@ + super::spec::write_new_session_ticket(n@));
    }
}

/// §4.4.2: append a Certificate body ([`super::spec::write_certificate`]).
pub fn write_certificate(out: &mut Vec<u8>, c: &Certificate<'_>)
    requires
        super::lemmas_hs::certificate_ok(c@),
    ensures
        final(out)@ =~= old(out)@ + super::spec::write_certificate(c@),
{
    push_vec(out, c.context, 255);
    let mut list: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    let ghost entries = super::types::views(c.entries@);
    proof {
        assert(entries.take(0) =~= Seq::<super::spec::CertificateEntry>::empty());
    }
    while i < c.entries.len()
        invariant
            i <= c.entries@.len(),
            entries == super::types::views(c.entries@),
            super::lemmas_hs::certificate_ok(c@),
            list@ =~= super::spec::write_list(
                entries.take(i as int),
                |e: super::spec::CertificateEntry| super::spec::write_certificate_entry(e),
            ),
        decreases c.entries@.len() - i,
    {
        let e = match c.entries.get(i) {
            Some(e) => e,
            None => {
                proof {
                    assert(false);
                }
                return ;
            },
        };
        proof {
            let w = |x: super::spec::CertificateEntry| super::spec::write_certificate_entry(x);
            assert(entries[i as int] == c.entries@[i as int]@);
            assert(super::lemmas_hs::entry_ok(entries[i as int]));
            super::lemmas_pl::lemma_write_list_push(entries.take(i as int), entries[i as int], w);
            assert(entries.take(i as int + 1) =~= entries.take(i as int).push(entries[i as int]));
            assert forall|k: int| 0 <= k < e.extensions@.len() implies (#[trigger] e.extensions@[k]).data@.len() <= 65535 by {
                assert(super::types::views(e.extensions@)[k] == e.extensions@[k]@);
            }
            assert(super::spec::write_list(
                super::types::views(e.extensions@),
                |x: super::spec::Ext| super::spec::write_ext(x),
            ).len() <= 65535);
        }
        let ghost before = list@;
        push_vec(&mut list, e.cert_data, 16777215);
        push_extension_block(&mut list, e.extensions.as_slice(), 65535);
        proof {
            let w = |x: super::spec::CertificateEntry| super::spec::write_certificate_entry(x);
            assert(list@ =~= before + super::spec::write_certificate_entry(entries[i as int]));
        }
        // i < len, so this does not saturate.
        i = i.saturating_add(1);
    }
    proof {
        assert(entries.take(entries.len() as int) =~= entries);
        assert(list@.len() <= 16777215);
    }
    push_vec(out, list.as_slice(), 16777215);
    proof {
        assert(out@ =~= old(out)@ + super::spec::write_certificate(c@));
    }
}

/// The alert §6.2 names for each kind of error, as a fatal alert
/// ([`super::spec::alert_for`]).
pub fn alert_for(k: ErrKind) -> (a: Alert)
    ensures
        a == super::spec::alert_for(k),
{
    let description = match k {
        ErrKind::Decode => super::spec::DECODE_ERROR,
        ErrKind::RecordOverflow => super::spec::RECORD_OVERFLOW,
        ErrKind::UnexpectedContentType => super::spec::UNEXPECTED_MESSAGE,
        ErrKind::UnexpectedHandshakeType => super::spec::UNEXPECTED_MESSAGE,
        ErrKind::ZeroLengthFragment => super::spec::UNEXPECTED_MESSAGE,
        ErrKind::Interleaved => super::spec::UNEXPECTED_MESSAGE,
        ErrKind::AllZeroInnerPlaintext => super::spec::UNEXPECTED_MESSAGE,
        ErrKind::BadChangeCipherSpec => super::spec::UNEXPECTED_MESSAGE,
        ErrKind::BadLegacyRecordVersion => super::spec::DECODE_ERROR,
        ErrKind::HandshakeTooLarge => super::spec::ILLEGAL_PARAMETER,
        ErrKind::DuplicateExtension => super::spec::ILLEGAL_PARAMETER,
        ErrKind::ExtensionNotAllowed => super::spec::ILLEGAL_PARAMETER,
        ErrKind::InvalidEnum => super::spec::ILLEGAL_PARAMETER,
        ErrKind::NonEmptyContext => super::spec::ILLEGAL_PARAMETER,
        ErrKind::MissingExtension => super::spec::MISSING_EXTENSION,
        ErrKind::BadRecordMac => super::spec::BAD_RECORD_MAC,
    };
    Alert { level: super::spec::LEVEL_FATAL, description }
}

} // verus!
