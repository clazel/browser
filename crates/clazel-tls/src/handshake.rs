//! The executable handshake messages (RFC 8446 §4), proven to meet
//! [`super::spec`]: reading every message the client receives (and
//! ClientHello, so that the client's own can be read back), checking the
//! rules of §4.1 to §4.6 that read their fields, and writing the messages
//! the client sends.

use super::extension::{check_extensions, read_exts, read_u16s};
use super::reader::{Cur, byte_at};
use super::spec::{
    ErrKind, HANDSHAKE_HEADER, HS_CERTIFICATE, HS_CERTIFICATE_REQUEST, HS_CERTIFICATE_VERIFY,
    HS_CLIENT_HELLO, HS_ENCRYPTED_EXTENSIONS, HS_END_OF_EARLY_DATA, HS_FINISHED,
    HS_NEW_SESSION_TICKET, HS_SERVER_HELLO, MsgKind, UPDATE_NOT_REQUESTED, UPDATE_REQUESTED,
};
use super::types::{
    Certificate, CertificateEntry, CertificateRequest, CertificateVerify, ClientHello, Extension,
    HsMsg, NewSessionTicket, ServerHello,
};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §4.1: ClientHello, ServerHello.
// ---------------------------------------------------------------------------

/// §4.1.2: read a ClientHello's body ([`super::spec::read_client_hello`]).
pub fn read_client_hello<'a>(body: &'a [u8]) -> (r: Option<ClientHello<'a>>)
    ensures
        match r {
            Some(m) => super::spec::read_client_hello(body@) == Some(m@),
            None => super::spec::read_client_hello(body@) is None,
        },
{
    let mut c = Cur::new(body);
    let ver = c.u16()?;
    let random = c.fixed(32)?;
    let sid = c.vec(0, 32)?;
    let mut cs = c.vec(2, 65534)?;
    let suites = read_u16s(&mut cs)?;
    let comp = c.vec(1, 255)?;
    let exts = read_exts(&mut c, 8, 65535)?;
    if !c.is_empty() {
        return None;
    }
    Some(
        ClientHello {
            legacy_version: ver,
            random,
            session_id: sid.as_slice(),
            cipher_suites: suites,
            compression: comp.as_slice(),
            extensions: exts,
        },
    )
}

/// §4.1.3: read a ServerHello's body ([`super::spec::read_server_hello`]).
pub fn read_server_hello<'a>(body: &'a [u8]) -> (r: Option<ServerHello<'a>>)
    ensures
        match r {
            Some(m) => super::spec::read_server_hello(body@) == Some(m@),
            None => super::spec::read_server_hello(body@) is None,
        },
{
    let mut c = Cur::new(body);
    let ver = c.u16()?;
    let random = c.fixed(32)?;
    let sid = c.vec(0, 32)?;
    let suite = c.u16()?;
    let comp = c.u8()?;
    let exts = read_exts(&mut c, 0, 65535)?;
    if !c.is_empty() {
        return None;
    }
    Some(
        ServerHello {
            legacy_version: ver,
            random,
            session_id_echo: sid.as_slice(),
            cipher_suite: suite,
            compression: comp,
            extensions: exts,
        },
    )
}

/// RFC 5246 §7.4.1.3 legacy form and RFC 8446 §4.1.3 negotiation: recognize
/// complete ServerHello bodies with no `supported_versions` extension before
/// applying the TLS 1.3 parser. Invalid or truncated framing returns false,
/// so the normal parser reports `decode_error` for those inputs.
pub fn legacy_server_hello_without_supported_versions(body: &[u8]) -> (out: bool)
    ensures out == super::spec::legacy_server_hello_without_supported_versions(body@),
{
    let mut c = Cur::new(body);
    if c.u16().is_none() { return false; }
    if c.fixed(32).is_none() { return false; }
    if c.vec(0, 32).is_none() { return false; }
    if c.u16().is_none() { return false; }
    if c.u8().is_none() { return false; }
    if c.is_empty() { return true; }
    let extensions = match read_exts(&mut c, 0, 65535) {
        Some(extensions) => extensions,
        None => return false,
    };
    if !c.is_empty() { return false; }
    !super::extension::has_ext(extensions.as_slice(), 43)
}

/// Whether two byte strings are equal.
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a@.len() - i,
    {
        if byte_at(a, i) != byte_at(b, i) {
            return false;
        }
        // i < len, so this does not saturate.
        i = i.saturating_add(1);
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// §4.1.3: the `Random` value that marks a HelloRetryRequest
/// ([`super::spec::hrr_random`]).
pub fn hrr_random() -> (v: Vec<u8>)
    ensures
        v@ == super::spec::hrr_random(),
{
    let v: Vec<u8> = vec![
        0xCF, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11, 0xBE, 0x1D, 0x8C, 0x02, 0x1E, 0x65, 0xB8, 0x91, 0xC2, 0xA2,
        0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E, 0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C,
    ];
    proof {
        assert(v@ =~= super::spec::hrr_random());
    }
    v
}

/// §4.1.3: "Upon receiving a message with type server_hello,
/// implementations MUST first examine the Random value and, if it matches
/// this value, process it as described in Section 4.1.4"
/// ([`super::spec::is_hello_retry_request`]).
pub fn is_hello_retry_request(sh: &ServerHello<'_>) -> (b: bool)
    ensures
        b == super::spec::is_hello_retry_request(sh@),
{
    let marker = hrr_random();
    bytes_eq(sh.random, marker.as_slice())
}

// ---------------------------------------------------------------------------
// §4.3 and §4.4.
// ---------------------------------------------------------------------------

/// §4.3.1: read an EncryptedExtensions body
/// ([`super::spec::read_encrypted_extensions`]).
pub fn read_encrypted_extensions<'a>(body: &'a [u8]) -> (r: Option<Vec<Extension<'a>>>)
    ensures
        match r {
            Some(es) => super::spec::read_encrypted_extensions(body@) == Some(super::types::views(es@)),
            None => super::spec::read_encrypted_extensions(body@) is None,
        },
{
    let mut c = Cur::new(body);
    let es = read_exts(&mut c, 0, 65535)?;
    if !c.is_empty() {
        return None;
    }
    Some(es)
}

/// §4.3.2: read a CertificateRequest body
/// ([`super::spec::read_certificate_request`]).
pub fn read_certificate_request<'a>(body: &'a [u8]) -> (r: Option<CertificateRequest<'a>>)
    ensures
        match r {
            Some(m) => super::spec::read_certificate_request(body@) == Some(m@),
            None => super::spec::read_certificate_request(body@) is None,
        },
{
    let mut c = Cur::new(body);
    let ctx = c.vec(0, 255)?;
    let es = read_exts(&mut c, 2, 65535)?;
    if !c.is_empty() {
        return None;
    }
    Some(CertificateRequest { context: ctx.as_slice(), extensions: es })
}

/// §4.4.2: read one `CertificateEntry`
/// ([`super::spec::read_certificate_entry`]).
pub fn read_certificate_entry<'a>(c: &mut Cur<'a>) -> (r: Option<CertificateEntry<'a>>)
    ensures
        match r {
            Some(e) => super::spec::read_certificate_entry(old(c)@) == Some((e@, final(c)@)),
            None => super::spec::read_certificate_entry(old(c)@) is None,
        },
{
    let cert = c.vec(1, 16777215)?;
    let es = read_exts(c, 0, 65535)?;
    Some(CertificateEntry { cert_data: cert.as_slice(), extensions: es })
}

/// The Certificate that a list of entries read so far makes with its
/// context, if the list is read.
pub open spec fn cert_after(ctx: Seq<u8>, entries: Option<Seq<super::spec::CertificateEntry>>) -> Option<
    super::spec::Certificate,
> {
    match entries {
        None => None,
        Some(es) => Some(super::spec::Certificate { context: ctx, entries: es }),
    }
}

/// §4.4.2: read a Certificate body ([`super::spec::read_certificate`]).
pub fn read_certificate<'a>(body: &'a [u8]) -> (r: Option<Certificate<'a>>)
    ensures
        match r {
            Some(m) => super::spec::read_certificate(body@) == Some(m@),
            None => super::spec::read_certificate(body@) is None,
        },
{
    let mut c = Cur::new(body);
    let ctx = c.vec(0, 255)?;
    let mut list = c.vec(0, 16777215)?;
    if !c.is_empty() {
        return None;
    }
    let ghost content = list@;
    let mut acc: Vec<CertificateEntry<'a>> = Vec::new();
    proof {
        assert(super::types::views(acc@) =~= Seq::<super::spec::CertificateEntry>::empty());
        let f = |x: Seq<u8>| super::spec::read_certificate_entry(x);
        match super::spec::read_list(content, f) {
            None => {},
            Some(es) => {
                assert(Seq::<super::spec::CertificateEntry>::empty() + es =~= es);
            },
        }
    }
    while !list.is_empty()
        invariant
            super::spec::read_certificate(body@) == cert_after(
                ctx@,
                super::lemmas_pl::list_after(super::types::views(acc@), list@, |x: Seq<u8>| super::spec::read_certificate_entry(x)),
            ),
        decreases list@.len(),
    {
        let ghost before = list@;
        proof {
            super::lemmas_pl::lemma_list_after_step(
                super::types::views(acc@),
                before,
                |x: Seq<u8>| super::spec::read_certificate_entry(x),
            );
            super::lemmas_hs::lemma_read_certificate_entry_canonical(before);
        }
        let e = read_certificate_entry(&mut list)?;
        proof {
            super::types::lemma_views_push(acc@, e);
        }
        acc.push(e);
    }
    proof {
        super::lemmas_pl::lemma_list_after_empty(super::types::views(acc@), |x: Seq<u8>| super::spec::read_certificate_entry(x));
        assert(list@ =~= Seq::<u8>::empty());
    }
    Some(Certificate { context: ctx.as_slice(), entries: acc })
}

/// §4.4.3: read a CertificateVerify body
/// ([`super::spec::read_certificate_verify`]).
pub fn read_certificate_verify<'a>(body: &'a [u8]) -> (r: Option<CertificateVerify<'a>>)
    ensures
        match r {
            Some(m) => super::spec::read_certificate_verify(body@) == Some(m@),
            None => super::spec::read_certificate_verify(body@) is None,
        },
{
    let mut c = Cur::new(body);
    let alg = c.u16()?;
    let sig = c.vec(0, 65535)?;
    if !c.is_empty() {
        return None;
    }
    Some(CertificateVerify { algorithm: alg, signature: sig.as_slice() })
}

/// §4.4.4: read a Finished body for a hash of `hash_len` bytes
/// ([`super::spec::read_finished`]).
pub fn read_finished(body: &[u8], hash_len: usize) -> (r: Option<&[u8]>)
    ensures
        match r {
            Some(v) => super::spec::read_finished(body@, hash_len as nat) == Some(v@),
            None => super::spec::read_finished(body@, hash_len as nat) is None,
        },
{
    if body.len() == hash_len {
        Some(body)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// §4.6.
// ---------------------------------------------------------------------------

/// §4.6.1: read a NewSessionTicket body
/// ([`super::spec::read_new_session_ticket`]).
pub fn read_new_session_ticket<'a>(body: &'a [u8]) -> (r: Option<NewSessionTicket<'a>>)
    ensures
        match r {
            Some(m) => super::spec::read_new_session_ticket(body@) == Some(m@),
            None => super::spec::read_new_session_ticket(body@) is None,
        },
{
    let mut c = Cur::new(body);
    let life = c.u32()?;
    let add = c.u32()?;
    let nonce = c.vec(0, 255)?;
    let ticket = c.vec(1, 65535)?;
    let es = read_exts(&mut c, 0, 65534)?;
    if !c.is_empty() {
        return None;
    }
    Some(
        NewSessionTicket {
            ticket_lifetime: life,
            ticket_age_add: add,
            ticket_nonce: nonce.as_slice(),
            ticket: ticket.as_slice(),
            extensions: es,
        },
    )
}

/// §4.6.3: read a KeyUpdate body ([`super::spec::read_key_update`]).
pub fn read_key_update(body: &[u8]) -> (r: Option<u8>)
    ensures
        r == super::spec::read_key_update(body@),
{
    if body.len() == 1 {
        Some(byte_at(body, 0))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// §4: the Handshake header and the rules that need a message's meaning.
// ---------------------------------------------------------------------------

/// Appendix B.3: whether `t` is a `HandshakeType` that `Handshake`'s
/// `select` has a case for ([`super::spec::handshake_type_known`]).
pub fn handshake_type_known(t: u8) -> (b: bool)
    ensures
        b == super::spec::handshake_type_known(t),
{
    t == 1 || t == 2 || t == 4 || t == 5 || t == 8 || t == 11 || t == 13 || t == 15 || t == 20 || t == 24
}

/// §4.4.2 on the extensions of each entry of a Certificate
/// ([`super::spec::certificate_entries_error`]).
fn certificate_entries_error(es: &[CertificateEntry<'_>]) -> (r: Option<ErrKind>)
    ensures
        r == super::spec::certificate_entries_error(super::types::views(es@)),
{
    let mut i: usize = 0;
    proof {
        assert(super::types::views(es@).skip(0) =~= super::types::views(es@));
    }
    while i < es.len()
        invariant
            i <= es@.len(),
            super::spec::certificate_entries_error(super::types::views(es@)) == super::spec::certificate_entries_error(
                super::types::views(es@).skip(i as int),
            ),
        decreases es@.len() - i,
    {
        let k = match es.get(i) {
            Some(e) => check_extensions(e.extensions.as_slice(), MsgKind::Ct),
            None => None,
        };
        proof {
            assert(super::types::views(es@).skip(i as int)[0] == es@[i as int]@);
            assert(super::types::views(es@).skip(i as int).skip(1) =~= super::types::views(es@).skip(i as int + 1));
        }
        if let Some(kind) = k {
            return Some(kind);
        }
        // i < len, so this does not saturate.
        i = i.saturating_add(1);
    }
    proof {
        assert(super::types::views(es@).skip(es@.len() as int) =~= Seq::<super::spec::CertificateEntry>::empty());
    }
    None
}

/// §4.1.2 and §4.2: a ClientHello body, read and checked.
fn parse_client_hello<'a>(body: &'a [u8], _hash_len: usize) -> (r: Result<HsMsg<'a>, ErrKind>)
    ensures
        super::types::res_view(r) == super::spec::parse_handshake_body(HS_CLIENT_HELLO, body@, _hash_len as nat),
{
    let ch = match read_client_hello(body) {
        None => return Err(ErrKind::Decode),
        Some(ch) => ch,
    };
    if !(ch.compression.len() == 1 && byte_at(ch.compression, 0) == 0) {
        proof {
            assert(ch.compression@ != seq![0u8]);
        }
        return Err(ErrKind::InvalidEnum);
    }
    proof {
        assert(ch.compression@ =~= seq![0u8]);
    }
    match check_extensions(ch.extensions.as_slice(), MsgKind::Ch) {
        Some(k) => Err(k),
        None => Ok(HsMsg::ClientHello(ch)),
    }
}

/// §4.1.3, §4.1.4 and §4.2: a ServerHello (or HelloRetryRequest) body,
/// read and checked.
fn parse_server_hello<'a>(body: &'a [u8], _hash_len: usize) -> (r: Result<HsMsg<'a>, ErrKind>)
    ensures
        super::types::res_view(r) == super::spec::parse_handshake_body(HS_SERVER_HELLO, body@, _hash_len as nat),
{
    let sh = match read_server_hello(body) {
        None => return Err(ErrKind::Decode),
        Some(sh) => sh,
    };
    if sh.compression != 0 {
        return Err(ErrKind::InvalidEnum);
    }
    let kind = if is_hello_retry_request(&sh) {
        MsgKind::Hrr
    } else {
        MsgKind::Sh
    };
    match check_extensions(sh.extensions.as_slice(), kind) {
        Some(k) => Err(k),
        None => Ok(HsMsg::ServerHello(sh)),
    }
}

/// §4.6.1 and §4.2: a NewSessionTicket body, read and checked.
fn parse_new_session_ticket<'a>(body: &'a [u8], _hash_len: usize) -> (r: Result<HsMsg<'a>, ErrKind>)
    ensures
        super::types::res_view(r) == super::spec::parse_handshake_body(HS_NEW_SESSION_TICKET, body@, _hash_len as nat),
{
    let n = match read_new_session_ticket(body) {
        None => return Err(ErrKind::Decode),
        Some(n) => n,
    };
    match check_extensions(n.extensions.as_slice(), MsgKind::Nst) {
        Some(k) => Err(k),
        None => Ok(HsMsg::NewSessionTicket(n)),
    }
}

/// §4.3.1 and §4.2: an EncryptedExtensions body, read and checked.
fn parse_encrypted_extensions<'a>(body: &'a [u8], _hash_len: usize) -> (r: Result<HsMsg<'a>, ErrKind>)
    ensures
        super::types::res_view(r) == super::spec::parse_handshake_body(HS_ENCRYPTED_EXTENSIONS, body@, _hash_len as nat),
{
    let es = match read_encrypted_extensions(body) {
        None => return Err(ErrKind::Decode),
        Some(es) => es,
    };
    match check_extensions(es.as_slice(), MsgKind::Ee) {
        Some(k) => Err(k),
        None => Ok(HsMsg::EncryptedExtensions(es)),
    }
}

/// §4.4.2 and §4.2: a Certificate body, read and checked.
fn parse_certificate<'a>(body: &'a [u8], _hash_len: usize) -> (r: Result<HsMsg<'a>, ErrKind>)
    ensures
        super::types::res_view(r) == super::spec::parse_handshake_body(HS_CERTIFICATE, body@, _hash_len as nat),
{
    let c = match read_certificate(body) {
        None => return Err(ErrKind::Decode),
        Some(c) => c,
    };
    match certificate_entries_error(c.entries.as_slice()) {
        Some(k) => Err(k),
        None => Ok(HsMsg::Certificate(c)),
    }
}

/// §4.3.2 and §4.2: a CertificateRequest body, read and checked.
fn parse_certificate_request<'a>(body: &'a [u8], _hash_len: usize) -> (r: Result<HsMsg<'a>, ErrKind>)
    ensures
        super::types::res_view(r) == super::spec::parse_handshake_body(HS_CERTIFICATE_REQUEST, body@, _hash_len as nat),
{
    let c = match read_certificate_request(body) {
        None => return Err(ErrKind::Decode),
        Some(c) => c,
    };
    match check_extensions(c.extensions.as_slice(), MsgKind::Cr) {
        Some(k) => Err(k),
        None => Ok(HsMsg::CertificateRequest(c)),
    }
}

/// §4.6.3: a KeyUpdate body, read and checked.
fn parse_key_update<'a>(body: &'a [u8], _hash_len: usize) -> (r: Result<HsMsg<'a>, ErrKind>)
    ensures
        super::types::res_view(r) == super::spec::parse_handshake_body(super::spec::HS_KEY_UPDATE, body@, _hash_len as nat),
{
    match read_key_update(body) {
        None => Err(ErrKind::Decode),
        Some(r) => {
            if r == UPDATE_NOT_REQUESTED || r == UPDATE_REQUESTED {
                Ok(HsMsg::KeyUpdate(r))
            } else {
                Err(ErrKind::InvalidEnum)
            }
        },
    }
}

/// §4: read and check the message of type `t` with body `body`
/// ([`super::spec::parse_handshake_body`]).
pub fn parse_handshake_body<'a>(t: u8, body: &'a [u8], hash_len: usize) -> (r: Result<HsMsg<'a>, ErrKind>)
    ensures
        super::types::res_view(r) == super::spec::parse_handshake_body(t, body@, hash_len as nat),
{
    if !handshake_type_known(t) {
        return Err(ErrKind::UnexpectedHandshakeType);
    }
    if t == HS_CLIENT_HELLO {
        parse_client_hello(body, hash_len)
    } else if t == HS_SERVER_HELLO {
        parse_server_hello(body, hash_len)
    } else if t == HS_NEW_SESSION_TICKET {
        parse_new_session_ticket(body, hash_len)
    } else if t == HS_END_OF_EARLY_DATA {
        if body.is_empty() {
            Ok(HsMsg::EndOfEarlyData)
        } else {
            Err(ErrKind::Decode)
        }
    } else if t == HS_ENCRYPTED_EXTENSIONS {
        parse_encrypted_extensions(body, hash_len)
    } else if t == HS_CERTIFICATE {
        parse_certificate(body, hash_len)
    } else if t == HS_CERTIFICATE_REQUEST {
        parse_certificate_request(body, hash_len)
    } else if t == HS_CERTIFICATE_VERIFY {
        match read_certificate_verify(body) {
            None => Err(ErrKind::Decode),
            Some(c) => Ok(HsMsg::CertificateVerify(c)),
        }
    } else if t == HS_FINISHED {
        match read_finished(body, hash_len) {
            None => Err(ErrKind::Decode),
            Some(v) => Ok(HsMsg::Finished(v)),
        }
    } else {
        parse_key_update(body, hash_len)
    }
}

/// §4: read and check one whole handshake message, as the reassembler
/// emits it ([`super::spec::parse_handshake`]).
pub fn parse_handshake<'a>(msg: &'a [u8], hash_len: usize) -> (r: Result<HsMsg<'a>, ErrKind>)
    ensures
        super::contract::parse_handshake_ensures(msg@, hash_len as nat, super::types::res_view(r)),
{
    if msg.len() < HANDSHAKE_HEADER {
        return Err(ErrKind::Decode);
    }
    let t = byte_at(msg, 0);
    let b1 = byte_at(msg, 1);
    let b2 = byte_at(msg, 2);
    let b3 = byte_at(msg, 3);
    proof {
        super::lemmas_pl::lemma_be_value_3(msg@.subrange(1, 4));
    }
    // b1 * 65536 + b2 * 256 + b3 < 2^24: no saturation.
    let len: usize = (b1 as usize).saturating_mul(65536).saturating_add((b2 as usize).saturating_mul(256)).saturating_add(
        b3 as usize,
    );
    if !handshake_type_known(t) {
        return Err(ErrKind::UnexpectedHandshakeType);
    }
    // len < 2^24, so this does not saturate.
    if msg.len() != HANDSHAKE_HEADER.saturating_add(len) {
        return Err(ErrKind::Decode);
    }
    let body = vstd::slice::slice_subrange(msg, HANDSHAKE_HEADER, msg.len());
    proof {
        assert(body@ =~= msg@.skip(4));
    }
    parse_handshake_body(t, body, hash_len)
}

} // verus!
