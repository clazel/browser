//! Facts proven about the handshake messages of [`super::spec`] (RFC 8446
//! §4): every message the client sends (ClientHello, Finished, KeyUpdate,
//! and the empty Certificate that refuses a CertificateRequest) is read
//! back from its encoding, and what a reader accepts is one encoding, so
//! two different byte strings never give the same message.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One byte spelling `v` is `seq![v]`.
pub proof fn lemma_be_bytes_one(v: u8)
    ensures
        be_bytes(v as nat, 1) =~= seq![v],
{
    assert(be_bytes(v as nat, 0) =~= Seq::<u8>::empty());
    assert(be_bytes(v as nat, 1) =~= be_bytes(v as nat / 256, 0).push((v as nat % 256) as u8));
    assert(v as nat / 256 == 0);
    assert((v as nat % 256) as u8 == v);
}

/// A ServerHello that can be written.
pub open spec fn server_hello_requires(sh: ServerHello) -> bool {
    &&& sh.random.len() == 32
    &&& vec_in_bounds(sh.session_id_echo, 0, 32)
    &&& forall|i: int| 0 <= i < sh.extensions.len() ==> (#[trigger] sh.extensions[i]).data.len() <= 65535
    &&& vec_in_bounds(write_list(sh.extensions, |e: Ext| write_ext(e)), 0, 65535)
}

// ---------------------------------------------------------------------------
// §4.1.2 ClientHello.
// ---------------------------------------------------------------------------

/// A ClientHello the client writes is read back.
pub proof fn lemma_read_client_hello_write(ch: ClientHello)
    requires
        super::contract::client_hello_requires(ch),
    ensures
        read_client_hello(write_client_hello(ch)) == Some(ch),
{
    super::lemmas_pl::lemma_pow256_widths();
    let e = write_exts(ch.extensions, 65535);
    let cm = write_vec(ch.compression, 255) + e;
    let cs = write_vec(write_u16s(ch.cipher_suites), 65534) + cm;
    let sid = write_vec(ch.session_id, 32) + cs;
    let rnd = ch.random + sid;
    super::lemmas_pl::lemma_read_uint_write(ch.legacy_version as nat, 2, rnd);
    super::lemmas_pl::lemma_read_fixed_write(ch.random, sid);
    super::lemmas_pl::lemma_read_vec_write_vec(ch.session_id, 0, 32, cs);
    super::lemmas_pl::lemma_write_u16s_len(ch.cipher_suites);
    super::lemmas_pl::lemma_read_vec_write_vec(write_u16s(ch.cipher_suites), 2, 65534, cm);
    super::lemmas_pl::lemma_read_u16s_write_u16s(ch.cipher_suites);
    super::lemmas_pl::lemma_read_vec_write_vec(ch.compression, 1, 255, e);
    super::lemmas_ext::lemma_read_exts_write_exts(ch.extensions, 8, 65535, seq![]);
    assert(e + Seq::<u8>::empty() =~= e);
}

/// What [`read_client_hello`] accepts is what [`write_client_hello`]
/// writes, and the hello is one that can be written.
pub proof fn lemma_read_client_hello_canonical(b: Seq<u8>)
    ensures
        match read_client_hello(b) {
            Some(ch) => super::contract::client_hello_requires(ch) && write_client_hello(ch) =~= b,
            None => true,
        },
{
    super::lemmas_pl::lemma_pow256_widths();
    if let Some(ch) = read_client_hello(b) {
        let (ver, r1) = read_uint(b, 2)->Some_0;
        super::lemmas_pl::lemma_read_uint_canonical(b, 2);
        let (random, r2) = read_fixed(r1, 32)->Some_0;
        super::lemmas_pl::lemma_read_fixed_canonical(r1, 32);
        let (sid, r3) = read_vec(r2, 0, 32)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(r2, 0, 32);
        let (cs_bytes, r4) = read_vec(r3, 2, 65534)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(r3, 2, 65534);
        let cs = read_u16s(cs_bytes)->Some_0;
        super::lemmas_pl::lemma_write_u16s_read_u16s(cs_bytes);
        let (comp, r5) = read_vec(r4, 1, 255)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(r4, 1, 255);
        let (exts, r6) = read_exts(r5, 8, 65535)->Some_0;
        super::lemmas_ext::lemma_read_exts_canonical(r5, 8, 65535);
        assert(r6.len() == 0);
        assert(r5 =~= write_exts(exts, 65535));
        assert(write_u16(ver as u16) =~= be_bytes(ver, 2));
        assert(b =~= write_client_hello(ch));
    }
}

// ---------------------------------------------------------------------------
// §4.1.3 ServerHello.
// ---------------------------------------------------------------------------

/// A ServerHello is read back from its encoding.
pub proof fn lemma_read_server_hello_write(sh: ServerHello)
    requires
        server_hello_requires(sh),
    ensures
        read_server_hello(write_server_hello(sh)) == Some(sh),
{
    super::lemmas_pl::lemma_pow256_widths();
    let e = write_exts(sh.extensions, 65535);
    let cm = seq![sh.compression] + e;
    let cs = write_u16(sh.cipher_suite) + cm;
    let sid = write_vec(sh.session_id_echo, 32) + cs;
    let rnd = sh.random + sid;
    super::lemmas_pl::lemma_read_uint_write(sh.legacy_version as nat, 2, rnd);
    super::lemmas_pl::lemma_read_fixed_write(sh.random, sid);
    super::lemmas_pl::lemma_read_vec_write_vec(sh.session_id_echo, 0, 32, cs);
    super::lemmas_pl::lemma_read_uint_write(sh.cipher_suite as nat, 2, cm);
    lemma_be_bytes_one(sh.compression);
    super::lemmas_pl::lemma_read_uint_write(sh.compression as nat, 1, e);
    super::lemmas_ext::lemma_read_exts_write_exts(sh.extensions, 0, 65535, seq![]);
    assert(e + Seq::<u8>::empty() =~= e);
}

/// What [`read_server_hello`] accepts is written back byte-for-byte.
pub proof fn lemma_read_server_hello_canonical(b: Seq<u8>)
    ensures
        match read_server_hello(b) {
        Some(sh) => server_hello_requires(sh) && write_server_hello(sh) =~= b,
            None => true,
        },
{
    super::lemmas_pl::lemma_pow256_widths();
    if let Some(sh) = read_server_hello(b) {
        let (ver, r1) = read_uint(b, 2)->Some_0;
        super::lemmas_pl::lemma_read_uint_canonical(b, 2);
        let (random, r2) = read_fixed(r1, 32)->Some_0;
        super::lemmas_pl::lemma_read_fixed_canonical(r1, 32);
        let (sid, r3) = read_vec(r2, 0, 32)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(r2, 0, 32);
        let (cs, r4) = read_uint(r3, 2)->Some_0;
        super::lemmas_pl::lemma_read_uint_canonical(r3, 2);
        let (comp, r5) = read_uint(r4, 1)->Some_0;
        super::lemmas_pl::lemma_read_uint_canonical(r4, 1);
        let (exts, r6) = read_exts(r5, 0, 65535)->Some_0;
        assert(r6.len() == 0);
        super::lemmas_ext::lemma_read_exts_canonical(r5, 0, 65535);
        assert(r5 =~= write_exts(exts, 65535));
        assert(b =~= write_server_hello(sh));
        assert(write_u16(ver as u16) =~= be_bytes(ver, 2));
        assert(write_u16(cs as u16) =~= be_bytes(cs, 2));
        lemma_be_bytes_one(comp as u8);
        assert(b =~= write_server_hello(sh));
    }
}

// ---------------------------------------------------------------------------
// §4.3 and §4.4.
// ---------------------------------------------------------------------------

/// An EncryptedExtensions body is read back.
pub proof fn lemma_read_encrypted_extensions_write(es: Seq<Ext>)
    requires
        forall|i: int| 0 <= i < es.len() ==> super::lemmas_ext::ext_ok(#[trigger] es[i]),
        vec_in_bounds(write_list(es, |e: Ext| write_ext(e)), 0, 65535),
    ensures
        read_encrypted_extensions(write_encrypted_extensions(es)) == Some(es),
{
    super::lemmas_ext::lemma_read_exts_write_exts(es, 0, 65535, seq![]);
    assert(write_exts(es, 65535) + Seq::<u8>::empty() =~= write_exts(es, 65535));
}

/// What [`read_encrypted_extensions`] accepts is one encoding.
pub proof fn lemma_read_encrypted_extensions_canonical(b: Seq<u8>)
    ensures
        match read_encrypted_extensions(b) {
            Some(es) => {
                &&& forall|i: int| 0 <= i < es.len() ==> super::lemmas_ext::ext_ok(#[trigger] es[i])
                &&& vec_in_bounds(write_list(es, |e: Ext| write_ext(e)), 0, 65535)
                &&& write_encrypted_extensions(es) =~= b
            },
            None => true,
        },
{
    if let Some(es) = read_encrypted_extensions(b) {
        super::lemmas_ext::lemma_read_exts_canonical(b, 0, 65535);
    }
}

/// A CertificateVerify body is read back.
pub proof fn lemma_read_certificate_verify_write(c: CertificateVerify)
    requires
        c.signature.len() <= 65535,
    ensures
        read_certificate_verify(write_certificate_verify(c)) == Some(c),
{
    super::lemmas_pl::lemma_pow256_widths();
    let v = write_vec(c.signature, 65535);
    super::lemmas_pl::lemma_read_uint_write(c.algorithm as nat, 2, v);
    super::lemmas_pl::lemma_read_vec_write_vec(c.signature, 0, 65535, seq![]);
    assert(v + Seq::<u8>::empty() =~= v);
}

/// What [`read_certificate_verify`] accepts is one encoding.
pub proof fn lemma_read_certificate_verify_canonical(b: Seq<u8>)
    ensures
        match read_certificate_verify(b) {
            Some(c) => c.signature.len() <= 65535 && write_certificate_verify(c) =~= b,
            None => true,
        },
{
    super::lemmas_pl::lemma_pow256_widths();
    if let Some(c) = read_certificate_verify(b) {
        let (alg, r1) = read_uint(b, 2)->Some_0;
        super::lemmas_pl::lemma_read_uint_canonical(b, 2);
        let (sig, rest) = read_vec(r1, 0, 65535)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(r1, 0, 65535);
        assert(write_u16(alg as u16) =~= be_bytes(alg, 2));
        assert(b =~= write_certificate_verify(c));
    }
}

/// A CertificateRequest body is read back.
pub proof fn lemma_read_certificate_request_write(c: CertificateRequest)
    requires
        vec_in_bounds(c.context, 0, 255),
        forall|i: int| 0 <= i < c.extensions.len() ==> super::lemmas_ext::ext_ok(#[trigger] c.extensions[i]),
        vec_in_bounds(write_list(c.extensions, |e: Ext| write_ext(e)), 2, 65535),
    ensures
        read_certificate_request(write_certificate_request(c)) == Some(c),
{
    super::lemmas_pl::lemma_read_vec_write_vec(c.context, 0, 255, write_exts(c.extensions, 65535));
    super::lemmas_ext::lemma_read_exts_write_exts(c.extensions, 2, 65535, seq![]);
    assert(write_exts(c.extensions, 65535) + Seq::<u8>::empty() =~= write_exts(c.extensions, 65535));
}

/// What [`read_certificate_request`] accepts is one encoding.
pub proof fn lemma_read_certificate_request_canonical(b: Seq<u8>)
    ensures
        match read_certificate_request(b) {
            Some(c) => {
                &&& vec_in_bounds(c.context, 0, 255)
                &&& forall|i: int| 0 <= i < c.extensions.len() ==> super::lemmas_ext::ext_ok(#[trigger] c.extensions[i])
                &&& vec_in_bounds(write_list(c.extensions, |e: Ext| write_ext(e)), 2, 65535)
                &&& write_certificate_request(c) =~= b
            },
            None => true,
        },
{
    if let Some(c) = read_certificate_request(b) {
        let (ctx, r1) = read_vec(b, 0, 255)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(b, 0, 255);
        let (es, rest) = read_exts(r1, 2, 65535)->Some_0;
        super::lemmas_ext::lemma_read_exts_canonical(r1, 2, 65535);
        assert(b =~= write_certificate_request(c));
    }
}

/// A Certificate entry that can be written.
pub open spec fn entry_ok(e: CertificateEntry) -> bool {
    &&& vec_in_bounds(e.cert_data, 1, 16777215)
    &&& forall|i: int| 0 <= i < e.extensions.len() ==> super::lemmas_ext::ext_ok(#[trigger] e.extensions[i])
    &&& vec_in_bounds(write_list(e.extensions, |x: Ext| write_ext(x)), 0, 65535)
}

/// A Certificate entry is read back from its encoding, wherever it sits,
/// and is at least five bytes.
pub proof fn lemma_read_certificate_entry_write(e: CertificateEntry, rest: Seq<u8>)
    requires
        entry_ok(e),
    ensures
        read_certificate_entry(write_certificate_entry(e) + rest) == Some((e, rest)),
        write_certificate_entry(e).len() >= 1,
{
    super::lemmas_pl::lemma_pow256_widths();
    super::lemmas_pl::lemma_len_width_holds(16777215);
    let ex = write_exts(e.extensions, 65535);
    super::lemmas_pl::lemma_read_vec_write_vec(e.cert_data, 1, 16777215, ex + rest);
    super::lemmas_ext::lemma_read_exts_write_exts(e.extensions, 0, 65535, rest);
    assert(write_certificate_entry(e) + rest =~= write_vec(e.cert_data, 16777215) + (ex + rest));
    assert(write_vec(e.cert_data, 16777215).len() >= 3) by {
        super::lemmas_pl::lemma_be_bytes_len(e.cert_data.len(), 3);
    }
}

/// What [`read_certificate_entry`] accepts is one encoding.
pub proof fn lemma_read_certificate_entry_canonical(b: Seq<u8>)
    ensures
        match read_certificate_entry(b) {
            Some((e, rest)) => entry_ok(e) && write_certificate_entry(e) + rest =~= b && rest.len() < b.len(),
            None => true,
        },
{
    super::lemmas_pl::lemma_pow256_widths();
    if let Some((e, rest)) = read_certificate_entry(b) {
        let (cert, r1) = read_vec(b, 1, 16777215)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(b, 1, 16777215);
        super::lemmas_ext::lemma_read_exts_canonical(r1, 0, 65535);
        assert(b =~= write_certificate_entry(e) + rest);
        assert(write_vec(cert, 16777215).len() >= 1) by {
            super::lemmas_pl::lemma_be_bytes_len(cert.len(), 3);
        }
    }
}

/// A Certificate that can be written.
pub open spec fn certificate_ok(c: Certificate) -> bool {
    &&& vec_in_bounds(c.context, 0, 255)
    &&& forall|i: int| 0 <= i < c.entries.len() ==> entry_ok(#[trigger] c.entries[i])
    &&& vec_in_bounds(write_list(c.entries, |e: CertificateEntry| write_certificate_entry(e)), 0, 16777215)
}

/// A Certificate body is read back, in particular the one with no entries
/// that refuses a CertificateRequest.
pub proof fn lemma_read_certificate_write(c: Certificate)
    requires
        certificate_ok(c),
    ensures
        read_certificate(write_certificate(c)) == Some(c),
{
    let w = |e: CertificateEntry| write_certificate_entry(e);
    let f = |x: Seq<u8>| read_certificate_entry(x);
    let ok = |e: CertificateEntry| entry_ok(e);
    assert forall|e: CertificateEntry| #[trigger] ok(e) implies w(e).len() >= 1 by {
        lemma_read_certificate_entry_write(e, seq![]);
    }
    assert forall|e: CertificateEntry, r: Seq<u8>| ok(e) implies #[trigger] f(w(e) + r) == Some((e, r)) by {
        lemma_read_certificate_entry_write(e, r);
    }
    super::lemmas_pl::lemma_read_list_write_list(c.entries, w, f, ok);
    let l = write_vec(write_list(c.entries, w), 16777215);
    super::lemmas_pl::lemma_read_vec_write_vec(c.context, 0, 255, l);
    super::lemmas_pl::lemma_read_vec_write_vec(write_list(c.entries, w), 0, 16777215, seq![]);
    assert(l + Seq::<u8>::empty() =~= l);
}

/// What [`read_certificate`] accepts is one encoding.
pub proof fn lemma_read_certificate_canonical(b: Seq<u8>)
    ensures
        match read_certificate(b) {
            Some(c) => certificate_ok(c) && write_certificate(c) =~= b,
            None => true,
        },
{
    if let Some(c) = read_certificate(b) {
        let (ctx, r1) = read_vec(b, 0, 255)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(b, 0, 255);
        let (list, rest) = read_vec(r1, 0, 16777215)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(r1, 0, 16777215);
        let w = |e: CertificateEntry| write_certificate_entry(e);
        let f = |x: Seq<u8>| read_certificate_entry(x);
        assert forall|bb: Seq<u8>| #[trigger] f(bb) is Some implies w(f(bb)->Some_0.0) + f(bb)->Some_0.1 == bb by {
            lemma_read_certificate_entry_canonical(bb);
        }
        super::lemmas_pl::lemma_write_list_read_list(list, w, f);
        lemma_read_certificate_entries_ok(list);
        assert(b =~= write_certificate(c));
    }
}

/// Every entry [`read_list`] reads from a certificate list is
/// [`entry_ok`].
proof fn lemma_read_certificate_entries_ok(list: Seq<u8>)
    ensures
        match read_list(list, |x: Seq<u8>| read_certificate_entry(x)) {
            Some(es) => forall|i: int| 0 <= i < es.len() ==> entry_ok(#[trigger] es[i]),
            None => true,
        },
    decreases list.len(),
{
    let f = |x: Seq<u8>| read_certificate_entry(x);
    if list.len() > 0 {
        lemma_read_certificate_entry_canonical(list);
        if let Some((e, rest)) = read_certificate_entry(list) {
            if rest.len() < list.len() {
                lemma_read_certificate_entries_ok(rest);
                if let Some(es) = read_list(rest, f) {
                    let all = seq![e] + es;
                    assert forall|i: int| 0 <= i < all.len() implies entry_ok(#[trigger] all[i]) by {
                        if i > 0 {
                            assert(all[i] == es[i - 1]);
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §4.6.
// ---------------------------------------------------------------------------

/// A NewSessionTicket that can be written.
pub open spec fn new_session_ticket_ok(n: NewSessionTicket) -> bool {
    &&& vec_in_bounds(n.ticket_nonce, 0, 255)
    &&& vec_in_bounds(n.ticket, 1, 65535)
    &&& forall|i: int| 0 <= i < n.extensions.len() ==> super::lemmas_ext::ext_ok(#[trigger] n.extensions[i])
    &&& vec_in_bounds(write_list(n.extensions, |e: Ext| write_ext(e)), 0, 65534)
}

/// A NewSessionTicket body is read back.
pub proof fn lemma_read_new_session_ticket_write(n: NewSessionTicket)
    requires
        new_session_ticket_ok(n),
    ensures
        read_new_session_ticket(write_new_session_ticket(n)) == Some(n),
{
    super::lemmas_pl::lemma_pow256_widths();
    let ex = write_exts(n.extensions, 65534);
    let t = write_vec(n.ticket, 65535) + ex;
    let nn = write_vec(n.ticket_nonce, 255) + t;
    let ad = be_bytes(n.ticket_age_add as nat, 4) + nn;
    super::lemmas_pl::lemma_read_uint_write(n.ticket_lifetime as nat, 4, ad);
    super::lemmas_pl::lemma_read_uint_write(n.ticket_age_add as nat, 4, nn);
    super::lemmas_pl::lemma_read_vec_write_vec(n.ticket_nonce, 0, 255, t);
    super::lemmas_pl::lemma_read_vec_write_vec(n.ticket, 1, 65535, ex);
    super::lemmas_ext::lemma_read_exts_write_exts(n.extensions, 0, 65534, seq![]);
    assert(ex + Seq::<u8>::empty() =~= ex);
}

/// What [`read_new_session_ticket`] accepts is one encoding.
pub proof fn lemma_read_new_session_ticket_canonical(b: Seq<u8>)
    ensures
        match read_new_session_ticket(b) {
            Some(n) => new_session_ticket_ok(n) && write_new_session_ticket(n) =~= b,
            None => true,
        },
{
    super::lemmas_pl::lemma_pow256_widths();
    if let Some(n) = read_new_session_ticket(b) {
        let (life, r1) = read_uint(b, 4)->Some_0;
        super::lemmas_pl::lemma_read_uint_canonical(b, 4);
        let (add, r2) = read_uint(r1, 4)->Some_0;
        super::lemmas_pl::lemma_read_uint_canonical(r1, 4);
        let (nonce, r3) = read_vec(r2, 0, 255)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(r2, 0, 255);
        let (ticket, r4) = read_vec(r3, 1, 65535)->Some_0;
        super::lemmas_pl::lemma_read_vec_canonical(r3, 1, 65535);
        let (es, rest) = read_exts(r4, 0, 65534)->Some_0;
        super::lemmas_ext::lemma_read_exts_canonical(r4, 0, 65534);
        assert(rest.len() == 0);
        assert(be_bytes(life, 4) =~= be_bytes(n.ticket_lifetime as nat, 4)) by {
            assert(life < 4294967296) by {
                super::lemmas_pl::lemma_read_uint_canonical(b, 4);
            }
        }
        assert(be_bytes(add, 4) =~= be_bytes(n.ticket_age_add as nat, 4)) by {
            assert(add < 4294967296);
        }
        assert(r4 =~= write_exts(es, 65534));
        assert(b =~= write_new_session_ticket(n));
    }
}

// ---------------------------------------------------------------------------
// §4: the Handshake header and the messages the client sends.
// ---------------------------------------------------------------------------

/// The header of a handshake message is its type and the length of its
/// body in three bytes; a body of at most 2^24 - 1 bytes is read back.
pub proof fn lemma_read_handshake_header_write(t: u8, body: Seq<u8>, rest: Seq<u8>)
    requires
        body.len() < 16777216,
    ensures
        read_handshake_header(write_handshake(t, body) + rest) == Some((t, body.len())),
        write_handshake(t, body).len() == HANDSHAKE_HEADER + body.len(),
{
    super::lemmas_pl::lemma_pow256_widths();
    super::lemmas_pl::lemma_be_bytes_len(body.len(), 3);
    let b = write_handshake(t, body) + rest;
    assert(b[0] == t);
    assert(b.subrange(1, 4) =~= be_bytes(body.len(), 3));
    super::lemmas_pl::lemma_be_value_of_be_bytes(body.len(), 3);
}

/// A handshake message the client writes with a body within the limit is
/// a whole message ([`super::lemmas_record::is_message`]), so the
/// reassembler emits it as soon as it has arrived.
pub proof fn lemma_write_handshake_is_message(t: u8, body: Seq<u8>)
    requires
        body.len() <= MAX_HANDSHAKE_BODY,
    ensures
        super::lemmas_record::is_message(write_handshake(t, body)),
{
    super::lemmas_pl::lemma_pow256_widths();
    super::lemmas_pl::lemma_be_bytes_len(body.len(), 3);
    let m = write_handshake(t, body);
    assert(m.subrange(1, 4) =~= be_bytes(body.len(), 3));
    super::lemmas_pl::lemma_be_value_of_be_bytes(body.len(), 3);
}

/// A handshake message is read back from the header and the body: the
/// message `parse_handshake` reads from `write_handshake(t, body)` is the
/// one [`parse_handshake_body`] reads from `body`.
pub proof fn lemma_parse_handshake_write(t: u8, body: Seq<u8>, hash_len: nat)
    requires
        body.len() < 16777216,
    ensures
        parse_handshake(write_handshake(t, body), hash_len) == parse_handshake_body(t, body, hash_len),
{
    lemma_read_handshake_header_write(t, body, seq![]);
    let m = write_handshake(t, body);
    assert(m + Seq::<u8>::empty() =~= m);
    assert(m.skip(4) =~= body);
}

/// The client's Finished is read back: `verify_data` of the hash's length.
pub proof fn lemma_client_finished_round_trip(verify_data: Seq<u8>)
    requires
        verify_data.len() < 16777216,
    ensures
        parse_handshake(write_handshake(HS_FINISHED, verify_data), verify_data.len()) == Res::<HsMsg>::Ok(
            HsMsg::Finished(verify_data),
        ),
{
    lemma_parse_handshake_write(HS_FINISHED, verify_data, verify_data.len());
}

/// The client's KeyUpdate is read back, for both defined requests.
pub proof fn lemma_client_key_update_round_trip(request_update: u8)
    requires
        request_update == UPDATE_NOT_REQUESTED || request_update == UPDATE_REQUESTED,
    ensures
        parse_handshake(write_handshake(HS_KEY_UPDATE, write_key_update(request_update)), 32) == Res::<HsMsg>::Ok(
            HsMsg::KeyUpdate(request_update),
        ),
{
    lemma_parse_handshake_write(HS_KEY_UPDATE, write_key_update(request_update), 32);
}

/// The client's ClientHello is read back as a ClientHello, if it is one
/// the client may send: it fits the encoding, has the single null
/// compression method, and obeys the rules of §4.2 for the extensions of a
/// ClientHello.
pub proof fn lemma_client_hello_round_trip(ch: ClientHello, hash_len: nat)
    requires
        super::contract::client_hello_requires(ch),
        ch.compression == seq![0u8],
        check_extensions(ch.extensions, MsgKind::Ch) is None,
    ensures
        parse_handshake(write_handshake(HS_CLIENT_HELLO, write_client_hello(ch)), hash_len) == Res::<HsMsg>::Ok(
            HsMsg::ClientHello(ch),
        ),
{
    super::lemmas_pl::lemma_pow256_widths();
    lemma_read_client_hello_write(ch);
    // The body is at most 2 + 32 + 33 + 65536 + 256 + 65538 bytes.
    lemma_client_hello_len(ch);
    lemma_parse_handshake_write(HS_CLIENT_HELLO, write_client_hello(ch), hash_len);
}

/// The size of a ClientHello body: its fields' sizes add up.
pub proof fn lemma_client_hello_len(ch: ClientHello)
    requires
        super::contract::client_hello_requires(ch),
    ensures
        write_client_hello(ch).len() == 2 + 32 + (1 + ch.session_id.len()) + (2 + 2 * ch.cipher_suites.len()) + (1
            + ch.compression.len()) + (2 + write_list(ch.extensions, |e: Ext| write_ext(e)).len()),
        write_client_hello(ch).len() < 16777216,
{
    super::lemmas_pl::lemma_pow256_widths();
    super::lemmas_pl::lemma_be_bytes_len(ch.legacy_version as nat, 2);
    super::lemmas_pl::lemma_be_bytes_len(ch.session_id.len(), 1);
    super::lemmas_pl::lemma_be_bytes_len(ch.cipher_suites.len() * 2, 2);
    super::lemmas_pl::lemma_be_bytes_len(ch.compression.len(), 1);
    super::lemmas_pl::lemma_be_bytes_len(write_list(ch.extensions, |e: Ext| write_ext(e)).len(), 2);
    super::lemmas_pl::lemma_write_u16s_len(ch.cipher_suites);
}

/// The empty Certificate message that refuses a CertificateRequest is read
/// back, with the request's context ("the client MUST send a Certificate
/// message containing no certificates", §4.4.2). The generic structure
/// reader preserves the context; the initial-server-authentication layer
/// separately requires it to be empty, while a client response echoes it.
pub proof fn lemma_empty_certificate_round_trip(context: Seq<u8>)
    requires
        vec_in_bounds(context, 0, 255),
    ensures
        read_certificate(write_certificate(Certificate { context, entries: seq![] })) == Some(
            Certificate { context, entries: seq![] },
        ),
{
    let c = Certificate { context, entries: seq![] };
    assert(write_list(c.entries, |e: CertificateEntry| write_certificate_entry(e)) =~= Seq::<u8>::empty());
    lemma_read_certificate_write(c);
}

} // verus!
