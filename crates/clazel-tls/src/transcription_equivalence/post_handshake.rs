//! RFC 8446 §4.6, §5, §6 and §7.2: the client after the handshake,
//! `connection/post_handshake_spec.rs`, against the clean-room
//! transcription's CONNECTED state (`state_machine::receive_post_handshake`,
//! `post_handshake.rs`) and the record layer of `connection.rs` around it
//! (`receive_stream`, `send_application_data`, `send_key_update`,
//! `close_write`, `updated_traffic`): [`theorem_post_handshake_equivalence`].

#[cfg(verus_only)]
use crate::connection::post_handshake_spec::{End, Phase, State};
#[cfg(verus_only)]
use crate::spec::MsgKind;
#[cfg(verus_only)]
use crate::transcription::alerts::ClientError;
#[cfg(verus_only)]
use crate::transcription::connection::{Connection, Protection, SendResult};
#[cfg(verus_only)]
use crate::transcription::extensions::TableMessage;
#[cfg(verus_only)]
use crate::transcription::primitives::Primitives;
#[cfg(verus_only)]
use crate::transcription::state_machine::{ClientState, HandshakeStep};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Hypotheses on the primitives.
// ---------------------------------------------------------------------------

/// The crate's key-explicit AEAD (`traffic::spec::Cipher`) is the
/// transcription's AEAD-Encrypt and AEAD-Decrypt, for every key.
pub open spec fn cipher_agrees(f: crate::traffic::spec::Cipher, p: Primitives) -> bool {
    &&& forall|k: Seq<u8>, n: Seq<u8>, ad: Seq<u8>, x: Seq<u8>|
        #[trigger] (f.seal)(k, n, ad, x) == (p.aead_encrypt)(k, n, ad, x)
    &&& forall|k: Seq<u8>, n: Seq<u8>, ad: Seq<u8>, x: Seq<u8>|
        #[trigger] (f.open)(k, n, ad, x) == (p.aead_decrypt)(k, n, ad, x)
}

/// HKDF-Expand gives the `L` octets asked for (RFC 5869 §2.3: "OKM (output
/// keying material of length L octets)"), for §7.2's `Hash.length` of 32.
pub open spec fn expand_is_sized(p: Primitives) -> bool {
    forall|prk: Seq<u8>, info: Seq<u8>| #[trigger] (p.hkdf_expand)(prk, info, 32).len() == 32
}

/// Every hypothesis of the theorem: the two sides' primitives are the same
/// functions, and HKDF-Expand's output has its length.
pub open spec fn hypotheses(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives) -> bool {
    super::schedule::crypto_agrees(c, p) && cipher_agrees(f, p) && expand_is_sized(p)
}

// ---------------------------------------------------------------------------
// The relation.
// ---------------------------------------------------------------------------

/// One direction: the crate's live epoch and current secret are the
/// transcription's protection, its secret, key, IV and sequence number.
pub open spec fn direction_agrees(ep: Option<crate::traffic::spec::State>, secret: Seq<u8>, pr: Protection) -> bool {
    match ep {
        Some(e) => match pr {
            Protection::Protected(t) => super::record::epoch_agrees(e, t) && t.secret == secret
                && secret.len() == 32 && !e.failed,
            Protection::Unprotected => false,
        },
        None => false,
    }
}

/// The write side: the client's epoch and secret are the transcription's
/// `send`, the epoch has a next sequence number (the crate's item 10), and
/// no KeyUpdate is owed (the crate answers at once; see [`settle`]).
pub open spec fn sender_agrees(s: State, c: Connection) -> bool {
    &&& direction_agrees(s.sender, s.client_secret, c.send)
    &&& s.sender->Some_0.next is Some
    &&& !c.key_update_owed
}

/// The read side: the server's epoch and secret are the transcription's
/// `receive`, and the read side is open.
pub open spec fn receiver_agrees(s: State, c: Connection) -> bool {
    direction_agrees(s.receiver, s.server_secret, c.receive) && !c.read_closed
}

/// The crate's post-handshake state and the transcription's connection in
/// CONNECTED stand for the same connection. The transcription has no
/// write-closed state (`close_write` only gives the record), so once the
/// crate's write side has ended nothing is said of the transcription's
/// `send` or `key_update_owed`; a failed connection has no counterpart (the
/// transcription's run ended with `Abort` or `PeerError`).
pub open spec fn post_agrees(s: State, c: Connection) -> bool {
    &&& c.handshake.state == ClientState::Connected
    &&& match s.phase {
        Phase::Open => sender_agrees(s, c) && receiver_agrees(s, c) && c.handshake_fragments == s.reassembly.buf,
        Phase::WriteClosed => s.sender is None && receiver_agrees(s, c) && c.handshake_fragments == s.reassembly.buf,
        Phase::ReadClosed => sender_agrees(s, c) && s.receiver is None && c.read_closed,
        Phase::Closed => s.sender is None && s.receiver is None && c.read_closed,
        Phase::Failed => false,
    }
}

/// The transcription's connection at the end of the handshake, as A.1's
/// last actions leave it ("K_send = application", "K_recv = application",
/// no partial message, nothing closed or owed).
pub open spec fn established(p: Primitives, c: Connection, client_secret: Seq<u8>, server_secret: Seq<u8>) -> bool {
    &&& c.handshake.state == ClientState::Connected
    &&& c.send == Protection::Protected(crate::transcription::record::traffic_state(p, client_secret))
    &&& c.receive == Protection::Protected(crate::transcription::record::traffic_state(p, server_secret))
    &&& c.handshake_fragments.len() == 0
    &&& !c.read_closed
    &&& !c.key_update_owed
}

// ---------------------------------------------------------------------------
// Proofs: the write side.
// ---------------------------------------------------------------------------

/// The crate's keyed seal of an epoch is the transcription's AEAD-Encrypt
/// under the same key.
pub proof fn lemma_seal(f: crate::traffic::spec::Cipher, p: Primitives, e: crate::traffic::spec::State,
    t: crate::transcription::record::TrafficState)
    requires cipher_agrees(f, p), e.key == t.key,
    ensures
        super::record::seal_agrees(crate::connection::post_handshake_spec::seal_of(f, e), p, t.key),
        super::record::open_agrees(crate::connection::post_handshake_spec::open_of(f, e), p, t.key),
{
    let seal = crate::connection::post_handshake_spec::seal_of(f, e);
    let open = crate::connection::post_handshake_spec::open_of(f, e);
    assert forall|n: Seq<u8>, ad: Seq<u8>, pt: Seq<u8>| #[trigger] seal(n, ad, pt) == (p.aead_encrypt)(t.key, n, ad, pt) by {
        assert((f.seal)(e.key, n, ad, pt) == (p.aead_encrypt)(e.key, n, ad, pt));
    }
    assert forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] open(n, ad, ct) == (p.aead_decrypt)(t.key, n, ad, ct) by {
        assert((f.open)(e.key, n, ad, ct) == (p.aead_decrypt)(e.key, n, ad, ct));
    }
}

/// §7.2: the next generation of a 32-octet traffic secret is 32 octets, and
/// its epoch agrees with the transcription's `updated_traffic`.
pub proof fn lemma_next_epoch(c: crate::schedule::spec::Crypto, p: Primitives, secret: Seq<u8>)
    requires super::schedule::crypto_agrees(c, p), expand_is_sized(p),
    ensures ({
        let next = crate::schedule::spec::next_traffic_secret(c, secret);
        &&& next == crate::transcription::key_schedule::next_application_traffic_secret(p, secret)
        &&& next.len() == 32
        &&& crate::traffic::spec::start(c, next) is Ok
        &&& super::record::epoch_agrees(crate::traffic::spec::start(c, next)->Ok_0,
            crate::transcription::record::traffic_state(p, next))
        &&& !(crate::traffic::spec::start(c, next)->Ok_0).failed
        &&& (crate::traffic::spec::start(c, next)->Ok_0).next == Some(0u64)
    }),
{
    super::schedule::theorem_schedule_equivalence(c, p);
    let next = crate::schedule::spec::next_traffic_secret(c, secret);
    let info = crate::schedule::spec::hkdf_label(crate::schedule::spec::label_bytes(crate::schedule::spec::Label::Update),
        Seq::empty(), 32u16);
    assert(next == (p.hkdf_expand)(secret, info, 32));
    super::record::lemma_epoch_start(c, p, next);
}

/// §4.6.3: the KeyUpdate message both sides write.
pub proof fn lemma_key_update_message(request: u8)
    ensures
        crate::spec::write_handshake(crate::spec::HS_KEY_UPDATE, crate::spec::write_key_update(request))
            == crate::transcription::post_handshake::write_key_update(request as nat),
        crate::spec::write_handshake(crate::spec::HS_KEY_UPDATE, crate::spec::write_key_update(request)).len() == 5,
        crate::transcription::record::fragment_blocks(crate::transcription::post_handshake::write_key_update(request as nat))
            == seq![crate::transcription::post_handshake::write_key_update(request as nat)],
{
    super::auth::lemma_raw(24, seq![request]);
    assert(crate::transcription::presentation::encode_uint((request as nat) / 256, 0) =~= Seq::<u8>::empty());
    assert(crate::transcription::presentation::uint8(request as nat) =~= seq![request]);
}

/// The transcription's `send_blocks` of one block.
pub proof fn lemma_send_block(p: Primitives, t: crate::transcription::record::TrafficState, content_type: nat,
    block: Seq<u8>)
    ensures
        crate::transcription::connection::send_blocks(p, Protection::Protected(t), content_type, 0x0303, seq![block])
            == (seq![crate::transcription::record::protect_record(p, t, content_type, block)],
                Protection::Protected(crate::transcription::record::TrafficState {
                    sequence_number: t.sequence_number + 1, ..t })),
{
    let blocks = seq![block];
    assert(blocks.subrange(1, blocks.len() as int) =~= Seq::<Seq<u8>>::empty());
    let after = Protection::Protected(crate::transcription::record::TrafficState { sequence_number: t.sequence_number + 1, ..t });
    assert(crate::transcription::connection::send_blocks(p, after, content_type, 0x0303, Seq::<Seq<u8>>::empty())
        == (Seq::<Seq<u8>>::empty(), after));
    assert(seq![crate::transcription::record::protect_record(p, t, content_type, block)] + Seq::<Seq<u8>>::empty()
        =~= seq![crate::transcription::record::protect_record(p, t, content_type, block)]);
}

/// One record of `typ` sent by the crate's live send epoch is the
/// transcription's protected record, and the sequence numbers move on
/// together.
pub proof fn lemma_send_record(f: crate::traffic::spec::Cipher, p: Primitives, s: State, c: Connection, typ: u8,
    content: Seq<u8>)
    requires
        cipher_agrees(f, p),
        direction_agrees(s.sender, s.client_secret, c.send),
        s.sender->Some_0.next is Some,
        typ == 21 || typ == 22 || typ == 23,
        content.len() > 0 || typ == 23,
        content.len() <= crate::spec::MAX_PLAINTEXT,
    ensures ({
        let tx = s.sender->Some_0;
        let ts = c.send->Protected_0;
        let r = crate::connection::post_handshake_spec::send_record(f, tx, typ, content);
        &&& r.1 == Ok::<Seq<u8>, u8>(crate::transcription::record::protect_record(p, ts, typ as nat, content))
        &&& super::record::epoch_agrees(r.0,
            crate::transcription::record::TrafficState { sequence_number: ts.sequence_number + 1, ..ts })
        &&& r.0 == crate::traffic::spec::advance(tx)
        &&& !r.0.failed
    }),
{
    let tx = s.sender->Some_0;
    let ts = c.send->Protected_0;
    lemma_seal(f, p, tx, ts);
    super::record::lemma_protect(p, crate::connection::post_handshake_spec::seal_of(f, tx), tx, ts, typ, content);
}

/// §4.6.3, §7.2: a KeyUpdate sent by the crate is the transcription's
/// `send_key_update`: the same record under the old key, then both move to
/// the next generation of the client secret.
pub proof fn lemma_send_key_update(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, conn: Connection, request: u8)
    requires
        hypotheses(c, f, p),
        post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_write(s),
    ensures ({
        let (o, s2) = crate::connection::post_handshake_spec::send_key_update(c, f, s, request);
        let (records, conn2) = crate::transcription::connection::send_key_update(p, conn, request as nat);
        &&& o.wires == records
        &&& o.delivered.len() == 0
        &&& o.end == End::Continue
        &&& s2.phase == s.phase
        &&& post_agrees(s2, conn2)
        &&& conn2 == Connection { send: conn2.send, ..conn }
    }),
{
    let tx = s.sender->Some_0;
    let ts = conn.send->Protected_0;
    let message = crate::spec::write_handshake(crate::spec::HS_KEY_UPDATE, crate::spec::write_key_update(request));
    lemma_key_update_message(request);
    lemma_send_record(f, p, s, conn, crate::spec::CT_HANDSHAKE, message);
    lemma_send_block(p, ts, 22, message);
    lemma_next_epoch(c, p, s.client_secret);
}

/// One application data record sent by the crate's live send epoch, not on
/// its last sequence number.
pub proof fn lemma_send_data(f: crate::traffic::spec::Cipher, p: Primitives, s: State, conn: Connection, data: Seq<u8>)
    requires
        cipher_agrees(f, p),
        post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_write(s),
        s.sender->Some_0.next != Some(u64::MAX),
        data.len() <= crate::spec::MAX_PLAINTEXT,
    ensures ({
        let (o, s2) = crate::connection::post_handshake_spec::send_data_record(f, s, data);
        let (records, send) = crate::transcription::connection::send_blocks(p, conn.send, 23, 0x0303,
            crate::transcription::record::fragment_blocks(data));
        &&& o.wires == records
        &&& o.delivered.len() == 0
        &&& o.end == End::Continue
        &&& s2.phase == s.phase
        &&& post_agrees(s2, Connection { send, ..conn })
    }),
{
    let ts = conn.send->Protected_0;
    lemma_send_record(f, p, s, conn, crate::spec::CT_APPLICATION_DATA, data);
    lemma_send_block(p, ts, 23, data);
    assert(crate::transcription::record::fragment_blocks(data) == seq![data]);
}

/// §5, §5.3: the crate's `send_application` is the transcription's
/// `send_application_data`, for a record of at most 2^14 octets: the
/// KeyUpdate before the last sequence number, the same records and agreeing
/// states.
pub proof fn lemma_send_application(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, conn: Connection, data: Seq<u8>)
    requires
        hypotheses(c, f, p),
        post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_write(s),
        data.len() <= crate::spec::MAX_PLAINTEXT,
    ensures ({
        let (o, s2) = crate::connection::post_handshake_spec::send_application(c, f, s, data);
        match crate::transcription::connection::send_application_data(p, conn, data) {
            SendResult::Sent(records, conn2) => {
                &&& o.wires == records
                &&& o.delivered.len() == 0
                &&& o.end == End::Continue
                &&& s2.phase == s.phase
                &&& post_agrees(s2, conn2)
            },
            SendResult::NotConnected => false,
        }
    }),
{
    let tx = s.sender->Some_0;
    let ts = conn.send->Protected_0;
    assert(crate::transcription::record::fragment_blocks(data) == seq![data]);
    assert(Connection { key_update_owed: false, ..conn } == conn);
    if crate::connection::post_handshake_spec::needs_rekey(s) {
        lemma_send_key_update(c, f, p, s, conn, crate::spec::UPDATE_NOT_REQUESTED);
        let (o1, s1) = crate::connection::post_handshake_spec::send_key_update(c, f, s, crate::spec::UPDATE_NOT_REQUESTED);
        let (r1, conn1) = crate::transcription::connection::send_key_update(p, conn, 0);
        lemma_next_epoch(c, p, s.client_secret);
        lemma_send_data(f, p, s1, conn1, data);
        let (o2, s2) = crate::connection::post_handshake_spec::send_data_record(f, s1, data);
        let (r2, send) = crate::transcription::connection::send_blocks(p, conn1.send, 23, 0x0303, seq![data]);
        assert(conn1 == Connection { key_update_owed: false, ..conn1 });
    } else {
        lemma_send_data(f, p, s, conn, data);
        assert(Seq::<Seq<u8>>::empty() + crate::transcription::connection::send_blocks(p, conn.send, 23, 0x0303,
            seq![data]).0 =~= crate::transcription::connection::send_blocks(p, conn.send, 23, 0x0303, seq![data]).0);
    }
}

/// §4.6.3: the crate's client-initiated KeyUpdate is the transcription's
/// `send_key_update` of the same request.
pub proof fn lemma_update_keys(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, conn: Connection, request_peer: bool)
    requires
        hypotheses(c, f, p),
        post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_write(s),
    ensures ({
        let (o, s2) = crate::connection::post_handshake_spec::update_keys(c, f, s, request_peer);
        let (records, conn2) = crate::transcription::connection::send_key_update(p, conn,
            if request_peer { crate::transcription::post_handshake::update_requested() }
            else { crate::transcription::post_handshake::update_not_requested() });
        &&& o.wires == records
        &&& o.delivered.len() == 0
        &&& o.end == End::Continue
        &&& s2.phase == s.phase
        &&& post_agrees(s2, conn2)
    }),
{
    let request = if request_peer { crate::spec::UPDATE_REQUESTED } else { crate::spec::UPDATE_NOT_REQUESTED };
    lemma_send_key_update(c, f, p, s, conn, request);
}

/// §6.1: the crate's close is the transcription's `close_write`: the same
/// `close_notify` record; the crate's write side then ends, which the
/// transcription does not record.
pub proof fn lemma_close(f: crate::traffic::spec::Cipher, p: Primitives, s: State, conn: Connection)
    requires
        cipher_agrees(f, p),
        post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_write(s),
    ensures ({
        let (o, s2) = crate::connection::post_handshake_spec::close(f, s);
        &&& o.wires == seq![crate::transcription::connection::close_write(p, conn)]
        &&& o.delivered.len() == 0
        &&& o.end == (if s.phase == Phase::Open { End::Continue } else { End::Close })
        &&& post_agrees(s2, conn)
    }),
{
    let a = crate::spec::Alert { level: crate::spec::LEVEL_WARNING, description: crate::spec::CLOSE_NOTIFY };
    lemma_send_record(f, p, s, conn, crate::spec::CT_ALERT, crate::spec::write_alert(a));
    assert(crate::transcription::alerts::write_alert(0) =~= crate::spec::write_alert(a));
}

/// §7.1, §7.3: the crate's starting state agrees with the transcription's
/// connection at the end of the handshake, for the same two secrets.
pub proof fn lemma_start(c: crate::schedule::spec::Crypto, p: Primitives, client_secret: Seq<u8>,
    server_secret: Seq<u8>, conn: Connection)
    requires
        super::schedule::crypto_agrees(c, p),
        client_secret.len() == 32,
        server_secret.len() == 32,
        established(p, conn, client_secret, server_secret),
    ensures
        crate::connection::post_handshake_spec::start(c, client_secret, server_secret) is Ok,
        post_agrees(crate::connection::post_handshake_spec::start(c, client_secret, server_secret)->Ok_0, conn),
{
    super::record::lemma_epoch_start(c, p, client_secret);
    super::record::lemma_epoch_start(c, p, server_secret);
    assert(conn.handshake_fragments =~= crate::spec::reasm_new().buf);
}

// ---------------------------------------------------------------------------
// Proofs: one post-handshake message (§4.6).
// ---------------------------------------------------------------------------

/// One extension of a NewSessionTicket that §4.2's table allows there: its
/// body fails on the transcription's side (`decode_error`) exactly when the
/// crate's `ext_body_ok` does (§4.2.10: early_data's `uint32
/// max_early_data_size`; no other body is read).
pub proof fn lemma_nst_body(e: crate::spec::Ext)
    requires crate::spec::extension_allowed(e.etype, MsgKind::Nst),
    ensures
        crate::transcription::extension_bodies::one_body_failures(seq![], super::messages::ext_view(e), TableMessage::Nst)
            == if crate::spec::ext_body_ok(e, MsgKind::Nst) { Seq::<ClientError>::empty() }
            else { seq![ClientError::Malformed] },
{
    super::extensions::lemma_table(e.etype, MsgKind::Nst);
}

/// A NewSessionTicket's block, its extensions all allowed there: every body
/// failure is `Malformed`, and there is none exactly when the crate's body
/// checks pass.
pub proof fn lemma_nst_bodies(es: Seq<crate::spec::Ext>)
    requires crate::spec::all_allowed(es, MsgKind::Nst),
    ensures ({
        let f = crate::transcription::extension_bodies::extension_body_failures(seq![], super::messages::exts_view(es),
            TableMessage::Nst);
        &&& (f.len() == 0) == crate::spec::all_bodies_ok(es, MsgKind::Nst)
        &&& forall|i: int| 0 <= i < f.len() ==> #[trigger] f[i] == ClientError::Malformed
    }),
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    let f = crate::transcription::extension_bodies::extension_body_failures(seq![], v, TableMessage::Nst);
    if es.len() > 0 {
        let rest = es.skip(1);
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(rest));
        assert(v[0] == super::messages::ext_view(es[0]));
        lemma_nst_bodies(rest);
        lemma_nst_body(es[0]);
        let mine = crate::transcription::extension_bodies::one_body_failures(seq![], v[0], TableMessage::Nst);
        let tail = crate::transcription::extension_bodies::extension_body_failures(seq![],
            super::messages::exts_view(rest), TableMessage::Nst);
        assert(f == mine + tail);
        assert forall|i: int| 0 <= i < f.len() implies #[trigger] f[i] == ClientError::Malformed by {
            if i >= mine.len() {
                assert(f[i] == tail[i - mine.len()]);
            }
        }
    }
}

/// §4.6.1 syntax: a NewSessionTicket reads the same on both sides.
pub proof fn lemma_read_nst(body: Seq<u8>)
    ensures
        match crate::spec::read_new_session_ticket(body) {
            None => crate::transcription::post_handshake::read_new_session_ticket(body) is None,
            Some(n) => {
                &&& crate::transcription::post_handshake::read_new_session_ticket(body) is Some
                &&& crate::transcription::post_handshake::read_new_session_ticket(body)->Some_0.extensions
                    == super::messages::exts_view(n.extensions)
                &&& crate::transcription::post_handshake::read_new_session_ticket(body)->Some_0.ticket_lifetime
                    == n.ticket_lifetime as nat
            },
        },
{
    if body.len() >= 8 {
        let r2 = body.skip(4).skip(4);
        assert(r2 =~= body.subrange(8, body.len() as int));
        super::messages::lemma_read_vec(r2, 0, 255);
        match crate::spec::read_vec(r2, 0, 255) {
            None => {},
            Some((nonce, r3)) => {
                super::messages::lemma_read_vec(r3, 1, 65535);
                match crate::spec::read_vec(r3, 1, 65535) {
                    None => {},
                    Some((ticket, r4)) => {
                        super::messages::lemma_read_exts(r4, 0, 65534);
                        super::record::lemma_read_uint(body, 4);
                        crate::lemmas_pl::lemma_be_value_bound(body.take(4));
                        assert(crate::spec::pow256(4) == 0x1_0000_0000) by (compute_only);
                    },
                }
            },
        }
    }
}

/// §4.6.1: a NewSessionTicket in CONNECTED. The crate's parser refuses it
/// exactly when the transcription aborts, with the alert of the
/// transcription's first failure (both check the lifetime, then §4.2's
/// block rules, then the bodies); otherwise both go on with nothing to do.
pub proof fn lemma_nst(hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>)
    ensures
        match crate::spec::parse_handshake_body(4, body, 32) {
            crate::spec::Res::Err(k) => {
                let t = crate::transcription::state_machine::receive_post_handshake(hs, 4, body);
                &&& t is Abort
                &&& crate::transcription::alerts::required_alert(t->Abort_0) == crate::spec::alert_of(k) as nat
            },
            crate::spec::Res::Ok(m) => {
                &&& m is NewSessionTicket
                &&& crate::transcription::state_machine::receive_post_handshake(hs, 4, body)
                    == crate::transcription::state_machine::proceed(hs, seq![])
            },
        },
{
    lemma_read_nst(body);
    match crate::spec::read_new_session_ticket(body) {
        None => {},
        Some(n) => {
            let m = crate::transcription::post_handshake::read_new_session_ticket(body)->Some_0;
            let es = n.extensions;
            let ev = super::messages::exts_view(es);
            assert(m.extensions == ev);
            let life = crate::transcription::alerts::fails_if(m.ticket_lifetime > 604800, ClientError::TicketLifetimeTooLong);
            let dup = crate::transcription::alerts::fails_if(crate::transcription::extensions::has_duplicate_extension(ev),
                ClientError::DuplicateExtension);
            let nsp = crate::transcription::alerts::fails_if(
                crate::transcription::extensions::any_not_specified(ev, TableMessage::Nst),
                ClientError::ExtensionNotSpecifiedForMessage);
            let bf = crate::transcription::extension_bodies::extension_body_failures(seq![], ev, TableMessage::Nst);
            let failures = crate::transcription::post_handshake::new_session_ticket_failures(m);
            assert(crate::transcription::extensions::block_rules_failures(ev, TableMessage::Nst) == dup + nsp);
            assert(failures == life + (dup + nsp) + bf);
            super::extensions::lemma_unique(es);
            super::extensions::lemma_all_allowed(es, MsgKind::Nst);
            if n.ticket_lifetime > 604800 {
                assert(failures[0] == ClientError::TicketLifetimeTooLong);
            } else if !crate::spec::exts_unique(es) {
                assert(failures[0] == ClientError::DuplicateExtension);
            } else if !crate::spec::all_allowed(es, MsgKind::Nst) {
                assert(failures[0] == ClientError::ExtensionNotSpecifiedForMessage);
            } else {
                lemma_nst_bodies(es);
                assert(failures =~= bf);
                if bf.len() > 0 {
                    assert(bf[0] == ClientError::Malformed);
                }
            }
        },
    }
}

/// §4.6.3: a KeyUpdate in CONNECTED. The crate's parser refuses it exactly
/// when the transcription aborts, with the same alert; otherwise the request
/// is one of the two defined values and the transcription updates its read
/// side, owing a KeyUpdate of its own on `update_requested`, with a key
/// change after the message.
pub proof fn lemma_ku(hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>)
    ensures
        match crate::spec::parse_handshake_body(24, body, 32) {
            crate::spec::Res::Err(k) => {
                let t = crate::transcription::state_machine::receive_post_handshake(hs, 24, body);
                &&& t is Abort
                &&& crate::transcription::alerts::required_alert(t->Abort_0) == crate::spec::alert_of(k) as nat
            },
            crate::spec::Res::Ok(m) => {
                &&& m is KeyUpdate
                &&& (m->KeyUpdate_0 == crate::spec::UPDATE_NOT_REQUESTED || m->KeyUpdate_0 == crate::spec::UPDATE_REQUESTED)
                &&& crate::transcription::state_machine::receive_post_handshake(hs, 24, body) == HandshakeStep::Proceed {
                    handshake: hs,
                    actions: if m->KeyUpdate_0 == crate::spec::UPDATE_REQUESTED {
                        seq![crate::transcription::state_machine::Action::UpdateReceiveSecret,
                            crate::transcription::state_machine::Action::RespondToKeyUpdate]
                    } else {
                        seq![crate::transcription::state_machine::Action::UpdateReceiveSecret]
                    },
                    receive_key_changes: true,
                }
            },
        },
{
}

/// §4.6: a message of any other type in CONNECTED is `unexpected_message`
/// on both sides (the transcription names three cases, all with that alert).
pub proof fn lemma_other_type(hs: crate::transcription::state_machine::ClientHandshake, t: u8, body: Seq<u8>)
    requires t != 4 && t != 24,
    ensures
        crate::transcription::state_machine::receive_post_handshake(hs, t as nat, body) is Abort,
        crate::transcription::alerts::required_alert(
            crate::transcription::state_machine::receive_post_handshake(hs, t as nat, body)->Abort_0) == 10,
{
}

// ---------------------------------------------------------------------------
// The handshake messages of one record.
// ---------------------------------------------------------------------------

/// §4.6.3, the one difference in what is sent: "If the request_update field
/// is set to "update_requested", then the receiver MUST send a KeyUpdate of
/// its own with request_update set to "update_not_requested" prior to sending
/// its next Application Data record." The crate sends it at once, in the
/// step that receives the request (its item 9); the transcription records it
/// as owed (`key_update_owed`) and sends it first in its next
/// `send_application_data`. `settle` is that send of the owed KeyUpdate
/// (exactly what `send_application_data` does first), while the crate's
/// write side is open: the crate's records are the transcription's followed
/// by these, and its state is the transcription's after them.
pub open spec fn settle(p: Primitives, s: State, c: Connection) -> (Seq<Seq<u8>>, Connection) {
    if s.phase == Phase::Open && c.key_update_owed {
        crate::transcription::connection::send_key_update(p, Connection { key_update_owed: false, ..c },
            crate::transcription::post_handshake::update_not_requested())
    } else {
        (seq![], c)
    }
}

/// What the crate sends when it fails with `alert`: while its write side is
/// open, the transcription's `alert_record` of that description (§6.2: a
/// fatal alert, under the current client key); after its close_notify,
/// nothing (§6.1).
pub open spec fn alert_wires(p: Primitives, s: State, c: Connection, alert: u8) -> Seq<Seq<u8>> {
    if crate::connection::post_handshake_spec::can_write(s) {
        seq![crate::transcription::connection::alert_record(p, c, alert as nat)]
    } else {
        seq![]
    }
}

/// [`post_agrees`] with the read side open, except perhaps for the bytes of
/// an unfinished handshake message (the crate keeps those it has not yet
/// read as messages in its reassembly buffer).
pub open spec fn agrees_but_buffer(s: State, c: Connection) -> bool {
    &&& (s.phase == Phase::Open || s.phase == Phase::WriteClosed)
    &&& post_agrees(s, Connection { handshake_fragments: s.reassembly.buf, ..c })
}

/// The crate's processing of a record's messages (`messages`) and the
/// transcription's (`process_handshake_bytes`) agree: both fail, with the
/// same alert and the crate sending the transcription's alert record; or both
/// go on, delivering and (but for [`settle`]) sending nothing, in agreeing
/// states.
pub open spec fn messages_agree(p: Primitives, s: State, c: Connection,
    r: (crate::connection::post_handshake_spec::Out, State), t: crate::transcription::connection::Receive) -> bool
{
    let (o, s2) = r;
    &&& o.delivered.len() == 0
    &&& match o.end {
        End::Fail(a) => {
            &&& s2 == crate::connection::post_handshake_spec::failed()
            &&& t is Abort
            &&& crate::transcription::alerts::required_alert(t->Abort_0) == a as nat
            &&& o.wires == alert_wires(p, s, c, a)
        },
        End::Continue => match t {
            crate::transcription::connection::Receive::Continue(progress) => {
                &&& progress.application_data.len() == 0
                &&& progress.records_to_send.len() == 0
                &&& s2.phase == s.phase
                &&& o.wires == settle(p, s2, progress.connection).0
                &&& post_agrees(s2, settle(p, s2, progress.connection).1)
            },
            _ => false,
        },
        _ => false,
    }
}

/// §6.2: the crate's fatal error with a description other than the two
/// closure alerts is the transcription's `alert_record` of it, sent while
/// the write side is open.
pub proof fn lemma_fatal(f: crate::traffic::spec::Cipher, p: Primitives, s: State, c: Connection, alert: u8)
    requires
        cipher_agrees(f, p),
        agrees_but_buffer(s, c),
        alert != 0 && alert != 90,
    ensures
        crate::connection::post_handshake_spec::fatal(f, s, alert)
            == (crate::connection::post_handshake_spec::Out { wires: alert_wires(p, s, c, alert), delivered: seq![],
                end: End::Fail(alert) }, crate::connection::post_handshake_spec::failed()),
{
    if s.phase == Phase::Open {
        let a = crate::spec::Alert { level: crate::spec::LEVEL_FATAL, description: alert };
        let c2 = Connection { handshake_fragments: s.reassembly.buf, ..c };
        lemma_send_record(f, p, s, c2, crate::spec::CT_ALERT, crate::spec::write_alert(a));
        assert(crate::transcription::alerts::write_alert(alert as nat) =~= crate::spec::write_alert(a));
    }
}

/// `alert_of` never names a closure alert.
pub proof fn lemma_alert_of(k: crate::spec::ErrKind)
    ensures crate::spec::alert_of(k) != 0 && crate::spec::alert_of(k) != 90,
{
}

/// §4: one more message off the front of a buffer the crate has split into
/// messages.
pub proof fn lemma_extract_more(bf: Seq<u8>)
    requires
        crate::spec::extract_messages(bf) is Ok,
        crate::spec::extract_messages(bf)->Ok_0.0.len() > 0,
    ensures ({
        let (ms, r) = crate::spec::extract_messages(bf)->Ok_0;
        let n = super::bootstrap::first_length(bf);
        &&& 4 <= n <= bf.len()
        &&& crate::spec::extract_messages(bf.skip(n as int)) == crate::spec::Res::Ok((ms.skip(1), r))
        &&& ms[0] == bf.subrange(0, n as int)
        &&& bf.skip(n as int).len() < bf.len()
    }),
{
    let n = super::bootstrap::first_length(bf);
    let (ms, r) = crate::spec::extract_messages(bf)->Ok_0;
    let (tail, rest) = crate::spec::extract_messages(bf.skip(n as int))->Ok_0;
    assert(ms == seq![bf.take(n as int)] + tail);
    assert(ms.skip(1) =~= tail);
    assert(bf.take(n as int) =~= bf.subrange(0, n as int));
}

/// A KeyUpdate's actions, in A.1's order (`receive_post_handshake`).
pub open spec fn ku_actions(requested: bool) -> Seq<crate::transcription::state_machine::Action> {
    if requested {
        seq![crate::transcription::state_machine::Action::UpdateReceiveSecret,
            crate::transcription::state_machine::Action::RespondToKeyUpdate]
    } else {
        seq![crate::transcription::state_machine::Action::UpdateReceiveSecret]
    }
}

/// The transcription's `apply_actions` of a KeyUpdate's actions: the read
/// side moves to the next generation (§4.6.3, §7.2); on `update_requested`
/// a KeyUpdate is owed; nothing is written.
pub proof fn lemma_ku_actions(p: Primitives, c: Connection, requested: bool)
    ensures
        crate::transcription::connection::apply_actions(p, c, ku_actions(requested))
            == (Connection {
                receive: crate::transcription::connection::updated_traffic(p, c.receive),
                key_update_owed: c.key_update_owed || requested,
                ..c
            }, Seq::<Seq<u8>>::empty()),
{
    let c1 = Connection { receive: crate::transcription::connection::updated_traffic(p, c.receive), ..c };
    let e = Seq::<crate::transcription::state_machine::Action>::empty();
    assert(crate::transcription::connection::apply_actions(p, c1, e) == (c1, Seq::<Seq<u8>>::empty()));
    if requested {
        let a = ku_actions(true);
        let a1 = seq![crate::transcription::state_machine::Action::RespondToKeyUpdate];
        assert(a.subrange(1, 2) =~= a1);
        assert(a1.subrange(1, 1) =~= e);
        let c2 = Connection { key_update_owed: true, ..c1 };
        assert(crate::transcription::connection::apply_actions(p, c2, e) == (c2, Seq::<Seq<u8>>::empty()));
        assert(crate::transcription::connection::apply_actions(p, c1, a1)
            == crate::transcription::connection::apply_actions(p, c2, e));
        assert(crate::transcription::connection::apply_actions(p, c, a)
            == crate::transcription::connection::apply_actions(p, c1, a1));
    } else {
        let a = ku_actions(false);
        assert(a.subrange(1, 1) =~= e);
        assert(crate::transcription::connection::apply_actions(p, c, a)
            == crate::transcription::connection::apply_actions(p, c1, e));
    }
}

/// The transcription's `process_handshake_bytes` with no whole message left:
/// the bytes wait for the next record.
pub proof fn lemma_t_incomplete(p: Primitives, y: Connection, bf: Seq<u8>)
    requires
        match crate::transcription::key_exchange::read_handshake_header(bf) {
            None => true,
            Some(h) => bf.len() < 4 + h.length,
        },
    ensures
        crate::transcription::connection::process_handshake_bytes(p, y, bf)
            == crate::transcription::connection::Receive::Continue(crate::transcription::connection::Progress {
                connection: Connection { handshake_fragments: bf, ..y },
                application_data: seq![],
                records_to_send: seq![],
            }),
{
}

/// The transcription's `process_handshake_bytes` on its first whole
/// message in CONNECTED: `receive_post_handshake`, §5.1's alignment check on
/// a key change, the actions, then the rest of the buffer.
pub proof fn lemma_t_first(p: Primitives, y: Connection, bf: Seq<u8>, n: nat)
    requires
        y.handshake.state == ClientState::Connected,
        4 <= n <= bf.len(),
        crate::transcription::key_exchange::read_handshake_header(bf) is Some,
        4 + crate::transcription::key_exchange::read_handshake_header(bf)->Some_0.length == n,
    ensures ({
        let rest = bf.subrange(n as int, bf.len() as int);
        crate::transcription::connection::process_handshake_bytes(p, y, bf)
            == match crate::transcription::state_machine::receive_post_handshake(y.handshake, bf[0] as nat,
                bf.subrange(4, n as int)) {
                HandshakeStep::Abort(e) => crate::transcription::connection::Receive::Abort(e),
                HandshakeStep::Proceed { handshake, actions, receive_key_changes } =>
                    if receive_key_changes && rest.len() != 0 {
                        crate::transcription::connection::Receive::Abort(ClientError::KeyChangeNotAligned)
                    } else {
                        let (after, sent) = crate::transcription::connection::apply_actions(p,
                            Connection { handshake, ..y }, actions);
                        super::bootstrap::after_records(sent,
                            crate::transcription::connection::process_handshake_bytes(p, after, rest))
                    },
            }
    }),
{
    let raw = bf.subrange(0, n as int);
    assert(raw.subrange(4, raw.len() as int) =~= bf.subrange(4, n as int));
    assert(raw[0] == bf[0]);
}

/// The crate's `message` on one whole message `m`: the type, then the
/// parser, then the KeyUpdate's own handling.
pub proof fn lemma_c_first(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, m: Seq<u8>,
    last: bool)
    requires
        m.len() >= 4,
        m.len() == 4 + crate::spec::be_value(m.subrange(1, 4)),
    ensures
        crate::connection::post_handshake_spec::message(c, f, s, m, last) == if m[0] != 4 && m[0] != 24 {
            crate::connection::post_handshake_spec::fatal(f, s, 10)
        } else {
            match crate::spec::parse_handshake_body(m[0], m.skip(4), 32) {
                crate::spec::Res::Err(k) => crate::connection::post_handshake_spec::fatal(f, s, crate::spec::alert_of(k)),
                crate::spec::Res::Ok(crate::spec::HsMsg::KeyUpdate(r)) =>
                    crate::connection::post_handshake_spec::key_update_received(c, f, s, r, last),
                crate::spec::Res::Ok(_) => (crate::connection::post_handshake_spec::quiet(), s),
            }
        },
{
}

/// A message the crate refuses with `a`, which the transcription refuses
/// with the same alert: the record's processing ends there on both sides.
pub proof fn lemma_msgs_fail(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, y: Connection, ms: Seq<Seq<u8>>, t: crate::transcription::connection::Receive, a: u8)
    requires
        cipher_agrees(f, p),
        agrees_but_buffer(s, y),
        ms.len() > 0,
        a != 0 && a != 90,
        crate::connection::post_handshake_spec::message(c, f, s, ms[0], ms.len() == 1)
            == crate::connection::post_handshake_spec::fatal(f, s, a),
        t is Abort,
        crate::transcription::alerts::required_alert(t->Abort_0) == a as nat,
    ensures
        messages_agree(p, s, y, crate::connection::post_handshake_spec::messages(c, f, s, ms), t),
{
    lemma_fatal(f, p, s, y, a);
}

/// An accepted NewSessionTicket: nothing happens on either side, and the
/// rest of the record is processed from the same states.
pub proof fn lemma_msgs_nst(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, y: Connection, ms: Seq<Seq<u8>>, t_rest: crate::transcription::connection::Receive)
    requires
        ms.len() > 0,
        crate::connection::post_handshake_spec::can_read(s),
        crate::connection::post_handshake_spec::message(c, f, s, ms[0], ms.len() == 1)
            == (crate::connection::post_handshake_spec::quiet(), s),
        messages_agree(p, s, y, crate::connection::post_handshake_spec::messages(c, f, s, ms.skip(1)), t_rest),
    ensures
        messages_agree(p, s, y, crate::connection::post_handshake_spec::messages(c, f, s, ms),
            super::bootstrap::after_records(seq![], t_rest)),
{
    let (o2, s2) = crate::connection::post_handshake_spec::messages(c, f, s, ms.skip(1));
    assert(Seq::<Seq<u8>>::empty() + o2.wires =~= o2.wires);
    match t_rest {
        crate::transcription::connection::Receive::Continue(pr) => {
            assert(Seq::<Seq<u8>>::empty() + pr.records_to_send =~= pr.records_to_send);
        },
        _ => {},
    }
}

/// §4.6.3, §5.1, §7.2: a valid KeyUpdate that ends its record at a message
/// boundary. Both sides move the read side to the next generation; on
/// `update_requested` the crate sends its KeyUpdate at once and the
/// transcription owes it ([`settle`]).
pub proof fn lemma_msgs_ku(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, y: Connection, ms: Seq<Seq<u8>>, req: u8)
    requires
        hypotheses(c, f, p),
        agrees_but_buffer(s, y),
        s.reassembly.buf.len() == 0,
        ms.len() == 1,
        req == 0 || req == 1,
        crate::connection::post_handshake_spec::message(c, f, s, ms[0], true)
            == crate::connection::post_handshake_spec::key_update_received(c, f, s, req, true),
    ensures ({
        let after = crate::transcription::connection::apply_actions(p, y, ku_actions(req == 1)).0;
        messages_agree(p, s, y, crate::connection::post_handshake_spec::messages(c, f, s, ms),
            crate::transcription::connection::Receive::Continue(crate::transcription::connection::Progress {
                connection: Connection { handshake_fragments: Seq::empty(), ..after },
                application_data: Seq::empty(),
                records_to_send: Seq::empty(),
            }))
    }),
{
    let requested = req == 1;
    lemma_next_epoch(c, p, s.server_secret);
    lemma_ku_actions(p, y, requested);
    let s1r = crate::connection::post_handshake_spec::rotated_receiver(c, s)->Ok_0;
    let next = crate::schedule::spec::next_traffic_secret(c, s.server_secret);
    let yb = Connection { handshake_fragments: s.reassembly.buf, ..y };
    assert(s.reassembly.buf =~= Seq::<u8>::empty());
    assert(direction_agrees(s.receiver, s.server_secret, yb.receive));
    let tr = y.receive->Protected_0;
    assert(tr.secret == s.server_secret);
    let updated = crate::transcription::connection::updated_traffic(p, y.receive);
    assert(updated == Protection::Protected(crate::transcription::record::traffic_state(p, next)));
    assert(s1r == State { receiver: Some(crate::traffic::spec::start(c, next)->Ok_0), server_secret: next, ..s });
    assert(direction_agrees(s1r.receiver, s1r.server_secret, updated));
    let after = Connection { receive: updated, key_update_owed: y.key_update_owed || requested, ..y };
    let after0 = Connection { handshake_fragments: Seq::empty(), ..after };
    assert(ms.skip(1) =~= Seq::<Seq<u8>>::empty());
    assert(crate::connection::post_handshake_spec::key_update_received(c, f, s, req, true) == if requested {
        crate::connection::post_handshake_spec::send_key_update(c, f, s1r, crate::spec::UPDATE_NOT_REQUESTED)
    } else {
        (crate::connection::post_handshake_spec::quiet(), s1r)
    });
    if s.phase == Phase::Open {
        assert(sender_agrees(s, yb));
        if requested {
            let y1 = Connection { key_update_owed: false, ..after0 };
            assert(sender_agrees(s1r, y1));
            assert(receiver_agrees(s1r, y1));
            assert(post_agrees(s1r, y1));
            lemma_send_key_update(c, f, p, s1r, y1, crate::spec::UPDATE_NOT_REQUESTED);
            let (o2, s2) = crate::connection::post_handshake_spec::send_key_update(c, f, s1r,
                crate::spec::UPDATE_NOT_REQUESTED);
            assert(o2.wires + Seq::<Seq<u8>>::empty() =~= o2.wires);
            lemma_messages_last(c, f, s, ms, o2, s2);
            assert(settle(p, s2, after0) == crate::transcription::connection::send_key_update(p, y1, 0));
        } else {
            assert(sender_agrees(s1r, after0));
            assert(receiver_agrees(s1r, after0));
            assert(post_agrees(s1r, after0));
            lemma_messages_last(c, f, s, ms, crate::connection::post_handshake_spec::quiet(), s1r);
        }
    } else {
        assert(receiver_agrees(s1r, after0));
        assert(post_agrees(s1r, after0));
        if requested {
            assert(!crate::connection::post_handshake_spec::can_write(s1r));
        }
        lemma_messages_last(c, f, s, ms, crate::connection::post_handshake_spec::quiet(), s1r);
    }
}

/// The crate's `messages` on a last message that leaves the read side open.
pub proof fn lemma_messages_last(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State,
    ms: Seq<Seq<u8>>, o: crate::connection::post_handshake_spec::Out, s2: State)
    requires
        ms.len() == 1,
        crate::connection::post_handshake_spec::message(c, f, s, ms[0], true) == (o, s2),
        crate::connection::post_handshake_spec::can_read(s2),
    ensures
        crate::connection::post_handshake_spec::messages(c, f, s, ms)
            == (crate::connection::post_handshake_spec::then(o, crate::connection::post_handshake_spec::quiet()), s2),
{
    assert(ms.skip(1) =~= Seq::<Seq<u8>>::empty());
    assert(crate::connection::post_handshake_spec::messages(c, f, s2, Seq::empty())
        == (crate::connection::post_handshake_spec::quiet(), s2));
}

/// No whole message in the buffer: nothing happens on the crate's side, and
/// the transcription keeps the bytes as its fragments, which are the crate's
/// reassembly buffer.
pub proof fn lemma_msgs_none(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, y: Connection, bf: Seq<u8>)
    requires
        agrees_but_buffer(s, y),
        s.reassembly.buf == bf,
        match crate::transcription::key_exchange::read_handshake_header(bf) {
            None => true,
            Some(h) => bf.len() < 4 + h.length,
        },
    ensures
        messages_agree(p, s, y, crate::connection::post_handshake_spec::messages(c, f, s, Seq::empty()),
            crate::transcription::connection::process_handshake_bytes(p, y, bf)),
{
    lemma_t_incomplete(p, y, bf);
}

/// The transcription's connection of agreeing states is in CONNECTED.
pub proof fn lemma_connected(s: State, y: Connection)
    requires agrees_but_buffer(s, y),
    ensures
        y.handshake.state == ClientState::Connected,
        crate::connection::post_handshake_spec::can_read(s),
{
}

/// The transcription's `apply_actions` of no action.
pub proof fn lemma_apply_none(p: Primitives, y: Connection)
    ensures crate::transcription::connection::apply_actions(p, y, seq![]) == (y, Seq::<Seq<u8>>::empty()),
{
}

/// The facts of the first whole message of a buffer, for
/// [`lemma_msgs_first`].
pub open spec fn first_facts(s: State, y: Connection, bf: Seq<u8>) -> bool {
    &&& agrees_but_buffer(s, y)
    &&& crate::spec::extract_messages(bf) is Ok
    &&& crate::spec::extract_messages(bf)->Ok_0.0.len() > 0
    &&& s.reassembly.buf == crate::spec::extract_messages(bf)->Ok_0.1
}

/// The first whole message of a buffer, given that the rest of the buffer
/// agrees (the induction step of [`lemma_messages`]).
#[verifier::rlimit(30)]
pub proof fn lemma_msgs_first(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, y: Connection, bf: Seq<u8>)
    requires
        hypotheses(c, f, p),
        first_facts(s, y, bf),
        messages_agree(p, s, y,
            crate::connection::post_handshake_spec::messages(c, f, s, crate::spec::extract_messages(bf)->Ok_0.0.skip(1)),
            crate::transcription::connection::process_handshake_bytes(p, y, bf.skip(super::bootstrap::first_length(bf) as int))),
    ensures
        messages_agree(p, s, y,
            crate::connection::post_handshake_spec::messages(c, f, s, crate::spec::extract_messages(bf)->Ok_0.0),
            crate::transcription::connection::process_handshake_bytes(p, y, bf)),
{
    hide(crate::connection::post_handshake_spec::messages);
    hide(crate::connection::post_handshake_spec::message);
    hide(crate::connection::post_handshake_spec::fatal);
    hide(crate::connection::post_handshake_spec::key_update_received);
    hide(crate::spec::parse_handshake_body);
    hide(crate::spec::extract_messages);
    hide(crate::transcription::state_machine::receive_post_handshake);
    hide(crate::transcription::connection::process_handshake_bytes);
    hide(crate::transcription::connection::apply_actions);
    hide(messages_agree);
    hide(post_agrees);
    hide(agrees_but_buffer);
    hide(settle);
    let (ms, r) = crate::spec::extract_messages(bf)->Ok_0;
    super::bootstrap::lemma_extract(bf);
    lemma_extract_more(bf);
    let n = super::bootstrap::first_length(bf);
    let m = ms[0];
    let rest = bf.subrange(n as int, bf.len() as int);
    assert(rest =~= bf.skip(n as int));
    lemma_connected(s, y);
    let hs = y.handshake;
    let body = bf.subrange(4, n as int);
    assert(m.skip(4) =~= body);
    assert(m.subrange(1, 4) =~= bf.subrange(1, 4));
    lemma_t_first(p, y, bf, n);
    let last = ms.len() == 1;
    lemma_c_first(c, f, s, m, last);
    let t = crate::transcription::connection::process_handshake_bytes(p, y, bf);
    if m[0] != 4 && m[0] != 24 {
        lemma_other_type(hs, m[0], body);
        lemma_msgs_fail(c, f, p, s, y, ms, t, 10);
    } else {
        if m[0] == 4 {
            lemma_nst(hs, body);
        } else {
            lemma_ku(hs, body);
        }
        match crate::spec::parse_handshake_body(m[0], body, 32) {
            crate::spec::Res::Err(k) => {
                lemma_alert_of(k);
                lemma_msgs_fail(c, f, p, s, y, ms, t, crate::spec::alert_of(k));
            },
            crate::spec::Res::Ok(crate::spec::HsMsg::KeyUpdate(req)) => {
                assert((!last || !crate::spec::at_message_boundary(s.reassembly)) == (rest.len() != 0));
                if rest.len() != 0 {
                    reveal(crate::connection::post_handshake_spec::key_update_received);
                    lemma_msgs_fail(c, f, p, s, y, ms, t, 10);
                } else {
                    assert(Connection { handshake: hs, ..y } == y);
                    lemma_ku_actions(p, y, req == 1);
                    let after = crate::transcription::connection::apply_actions(p, y, ku_actions(req == 1)).0;
                    assert(rest =~= Seq::<u8>::empty());
                    lemma_t_incomplete(p, after, rest);
                    lemma_msgs_ku(c, f, p, s, y, ms, req);
                    let e = Seq::<Seq<u8>>::empty();
                    assert(e + e =~= e);
                }
            },
            crate::spec::Res::Ok(_) => {
                assert(m[0] == 4);
                assert(Connection { handshake: hs, ..y } == y);
                lemma_apply_none(p, y);
                lemma_msgs_nst(c, f, p, s, y, ms, crate::transcription::connection::process_handshake_bytes(p, y, rest));
            },
        }
    }
}

/// §4, §5.1, §4.6: the crate's `messages` on the complete messages of a
/// buffer and the transcription's `process_handshake_bytes` of it agree
/// ([`messages_agree`]), the crate's reassembly state being the bytes after
/// them.
pub proof fn lemma_messages(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives, s: State,
    y: Connection, bf: Seq<u8>)
    requires
        hypotheses(c, f, p),
        agrees_but_buffer(s, y),
        crate::spec::extract_messages(bf) is Ok,
        s.reassembly.buf == crate::spec::extract_messages(bf)->Ok_0.1,
    ensures
        messages_agree(p, s, y,
            crate::connection::post_handshake_spec::messages(c, f, s, crate::spec::extract_messages(bf)->Ok_0.0),
            crate::transcription::connection::process_handshake_bytes(p, y, bf)),
    decreases bf.len(),
{
    hide(crate::connection::post_handshake_spec::messages);
    hide(crate::transcription::connection::process_handshake_bytes);
    hide(messages_agree);
    hide(post_agrees);
    hide(agrees_but_buffer);
    let (ms, r) = crate::spec::extract_messages(bf)->Ok_0;
    super::bootstrap::lemma_extract(bf);
    if ms.len() == 0 {
        assert(r == bf);
        assert(ms =~= Seq::<Seq<u8>>::empty());
        lemma_msgs_none(c, f, p, s, y, bf);
    } else {
        lemma_extract_more(bf);
        let n = super::bootstrap::first_length(bf);
        lemma_messages(c, f, p, s, y, bf.skip(n as int));
        lemma_msgs_first(c, f, p, s, y, bf);
    }
}

// ---------------------------------------------------------------------------
// One record.
// ---------------------------------------------------------------------------

/// Two faults in one record's header, where each side names a different
/// one: a type that is neither application_data nor change_cipher_spec and
/// a length above 2^14. The crate checks the type first (`read_record` step
/// 1, `unexpected_message`), the transcription the length first
/// (`record_overflow`); §5 and §5.1 rank neither.
pub open spec fn two_faults(b: Seq<u8>) -> bool {
    b[0] != crate::spec::CT_CHANGE_CIPHER_SPEC && b[0] != crate::spec::CT_APPLICATION_DATA
        && super::bootstrap::length(b) > crate::spec::MAX_PLAINTEXT
}

/// The crate's receive epoch is exhausted: it has read a record under
/// sequence number 2^64 - 1. The crate then refuses the next record with
/// `internal_error` before looking at it (`traffic::spec::receive`); the
/// transcription checks the record's header first, and refuses one that
/// passes with `SequenceNumberWrap` (`internal_error` too). Unreachable in
/// practice (2^64 records).
pub open spec fn exhausted(s: State) -> bool {
    s.receiver->Some_0.next is None
}

/// The crate's resource cap: the record's handshake content completes a
/// message header announcing more than 2^18 octets (`MAX_HANDSHAKE_BODY`),
/// refused with `internal_error`. §4's `uint24 length` allows it, and the
/// transcription has no cap: it waits for the bytes, or processes the
/// messages before it.
pub open spec fn cap(f: crate::traffic::spec::Cipher, s: State, b: Seq<u8>) -> bool {
    let rx = s.receiver->Some_0;
    match crate::traffic::spec::receive(crate::connection::post_handshake_spec::open_of(f, rx), rx, b).1 {
        crate::traffic::spec::Read::Record(typ, content, _) =>
            typ == crate::spec::CT_HANDSHAKE && crate::spec::extract_messages(s.reassembly.buf + content) is Err,
        _ => false,
    }
}

/// When the crate fails with `a` on a record: the transcription aborts with
/// that alert, or one of the stated differences holds.
pub open spec fn fail_agrees(f: crate::traffic::spec::Cipher, s: State, b: Seq<u8>,
    t: crate::transcription::connection::Receive, a: u8) -> bool
{
    ||| t is Abort && crate::transcription::alerts::required_alert(t->Abort_0) == a as nat
    ||| t is Abort && two_faults(b)
    ||| t is Abort && a == crate::spec::INTERNAL_ERROR && exhausted(s)
    ||| a == crate::spec::INTERNAL_ERROR && cap(f, s, b)
}

/// What the crate does with a record or its content (`o`, `s2`) and what
/// the transcription does (`t`) agree: a failure is the transcription's
/// abort (`failed`: the alert matches, or a stated difference holds), with
/// the transcription's alert record for the crate's alert; the peer's error
/// alert is `PeerError` on both sides; otherwise both go on, deliver the
/// same application data and, but for [`settle`], send nothing, in agreeing
/// states.
pub open spec fn outcome_agrees(p: Primitives, s: State, c: Connection, o: crate::connection::post_handshake_spec::Out,
    s2: State, t: crate::transcription::connection::Receive, failed: bool) -> bool
{
    match o.end {
        End::Fail(a) => {
            &&& s2 == crate::connection::post_handshake_spec::failed()
            &&& o.delivered.len() == 0
            &&& o.wires == alert_wires(p, s, c, a)
            &&& failed
        },
        End::PeerAlert(d) => {
            &&& s2 == crate::connection::post_handshake_spec::failed()
            &&& o.wires.len() == 0
            &&& o.delivered.len() == 0
            &&& t == crate::transcription::connection::Receive::PeerError(d as nat)
        },
        _ => match t {
            crate::transcription::connection::Receive::Continue(progress) => {
                &&& o.delivered == progress.application_data
                &&& progress.records_to_send.len() == 0
                &&& o.wires == settle(p, s2, progress.connection).0
                &&& post_agrees(s2, settle(p, s2, progress.connection).1)
            },
            _ => false,
        },
    }
}

/// The crate's step on one whole record `b` and the transcription's
/// `receive_stream` of it agree: the crate consumes the record, and
/// [`outcome_agrees`] with [`fail_agrees`] for a failure.
pub open spec fn record_agrees(p: Primitives, f: crate::traffic::spec::Cipher, s: State, c: Connection, b: Seq<u8>,
    r: (crate::connection::post_handshake_spec::Out, State, nat), t: crate::transcription::connection::Receive) -> bool
{
    &&& r.2 == b.len()
    &&& outcome_agrees(p, s, c, r.0, r.1, t, match r.0.end {
        End::Fail(a) => fail_agrees(f, s, b, t, a),
        _ => true,
    })
}

/// §5.3: reading a record moves both read sequence numbers on.
pub proof fn lemma_advance(rx: crate::traffic::spec::State, tr: crate::transcription::record::TrafficState)
    requires super::record::epoch_agrees(rx, tr), rx.next is Some,
    ensures
        super::record::epoch_agrees(crate::traffic::spec::advance(rx),
            crate::transcription::record::TrafficState { sequence_number: tr.sequence_number + 1, ..tr }),
        crate::traffic::spec::advance(rx).failed == rx.failed,
{
}

/// §5, §5.1, §5.2: the header of one whole record, read by the crate's
/// protected framer and by the transcription's `receive_record` in
/// CONNECTED. A TLSCiphertext goes on to `receive_ciphertext`; every other
/// record is refused on both sides, with the same alert or as
/// [`two_faults`].
pub proof fn lemma_frame(p: Primitives, c: Connection, b: Seq<u8>)
    requires
        super::bootstrap::whole_record(b),
        c.receive is Protected,
        c.handshake.state == ClientState::Connected,
        !c.read_closed,
    ensures ({
        let t = super::bootstrap::one_record(p, c, b);
        match crate::spec::read_record(b, true) {
            crate::spec::Read::Fail(k) => t is Abort
                && (crate::transcription::alerts::required_alert(t->Abort_0) == crate::spec::alert_of(k) as nat
                    || two_faults(b)),
            crate::spec::Read::Done(crate::spec::Frame::Protected(h, e), rest) => {
                &&& b[0] == crate::spec::CT_APPLICATION_DATA
                &&& rest.len() == 0
                &&& super::record::is_protected_record(b)
                &&& t == crate::transcription::connection::receive_ciphertext(p, c, c.receive->Protected_0,
                    crate::transcription::record::read_record_header(b)->Some_0.legacy_record_version,
                    b.subrange(5, b.len() as int).take(
                        crate::transcription::record::read_record_header(b)->Some_0.length as int))
            },
            crate::spec::Read::Done(_, _) => t is Abort
                && crate::transcription::alerts::required_alert(t->Abort_0) == 10,
            crate::spec::Read::NeedMore => false,
        }
    }),
{
    super::bootstrap::lemma_header(b);
    let len = super::bootstrap::length(b);
    assert(b.subrange(5, b.len() as int).take(len as int) =~= super::bootstrap::fragment(b));
    assert(b.subrange(5, (5 + len) as int) =~= super::bootstrap::fragment(b));
}

/// §5.4: what the crate's inner plaintext check lets through.
pub proof fn lemma_inner_ok(x: Seq<u8>)
    requires crate::spec::open_inner_plaintext(x) is Ok,
    ensures ({
        let r = crate::spec::open_inner_plaintext(x)->Ok_0;
        &&& r.ctype == 21 || r.ctype == 22 || r.ctype == 23
        &&& r.fragment.len() <= crate::spec::MAX_PLAINTEXT
        &&& r.ctype != 23 ==> r.fragment.len() > 0
    }),
{
}

/// §5.1, §6, §6.1: an alert record's content in CONNECTED.
pub proof fn lemma_alert_content(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, y: Connection, content: Seq<u8>)
    requires
        hypotheses(c, f, p),
        post_agrees(s, y),
        crate::connection::post_handshake_spec::can_read(s),
        content.len() > 0,
    ensures ({
        let (o, s2) = crate::connection::post_handshake_spec::record(c, f, s, 21, content);
        let t = crate::transcription::connection::receive_protected_content(p, y, 21, content);
        outcome_agrees(p, s, y, o, s2, t,
            t is Abort && crate::transcription::alerts::required_alert(t->Abort_0) == o.end->Fail_0 as nat)
    }),
{
    assert(Connection { handshake_fragments: s.reassembly.buf, ..y } == y);
    if s.reassembly.buf.len() > 0 {
        lemma_fatal(f, p, s, y, 10);
    } else if content.len() != 2 {
        lemma_fatal(f, p, s, y, 50);
    } else {
        let d = content[1];
        assert(State { reassembly: s.reassembly, ..s } == s);
        if d == 0 {
            let y2 = Connection { read_closed: true, ..y };
            let (o, s2) = crate::connection::post_handshake_spec::peer_closed(s);
            assert(post_agrees(s2, y2));
            assert(o.delivered =~= Seq::<u8>::empty());
        } else if d == 90 {
            assert(Seq::<u8>::empty() =~= Seq::<u8>::empty());
        }
    }
}

/// §5.1, §5.4, §4.6: the content of an authenticated record in CONNECTED:
/// the crate's `record` against the transcription's
/// `receive_protected_content`, for every type and content the crate's
/// inner-plaintext check lets through.
pub proof fn lemma_content(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, y: Connection, typ: u8, content: Seq<u8>)
    requires
        hypotheses(c, f, p),
        post_agrees(s, y),
        crate::connection::post_handshake_spec::can_read(s),
        typ == 21 || typ == 22 || typ == 23,
        content.len() <= crate::spec::MAX_PLAINTEXT,
        typ != 23 ==> content.len() > 0,
    ensures ({
        let (o, s2) = crate::connection::post_handshake_spec::record(c, f, s, typ, content);
        let t = crate::transcription::connection::receive_protected_content(p, y, typ as nat, content);
        outcome_agrees(p, s, y, o, s2, t, {
            ||| t is Abort && crate::transcription::alerts::required_alert(t->Abort_0) == o.end->Fail_0 as nat
            ||| o.end == End::Fail(crate::spec::INTERNAL_ERROR) && typ == crate::spec::CT_HANDSHAKE
                && crate::spec::extract_messages(s.reassembly.buf + content) is Err
        })
    }),
{
    assert(Connection { handshake_fragments: s.reassembly.buf, ..y } == y);
    assert(State { reassembly: s.reassembly, ..s } == s);
    if typ == 23 {
        if s.reassembly.buf.len() > 0 {
            lemma_fatal(f, p, s, y, 10);
        }
    } else if typ == 21 {
        lemma_alert_content(c, f, p, s, y, content);
    } else {
        let bf = s.reassembly.buf + content;
        super::bootstrap::lemma_extract(bf);
        match crate::spec::extract_messages(bf) {
            crate::spec::Res::Err(e) => {
                lemma_fatal(f, p, s, y, 80);
            },
            crate::spec::Res::Ok((ms, r)) => {
                let s3 = State { reassembly: crate::spec::Reasm { buf: r }, ..s };
                assert(Connection { handshake_fragments: s3.reassembly.buf, ..y }
                    == Connection { handshake_fragments: r, ..y });
                assert(agrees_but_buffer(s3, y));
                lemma_messages(c, f, p, s3, y, bf);
                let (o, s2) = crate::connection::post_handshake_spec::messages(c, f, s3, ms);
                match crate::transcription::connection::process_handshake_bytes(p, y, bf) {
                    crate::transcription::connection::Receive::Continue(progress) => {
                        assert(o.delivered =~= progress.application_data);
                    },
                    _ => {},
                }
            },
        }
    }
}

/// [`post_agrees`] with the read side open: the facts [`lemma_receive`]
/// uses.
pub proof fn lemma_receive_open_facts(s: State, conn: Connection)
    requires post_agrees(s, conn), crate::connection::post_handshake_spec::can_read(s),
    ensures
        agrees_but_buffer(s, conn),
        s.receiver is Some,
        conn.receive is Protected,
        super::record::epoch_agrees(s.receiver->Some_0, conn.receive->Protected_0),
        !s.receiver->Some_0.failed,
        conn.handshake.state == ClientState::Connected,
        !conn.read_closed,
{
    assert(Connection { handshake_fragments: s.reassembly.buf, ..conn } == conn);
}

/// After a record is read, the states with both read sequence numbers moved
/// on still agree.
pub proof fn lemma_post_agrees_read(s: State, conn: Connection, s1: State, after: Connection)
    requires
        post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_read(s),
        s1 == (State { receiver: s1.receiver, ..s }),
        after == (Connection { receive: after.receive, ..conn }),
        s1.receiver is Some,
        after.receive is Protected,
        super::record::epoch_agrees(s1.receiver->Some_0, after.receive->Protected_0),
        !s1.receiver->Some_0.failed,
        after.receive->Protected_0.secret == conn.receive->Protected_0.secret,
    ensures
        post_agrees(s1, after),
{
}

/// §5, §5.1 to §5.4, §6, §4.6: one whole record received with the read side
/// open: the crate's `step` against the transcription's `receive_stream`.
#[verifier::rlimit(30)]
pub proof fn lemma_receive(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, conn: Connection, b: Seq<u8>)
    requires
        hypotheses(c, f, p),
        post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_read(s),
        super::bootstrap::whole_record(b),
    ensures
        record_agrees(p, f, s, conn, b,
            crate::connection::post_handshake_spec::step(c, f, s, crate::connection::post_handshake_spec::Input::Bytes(b)),
            crate::transcription::connection::receive_stream(p, conn, b).0),
{
    hide(crate::connection::post_handshake_spec::record);
    hide(crate::connection::post_handshake_spec::fatal);
    hide(crate::transcription::connection::receive_protected_content);
    hide(crate::transcription::connection::receive_stream);
    hide(post_agrees);
    hide(settle);
    lemma_receive_open_facts(s, conn);
    super::bootstrap::lemma_stream_one(p, conn, b);
    let rx = s.receiver->Some_0;
    let tr = conn.receive->Protected_0;
    lemma_seal(f, p, rx, tr);
    lemma_frame(p, conn, b);
    let t = super::bootstrap::one_record(p, conn, b);
    let open = crate::connection::post_handshake_spec::open_of(f, rx);
    let read = crate::traffic::spec::receive(open, rx, b);
    if rx.next is None {
        lemma_fatal(f, p, s, conn, 80);
        match crate::spec::read_record(b, true) {
            crate::spec::Read::Done(crate::spec::Frame::Protected(h, e), rest) => {
                assert(t == crate::transcription::connection::Receive::Abort(ClientError::SequenceNumberWrap));
            },
            _ => {},
        }
    } else {
        match crate::spec::read_record(b, true) {
            crate::spec::Read::Fail(k) => {
                lemma_alert_of(k);
                lemma_fatal(f, p, s, conn, crate::spec::alert_of(k));
            },
            crate::spec::Read::Done(crate::spec::Frame::Protected(h, e), rest) => {
                super::record::lemma_deprotect(p, open, rx, conn, tr, b);
                match read.1 {
                    crate::traffic::spec::Read::Fail(a) => {
                        let n = rx.next->Some_0;
                        match crate::spec::decrypt_record(open, rx.iv, n, h, e) {
                            crate::spec::Res::Err(k) => { lemma_alert_of(k); },
                            _ => {},
                        }
                        lemma_fatal(f, p, s, conn, a);
                    },
                    crate::traffic::spec::Read::Record(typ, content, used) => {
                        let n = rx.next->Some_0;
                        let x = open(crate::spec::per_record_nonce(rx.iv, n), h, e)->Some_0;
                        lemma_inner_ok(x);
                        lemma_advance(rx, tr);
                        let s1 = State { receiver: Some(read.0), ..s };
                        let after = Connection {
                            receive: Protection::Protected(crate::transcription::record::TrafficState {
                                sequence_number: tr.sequence_number + 1, ..tr }),
                            ..conn
                        };
                        lemma_post_agrees_read(s, conn, s1, after);
                        lemma_content(c, f, p, s1, after, typ, content);
                        assert forall|a: u8| #[trigger] alert_wires(p, s1, after, a) == alert_wires(p, s, conn, a) by {}
                    },
                    crate::traffic::spec::Read::NeedMore => {},
                }
            },
            crate::spec::Read::Done(_, _) => {
                lemma_fatal(f, p, s, conn, 10);
            },
            crate::spec::Read::NeedMore => {},
        }
    }
}

/// The read side has ended (§6.1: "Any data received after a closure alert
/// has been received MUST be ignored"): both sides ignore a whole record.
pub proof fn lemma_receive_closed(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: State, conn: Connection, b: Seq<u8>)
    requires
        post_agrees(s, conn),
        !crate::connection::post_handshake_spec::can_read(s),
        super::bootstrap::whole_record(b),
    ensures
        record_agrees(p, f, s, conn, b,
            crate::connection::post_handshake_spec::step(c, f, s, crate::connection::post_handshake_spec::Input::Bytes(b)),
            crate::transcription::connection::receive_stream(p, conn, b).0),
{
    super::bootstrap::lemma_header(b);
    let rest = b.subrange((5 + super::bootstrap::length(b)) as int, b.len() as int);
    assert(rest =~= Seq::<u8>::empty());
    let e = crate::transcription::connection::Progress { connection: conn, application_data: seq![], records_to_send: seq![] };
    assert(crate::transcription::connection::receive_stream(p, conn, rest)
        == (crate::transcription::connection::Receive::Continue(e), rest));
    assert(Seq::<u8>::empty() + Seq::<u8>::empty() =~= Seq::<u8>::empty());
    assert(Seq::<Seq<u8>>::empty() + Seq::<Seq<u8>>::empty() =~= Seq::<Seq<u8>>::empty());
}

} // verus!