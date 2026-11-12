//! RFC 8446 §4.6, §5, §6 and §7.2: the client after the handshake,
//! `connection/post_handshake_spec.rs`, against the clean-room
//! transcription's CONNECTED state (`state_machine::receive_post_handshake`,
//! `post_handshake.rs`) and the record layer of `connection.rs` around it
//! (`receive_stream`, `send_application_data`, `send_key_update`,
//! `close_write`, `updated_traffic`): [`theorem_post_handshake_equivalence`].

#[cfg(verus_only)]
use crate::connection::post_handshake_spec::{End, Phase, State};
#[cfg(verus_only)]
use crate::transcription::connection::{Connection, Protection, SendResult};
#[cfg(verus_only)]
use crate::transcription::primitives::Primitives;
#[cfg(verus_only)]
use crate::transcription::state_machine::ClientState;
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

} // verus!
