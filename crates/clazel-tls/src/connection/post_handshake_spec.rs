//! RFC 8446 §4.6, §5, §5.3, §6, §6.1, §7.2 and §7.3: the client after the
//! handshake, as a transducer. Source:
//! <https://www.rfc-editor.org/rfc/rfc8446#section-4.6> (an RFC is
//! immutable, so there is no commit to pin).
//!
//! `step(state, input) -> (output, state, consumed)` over inputs `Bytes` and
//! `Closed`, with the actions `Send`, `Deliver`, `Close` and `Fail` of
//! phase-3.md item 3.5e. It starts from the two application traffic secrets
//! that the handshake produced and owns everything after that: protected
//! records, application data, NewSessionTicket, KeyUpdate and alerts.
//!
//! Modelling choices:
//! 1. **One record per step.** `Bytes(wire)` is processed up to the end of
//!    its first complete record; `consumed` says how many bytes that was. The
//!    caller resubmits the rest. An incomplete record consumes nothing and
//!    changes nothing (the caller resubmits the prefix with more bytes), as
//!    `traffic::spec::receive` does. The transducer therefore owns no byte
//!    buffer; its only partial input is the handshake reassembly buffer of
//!    §5.1.
//! 2. **`Out` and `actions`.** A step's effects are in the order the RFC
//!    forces: the records it sends, then the plaintext it delivers (a record
//!    that delivers sends nothing, and one that sends delivers nothing), then
//!    the end of the connection. `Out` holds the three parts, so a lemma can
//!    speak of "the plaintext delivered" without quantifying over a sequence;
//!    [`actions`] is the sequence of actions `Send*`, `Deliver?`, `Close` or
//!    `Fail`. A `Send` carries a whole protected record, ready for the
//!    transport; the caller sends them in order.
//! 3. **A `Send` is final.** The transport is assumed to accept every
//!    `Send` in order, so a key update takes effect in the same step, right
//!    after the record that announces it, as §4.6.3 says ("update its
//!    sending keys" after sending). The dispatcher of `dispatcher_spec` waits
//!    for an acknowledgement of each record instead; this transducer does not.
//! 4. **Starting point.** The caller gives the client and server application
//!    traffic secrets (§7.1, `[sender]_application_traffic_secret_0`). Both
//!    directions start at sequence number 0 (§5.3). Joining this to the
//!    `dispatcher_*` machine, which holds those secrets, is not done here.
//! 5. **Fatal errors send an alert, if they can.** On an error that is the
//!    local side's decision (a record that does not open, a message that
//!    must not arrive), the output is `Send(protected fatal alert)` and then
//!    `Fail(description)`, as §6.2 requires ("MUST be sent with
//!    AlertLevel=fatal"); the alert is protected with the client's current
//!    key, since protected records are all there is after the handshake. An
//!    alert received from the peer is `Fail(description)` alone: §6.2 asks
//!    for no reply. An error raised while sending (a record that is too long)
//!    is `Fail` alone, because the sending epoch is what failed.
//! 6. **Alerts.** Each direction closes on its own (§6.1, which drops the
//!    earlier versions' immediate answer to a `close_notify`). The peer's
//!    `close_notify` ends the read side: the output ends in `PeerClosed` and
//!    the write side stays usable ([`Phase::ReadClosed`]). Our `close_notify`
//!    ends the write side and the read side stays usable
//!    ([`Phase::WriteClosed`]). When both have gone the output ends in
//!    `Close`. `user_canceled` is not an error alert (§6.1) and changes
//!    nothing. Every other alert is fatal, whatever its level; TLS 1.3 says
//!    the level "can safely be ignored" (§6). It is `PeerAlert`, so the
//!    caller can tell it from a failure of ours, and never answered. Data that arrives after the
//!    read side ended is ignored (§6.1: "Any data received after a closure
//!    alert has been received MUST be ignored"): it is consumed with no
//!    action. `Closed` (the transport ended) while the read side is open is
//!    a truncation, `Fail(internal_error)` with no alert, because nothing can
//!    be sent.
//! 7. **NewSessionTicket (§4.6.1) is parsed, then ignored.** It is read with
//!    the parser of `spec.rs` (so a malformed one is `decode_error` or
//!    `illegal_parameter`, as the parser gives) and has no further effect.
//!    There is no resumption in this phase and no PSK is derived, cached or
//!    offered.
//! 8. **Which handshake messages may arrive (§4.6).** Only NewSessionTicket
//!    and KeyUpdate. The type byte is looked at first: any other type,
//!    known or not (ClientHello, ServerHello, Certificate, CertificateRequest,
//!    Finished, EndOfEarlyData, ...), is `unexpected_message` without reading
//!    its body. This client never offers `post_handshake_auth`, so a
//!    CertificateRequest is such a message too.
//! 9. **KeyUpdate (§4.6.3, §7.2).** On receipt the server application traffic
//!    secret becomes `HKDF-Expand-Label(secret, "traffic upd", "",
//!    Hash.length)` and the read key, IV and sequence number are those of the
//!    new secret (§7.3), for the next record. A KeyUpdate must end its
//!    record and leave no unfinished handshake message: §5.1, "Handshake
//!    messages MUST NOT span key changes. Implementations MUST verify that
//!    all messages immediately preceding a key change align with a record
//!    boundary; if not, then they MUST terminate the connection with an
//!    "unexpected_message" alert". An invalid `request_update` is
//!    `illegal_parameter` (the parser's `InvalidEnum`). Several KeyUpdates in
//!    one connection are fine; each needs its own record.
//!    **The answer to `update_requested` is owed, not sent at once.** §4.6.3:
//!    "If the request_update field is set to "update_requested", then the
//!    receiver MUST send a KeyUpdate of its own with request_update set to
//!    "update_not_requested" prior to sending its next Application Data
//!    record. This mechanism allows either side to force an update to the
//!    entire connection, but causes an implementation which receives multiple
//!    KeyUpdates while it is silent to respond with a single update." The
//!    step that receives the request sends nothing; it sets
//!    [`State::key_update_owed`], a flag and not a count, so several requests
//!    before the next application data draw one answer. [`send_application`]
//!    sends the owed KeyUpdate(`update_not_requested`) under the current
//!    write key, clears the flag, moves the write secret, key, IV and
//!    sequence number on as for any KeyUpdate it sends, and then sends the
//!    data under the new key. Nothing else sends or clears the owed answer: a
//!    client-initiated KeyUpdate ([`update_keys`]), our `close_notify` and a
//!    fatal alert go out under the current write key with the answer still
//!    owed (the RFC asks for it only before Application Data, and after
//!    `close_notify` there is none, §6.1). This is the mechanism the
//!    clean-room transcription models (`transcription::connection`:
//!    `key_update_owed`, `send_application_data`).
//! 10. **Sequence numbers (§5.3) close or rekey; they never wrap.** The
//!     receive epoch of `traffic::spec` becomes exhausted after using
//!     sequence number 2^64 - 1, and its next record is `Fail(internal_error)`:
//!     the server cannot send another record under that key, so this side
//!     *closes*. The send side *rekeys*: a data record that would use the
//!     last sequence number is preceded by KeyUpdate(`update_not_requested`),
//!     which uses that number and moves the write keys on, and the data goes
//!     out under the new key at sequence number 0 ([`needs_rekey`]). So the
//!     send epoch is never exhausted while the connection is open ([`wf`]).
//!     When an answer is owed (item 9) as well, that one KeyUpdate is both
//!     the answer and the rekey, as in the transcription's
//!     `send_application_data` (its `must_rekey` is either condition).
//! 11. **Local operations.** [`send_application`] sends one record of at most
//!     2^14 bytes (a longer one is `Fail(record_overflow)`: the caller
//!     fragments, as `traffic::exec` says); [`update_keys`] is the
//!     client-initiated KeyUpdate, with or without `update_requested`;
//!     [`close`] sends `close_notify` and ends the write side; the read side
//!     goes on until the server's own `close_notify`, which avoids truncation
//!     (§6.1). Each does nothing once the write side has ended. An answer
//!     owed under item 9 goes out only before application data.
//! 12. **No padding, no early data, no client authentication.** Records are
//!     sent with zero padding. 0-RTT, `EndOfEarlyData` and post-handshake
//!     client authentication are out of scope (an `EndOfEarlyData` or
//!     `Certificate` after the handshake is `unexpected_message`, item 8).
//! 13. **The AEAD is a parameter.** As in `traffic::spec`: a key-explicit
//!     `traffic::spec::Cipher` with the key taken from the epoch in use. The
//!     key schedule's `schedule::spec::Crypto` is a parameter too. Nothing
//!     about either is assumed here.
//! 14. RFC prose and equations have no numbered algorithm steps; the
//!     comments cite the section instead.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {

/// Whether the connection is live.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    /// Application traffic keys are installed in both directions.
    Open,
    /// Our `close_notify` went out: the send keys are dropped and the server
    /// can still be read.
    WriteClosed,
    /// The server's `close_notify` came in: the receive keys are dropped and
    /// the client can still write.
    ReadClosed,
    /// Both directions closed; every key and partial input is dropped.
    Closed,
    /// Fatal error; every key and partial input is dropped.
    Failed,
}

/// What the transducer is given.
pub enum Input {
    /// Bytes of the server's stream, starting at a record boundary.
    Bytes(Seq<u8>),
    /// The transport closed.
    Closed,
}

/// One effect, in the order it happens.
pub enum Action {
    /// A whole protected record to put on the wire.
    Send(Seq<u8>),
    /// Plaintext application data from the server, in order.
    Deliver(Seq<u8>),
    /// The server's `close_notify`: end of data; the write side goes on.
    PeerClosed,
    /// Both directions ended in order (`close_notify`).
    Close,
    /// The connection ended with this alert description.
    Fail(u8),
    /// §6: the peer's fatal alert ended the connection; it is not answered.
    PeerAlert(u8),
}

/// How a step ends the connection, if it does.
pub enum End {
    /// The connection goes on.
    Continue,
    /// The server's `close_notify`; the write side goes on.
    PeerClosed,
    /// Both directions ended with `close_notify`.
    Close,
    /// Fatal, with this alert description.
    Fail(u8),
    /// The peer's fatal alert, with its description.
    PeerAlert(u8),
}

/// A step's effects: records sent, in order; plaintext delivered (empty:
/// none); and how the connection ended, if it did.
pub struct Out {
    /// Protected records to send, in order.
    pub wires: Seq<Seq<u8>>,
    /// Plaintext to deliver; empty means no `Deliver` action.
    pub delivered: Seq<u8>,
    /// Whether the connection ended.
    pub end: End,
}

/// One `Send` per record, in order.
pub open spec fn sends(wires: Seq<Seq<u8>>) -> Seq<Action> {
    Seq::new(wires.len(), |i: int| Action::Send(wires[i]))
}

/// The effects of [`Out`] as the sequence of actions: every `Send`, then the
/// `Deliver` if there is plaintext, then `PeerClosed`, `Close`, `Fail` or
/// `PeerAlert`.
pub open spec fn actions(o: Out) -> Seq<Action> {
    sends(o.wires)
        + (if o.delivered.len() > 0 { seq![Action::Deliver(o.delivered)] } else { seq![] })
        + (match o.end {
            End::Continue => seq![],
            End::PeerClosed => seq![Action::PeerClosed],
            End::Close => seq![Action::Close],
            End::Fail(a) => seq![Action::Fail(a)],
            End::PeerAlert(a) => seq![Action::PeerAlert(a)],
        })
}

/// Connection-owned protocol state after the handshake.
pub struct State {
    /// Whether the connection is live.
    pub phase: Phase,
    /// Client application send epoch; absent once the write side ended.
    pub sender: Option<crate::traffic::spec::State>,
    /// Server application receive epoch; absent once the read side ended.
    pub receiver: Option<crate::traffic::spec::State>,
    /// Current `client_application_traffic_secret_N`.
    pub client_secret: Seq<u8>,
    /// Current `server_application_traffic_secret_N`.
    pub server_secret: Seq<u8>,
    /// Bytes of one unfinished handshake message (§5.1).
    pub reassembly: crate::spec::Reasm,
    /// §4.6.3: a KeyUpdate(`update_not_requested`) of ours is owed "prior to
    /// sending its next Application Data record" (item 9).
    pub key_update_owed: bool,
}

/// The state of a connection that has not ended.
pub open spec fn is_open(s: State) -> bool { s.phase == Phase::Open }

/// The server can still be read.
pub open spec fn can_read(s: State) -> bool { s.phase == Phase::Open || s.phase == Phase::WriteClosed }

/// The client can still write.
pub open spec fn can_write(s: State) -> bool { s.phase == Phase::Open || s.phase == Phase::ReadClosed }

/// Lifecycle invariant. Open: both epochs are installed, well formed and not
/// failed; the send epoch has a next sequence number (item 10: it is never
/// exhausted); both secrets are `Hash.length` bytes; the reassembly buffer is
/// within its bound. A closed direction holds no epoch or secret, and the rest
/// is as in `Open`. Ended: nothing is retained, and no answer is owed.
pub open spec fn wf(s: State) -> bool {
    match s.phase {
        Phase::Open => match (s.sender, s.receiver) {
            (Some(tx), Some(rx)) => crate::traffic::spec::wf(tx) && crate::traffic::spec::wf(rx) && !tx.failed && !rx.failed
                && tx.next is Some && s.client_secret.len() == crate::schedule::spec::HASH_LEN
                && s.server_secret.len() == crate::schedule::spec::HASH_LEN
                && s.reassembly.buf.len() < crate::spec::HANDSHAKE_HEADER + crate::spec::MAX_HANDSHAKE_BODY,
            _ => false,
        },
        Phase::WriteClosed => match (s.sender, s.receiver) {
            (None, Some(rx)) => crate::traffic::spec::wf(rx) && !rx.failed
                && s.client_secret.len() == 0
                && s.server_secret.len() == crate::schedule::spec::HASH_LEN
                && s.reassembly.buf.len() < crate::spec::HANDSHAKE_HEADER + crate::spec::MAX_HANDSHAKE_BODY,
            _ => false,
        },
        Phase::ReadClosed => match (s.sender, s.receiver) {
            (Some(tx), None) => crate::traffic::spec::wf(tx) && !tx.failed && tx.next is Some
                && s.client_secret.len() == crate::schedule::spec::HASH_LEN
                && s.server_secret.len() == 0
                && s.reassembly.buf.len() == 0,
            _ => false,
        },
        Phase::Closed | Phase::Failed => s.sender is None && s.receiver is None
            && s.client_secret.len() == 0 && s.server_secret.len() == 0
            && s.reassembly.buf.len() == 0 && !s.key_update_owed,
    }
}

/// Nothing sent, delivered or ended.
pub open spec fn quiet() -> Out { Out { wires: seq![], delivered: seq![], end: End::Continue } }

/// One record sent, nothing else.
pub open spec fn sending(wire: Seq<u8>) -> Out {
    Out { wires: seq![wire], delivered: seq![], end: End::Continue }
}

/// The first output's records, then the second's; the second's end.
/// Used where the first delivers nothing.
pub open spec fn then(first: Out, second: Out) -> Out {
    Out { wires: first.wires + second.wires, delivered: second.delivered, end: second.end }
}

/// The state of a connection that failed: all keys and partial input dropped.
pub open spec fn failed() -> State {
    State {
        phase: Phase::Failed,
        sender: None,
        receiver: None,
        client_secret: seq![],
        server_secret: seq![],
        reassembly: crate::spec::reasm_new(),
        key_update_owed: false,
    }
}

/// The state of a connection that ended in order: all keys dropped.
pub open spec fn closed() -> State { State { phase: Phase::Closed, ..failed() } }

/// §6.1: the write side has ended. Both have once the read side has too.
pub open spec fn finish_write(s: State) -> (End, State) {
    if s.phase == Phase::ReadClosed {
        (End::Close, closed())
    } else {
        (End::Continue, State { phase: Phase::WriteClosed, sender: None, client_secret: seq![], ..s })
    }
}

/// §6.1: the server's `close_notify` ended the read side. Both have ended
/// once the write side has too.
pub open spec fn peer_closed(s: State) -> (Out, State) {
    if s.phase == Phase::WriteClosed {
        (Out { wires: seq![], delivered: seq![], end: End::Close }, closed())
    } else {
        (
            Out { wires: seq![], delivered: seq![], end: End::PeerClosed },
            State {
                phase: Phase::ReadClosed,
                receiver: None,
                server_secret: seq![],
                reassembly: crate::spec::reasm_new(),
                ..s
            },
        )
    }
}

/// §5.2: the key-explicit AEAD encryption of this epoch's key.
pub open spec fn seal_of(f: crate::traffic::spec::Cipher, ep: crate::traffic::spec::State)
    -> spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>
{
    |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| (f.seal)(ep.key, n, ad, p)
}

/// §5.2: the key-explicit AEAD decryption of this epoch's key.
pub open spec fn open_of(f: crate::traffic::spec::Cipher, ep: crate::traffic::spec::State)
    -> spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>
{
    |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| (f.open)(ep.key, n, ad, ct)
}

/// §5.2 and §5.3: protect `content` as a record of type `typ`, with no
/// padding, under the epoch's next sequence number.
pub open spec fn send_record(f: crate::traffic::spec::Cipher, ep: crate::traffic::spec::State, typ: u8, content: Seq<u8>)
    -> (crate::traffic::spec::State, Result<Seq<u8>, u8>)
{
    crate::traffic::spec::send(seal_of(f, ep), ep, typ, content, 0)
}

/// The connection ends with this alert and no record to send (item 5).
pub open spec fn die(alert: u8) -> (Out, State) {
    (Out { wires: seq![], delivered: seq![], end: End::Fail(alert) }, failed())
}

/// §6: the peer's fatal alert: not answered, and every key is dropped.
pub open spec fn peer_alert(description: u8) -> (Out, State) {
    (Out { wires: seq![], delivered: seq![], end: End::PeerAlert(description) }, failed())
}

/// §6.2: a fatal error of the local side. The alert is protected with the
/// client's current key and sent, then the connection fails (item 5).
pub open spec fn fatal(f: crate::traffic::spec::Cipher, s: State, alert: u8) -> (Out, State) {
    match s.sender {
        Some(tx) => {
            let a = crate::spec::Alert { level: crate::spec::LEVEL_FATAL, description: alert };
            match send_record(f, tx, crate::spec::CT_ALERT, crate::spec::write_alert(a)) {
                (_, Ok(wire)) => (
                    Out { wires: seq![wire], delivered: seq![], end: End::Fail(alert) },
                    failed(),
                ),
                (_, Err(_)) => die(alert),
            }
        },
        None => die(alert),
    }
}

/// §6.1: send `close_notify` and end the write side (item 6).
pub open spec fn close_connection(f: crate::traffic::spec::Cipher, s: State) -> (Out, State) {
    match s.sender {
        Some(tx) => {
            let a = crate::spec::Alert { level: crate::spec::LEVEL_WARNING, description: crate::spec::CLOSE_NOTIFY };
            match send_record(f, tx, crate::spec::CT_ALERT, crate::spec::write_alert(a)) {
                (_, Ok(wire)) => (
                    Out { wires: seq![wire], delivered: seq![], end: finish_write(s).0 },
                    finish_write(s).1,
                ),
                (_, Err(_)) => (Out { wires: seq![], delivered: seq![], end: finish_write(s).0 }, finish_write(s).1),
            }
        },
        None => (Out { wires: seq![], delivered: seq![], end: finish_write(s).0 }, finish_write(s).1),
    }
}

/// §7.2: the client write secret becomes the next generation, and §7.3 a
/// fresh key and IV with sequence number 0 are derived from it.
pub open spec fn rotated_sender(c: crate::schedule::spec::Crypto, s: State) -> Result<State, u8> {
    let next = crate::schedule::spec::next_traffic_secret(c, s.client_secret);
    match crate::traffic::spec::start(c, next) {
        Ok(ep) => Ok(State { sender: Some(ep), client_secret: next, ..s }),
        Err(a) => Err(a),
    }
}

/// §7.2: the server read secret becomes the next generation, and §7.3 a
/// fresh key and IV with sequence number 0 are derived from it.
pub open spec fn rotated_receiver(c: crate::schedule::spec::Crypto, s: State) -> Result<State, u8> {
    let next = crate::schedule::spec::next_traffic_secret(c, s.server_secret);
    match crate::traffic::spec::start(c, next) {
        Ok(ep) => Ok(State { receiver: Some(ep), server_secret: next, ..s }),
        Err(a) => Err(a),
    }
}

/// §4.6.3: send KeyUpdate(`request`) under the current client key, then
/// update the client write keys (item 9). Nothing if the write side ended.
pub open spec fn send_key_update(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, request: u8)
    -> (Out, State)
{
    if !can_write(s) {
        (quiet(), s)
    } else {
        match s.sender {
            None => die(crate::spec::INTERNAL_ERROR),
            Some(tx) => {
                let message = crate::spec::write_handshake(crate::spec::HS_KEY_UPDATE, crate::spec::write_key_update(request));
                match send_record(f, tx, crate::spec::CT_HANDSHAKE, message) {
                    (_, Err(a)) => die(a),
                    (_, Ok(wire)) => match rotated_sender(c, s) {
                        Ok(s2) => (sending(wire), s2),
                        Err(a) => (
                            Out { wires: seq![wire], delivered: seq![], end: End::Fail(a) },
                            failed(),
                        ),
                    },
                }
            },
        }
    }
}

/// §5.3: the send epoch is on its last sequence number, so another record
/// under it must be a rekey (item 10).
pub open spec fn needs_rekey(s: State) -> bool {
    match s.sender {
        Some(tx) => tx.next == Some(u64::MAX),
        None => false,
    }
}

/// Protect one application data record under the current client key.
pub open spec fn send_data_record(f: crate::traffic::spec::Cipher, s: State, data: Seq<u8>) -> (Out, State) {
    match s.sender {
        None => die(crate::spec::INTERNAL_ERROR),
        Some(tx) => match send_record(f, tx, crate::spec::CT_APPLICATION_DATA, data) {
            (_, Err(a)) => die(a),
            (tx2, Ok(wire)) => (sending(wire), State { sender: Some(tx2), ..s }),
        },
    }
}

/// §5, §5.3, §4.6.3: send one application data record. A
/// KeyUpdate(`update_not_requested`) goes first when one is owed (item 9) or
/// on the last sequence number (item 10); it is one KeyUpdate if both, and
/// nothing is owed after it.
pub open spec fn send_application(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, data: Seq<u8>)
    -> (Out, State)
{
    if !can_write(s) {
        (quiet(), s)
    } else if s.key_update_owed || needs_rekey(s) {
        match send_key_update(c, f, State { key_update_owed: false, ..s }, crate::spec::UPDATE_NOT_REQUESTED) {
            (o1, s1) => if can_write(s1) {
                match send_data_record(f, s1, data) {
                    (o2, s2) => (then(o1, o2), s2),
                }
            } else {
                (o1, s1)
            },
        }
    } else {
        send_data_record(f, s, data)
    }
}

/// §4.6.3: the client-initiated KeyUpdate, asking the server to update too
/// when `request_peer` is set. An owed answer stays owed (item 9).
pub open spec fn update_keys(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, request_peer: bool)
    -> (Out, State)
{
    send_key_update(c, f, s, if request_peer { crate::spec::UPDATE_REQUESTED } else { crate::spec::UPDATE_NOT_REQUESTED })
}

/// §6.1: the client-initiated close.
pub open spec fn close(f: crate::traffic::spec::Cipher, s: State) -> (Out, State) {
    if can_write(s) { close_connection(f, s) } else { (quiet(), s) }
}

/// §4.6.3 on receipt of KeyUpdate(`request`), a valid value: the message must
/// end its record and leave no unfinished message (§5.1). The read keys are
/// updated; with `update_requested` an answer is owed and nothing is sent:
/// the receiver "MUST send a KeyUpdate of its own ... prior to sending its
/// next Application Data record" (item 9). A request while one is owed
/// leaves one owed.
pub open spec fn key_update_received(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, request: u8,
    last: bool) -> (Out, State)
{
    if !last || !crate::spec::at_message_boundary(s.reassembly) {
        fatal(f, s, crate::spec::UNEXPECTED_MESSAGE)
    } else {
        match rotated_receiver(c, s) {
            Err(a) => fatal(f, s, a),
            Ok(s1) => if request == crate::spec::UPDATE_REQUESTED {
                (quiet(), State { key_update_owed: true, ..s1 })
            } else {
                (quiet(), s1)
            },
        }
    }
}

/// §4.6: one complete handshake message `m` (header and body) after the
/// handshake. Only NewSessionTicket and KeyUpdate are allowed (item 8);
/// `last` says it is the last complete message of its record.
pub open spec fn message(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, m: Seq<u8>, last: bool)
    -> (Out, State)
{
    if m.len() == 0 || !(m[0] == crate::spec::HS_NEW_SESSION_TICKET || m[0] == crate::spec::HS_KEY_UPDATE) {
        fatal(f, s, crate::spec::UNEXPECTED_MESSAGE)
    } else {
        match crate::spec::parse_handshake(m, crate::schedule::spec::HASH_LEN as nat) {
            crate::spec::Res::Err(k) => fatal(f, s, crate::spec::alert_of(k)),
            crate::spec::Res::Ok(crate::spec::HsMsg::KeyUpdate(r)) => key_update_received(c, f, s, r, last),
            // §4.6.1: parsed, then ignored (item 7). The type check above
            // leaves only NewSessionTicket here.
            crate::spec::Res::Ok(_) => (quiet(), s),
        }
    }
}

/// The complete messages of one record, in order; the first that ends the
/// connection ends the rest.
pub open spec fn messages(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, ms: Seq<Seq<u8>>)
    -> (Out, State)
    decreases ms.len(),
{
    if ms.len() == 0 {
        (quiet(), s)
    } else {
        match message(c, f, s, ms[0], ms.len() == 1) {
            (o1, s1) => if !can_read(s1) {
                (o1, s1)
            } else {
                match messages(c, f, s1, ms.skip(1)) {
                    (o2, s2) => (then(o1, o2), s2),
                }
            },
        }
    }
}

/// §5.1 and §6: what one authenticated record of type `typ` does, through
/// the reassembler of `spec.rs`. A record the reassembler refuses
/// (interleaving, a zero-length fragment, a change_cipher_spec, an
/// unexpected type) is fatal with the alert of its `ErrKind`.
pub open spec fn record(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, typ: u8, content: Seq<u8>)
    -> (Out, State)
{
    match crate::spec::feed_record(s.reassembly, crate::spec::Record { ctype: typ, fragment: content }) {
        crate::spec::Res::Err(k) => fatal(f, s, crate::spec::alert_of(k)),
        crate::spec::Res::Ok((crate::spec::Event::AppData(d), r)) => (
            Out { wires: seq![], delivered: d, end: End::Continue },
            State { reassembly: r, ..s },
        ),
        crate::spec::Res::Ok((crate::spec::Event::Alert(a), r)) => {
            if a.description == crate::spec::CLOSE_NOTIFY { peer_closed(s) }
            else if a.description == crate::spec::USER_CANCELED { (quiet(), State { reassembly: r, ..s }) }
            else { peer_alert(a.description) }
        },
        crate::spec::Res::Ok((crate::spec::Event::Messages(ms), r)) => {
            messages(c, f, State { reassembly: r, ..s }, ms)
        },
        crate::spec::Res::Ok((crate::spec::Event::Ignored, _)) => fatal(f, s, crate::spec::UNEXPECTED_MESSAGE),
    }
}

/// A step's result with the number of input bytes it consumed.
pub open spec fn consuming(r: (Out, State), n: nat) -> (Out, State, nat) { (r.0, r.1, n) }

/// §5.1, §5.2 and §5.3: authenticate and open the first record of `wire`
/// and act on it. An incomplete record changes nothing and consumes nothing.
pub open spec fn receive(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, wire: Seq<u8>)
    -> (Out, State, nat)
{
    match s.receiver {
        None => consuming(die(crate::spec::INTERNAL_ERROR), wire.len()),
        Some(rx) => match crate::traffic::spec::receive(open_of(f, rx), rx, wire) {
            (_, crate::traffic::spec::Read::NeedMore) => (quiet(), s, 0),
            (_, crate::traffic::spec::Read::Fail(a)) => consuming(fatal(f, s, a), wire.len()),
            (rx2, crate::traffic::spec::Read::Record(typ, content, used)) => {
                consuming(record(c, f, State { receiver: Some(rx2), ..s }, typ, content), used)
            },
        },
    }
}

/// The transducer: `step(state, input) -> (output, state, consumed)`.
/// After the read side ended, bytes are consumed and ignored (§6.1).
pub open spec fn step(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, s: State, input: Input) -> (Out, State, nat) {
    match input {
        Input::Bytes(wire) => {
            if can_read(s) { receive(c, f, s, wire) } else { (quiet(), s, wire.len()) }
        },
        Input::Closed => {
            if can_read(s) { consuming(die(crate::spec::INTERNAL_ERROR), 0) } else { (quiet(), s, 0) }
        },
    }
}

/// The state at the end of the handshake: both application epochs at
/// sequence number 0 for the supplied secrets (§7.1, §7.3).
pub open spec fn start(c: crate::schedule::spec::Crypto, client_secret: Seq<u8>, server_secret: Seq<u8>)
    -> Result<State, u8>
{
    match (crate::traffic::spec::start(c, client_secret), crate::traffic::spec::start(c, server_secret)) {
        (Ok(tx), Ok(rx)) => Ok(State {
            phase: Phase::Open,
            sender: Some(tx),
            receiver: Some(rx),
            client_secret,
            server_secret,
            reassembly: crate::spec::reasm_new(),
            key_update_owed: false,
        }),
        (Err(a), _) => Err(a),
        (_, Err(a)) => Err(a),
    }
}
} // verus!
