//! Facts proven about [`super::post_handshake_spec`]: what the transducer
//! can and cannot do, for any key schedule and any AEAD. RFC 8446 §4.6, §5.3,
//! §6.1 and §7.2.
//!
//! - **Delivery.** Plaintext is delivered only from a record that opened and
//!   whose inner type is `application_data` ([`lemma_delivered_is_application_data`]);
//!   a record that failed to open, or was incomplete, delivers nothing
//!   ([`lemma_failed_open_delivers_nothing`]).
//! - **Ending.** A step that ends the connection leaves a connection that is
//!   not open ([`lemma_step_end_ends_connection`]), and a connection that is
//!   not open delivers and sends nothing for any later input
//!   ([`lemma_terminal_silent`]). One step at a time, that is "after
//!   `close_notify` or `Fail` nothing more is delivered".
//! - **Sends.** Every record the transducer sends is the encryption of a
//!   message it chose, under the next sequence number of the send epoch:
//!   [`lemma_key_update_wire`], [`lemma_application_wire`],
//!   [`lemma_close_notify_wire`] and [`lemma_fatal_wire`].
//! - **Sequence numbers.** A key update replaces the epoch of its direction
//!   by a fresh one at sequence number 0, from the next traffic secret
//!   ([`lemma_receive_key_update_resets`], [`lemma_send_key_update_resets`]);
//!   an application data record leaves both secrets and the send epoch alone
//!   ([`lemma_application_data_leaves_send_keys`]); on the last sequence
//!   number a data record is preceded by the KeyUpdate that uses it and the
//!   data goes out at sequence number 0 ([`lemma_last_sequence_number_rekeys`]).
//!
//! The invariant [`super::post_handshake_spec::wf`] is preserved by the
//! executable code (its contract says so); no lemma here restates that for the
//! spec.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// An ended connection holds nothing: the states `failed()` and `closed()`
/// satisfy the invariant.
pub proof fn lemma_failed_and_closed_wf()
    ensures
        super::post_handshake_spec::wf(super::post_handshake_spec::failed()),
        super::post_handshake_spec::wf(super::post_handshake_spec::closed()),
{}

/// §6.1: "Any data received after a closure alert has been received MUST be
/// ignored". Once the connection is not open, bytes are consumed and ignored
/// and the transport closing changes nothing: no record sent, nothing
/// delivered, no end, the same state.
pub proof fn lemma_terminal_silent(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: super::post_handshake_spec::State, wire: Seq<u8>)
    requires s.phase != super::post_handshake_spec::Phase::Open,
    ensures
        super::post_handshake_spec::step(c, f, s, super::post_handshake_spec::Input::Bytes(wire)).0
            == super::post_handshake_spec::quiet(),
        super::post_handshake_spec::step(c, f, s, super::post_handshake_spec::Input::Bytes(wire)).1 == s,
        super::post_handshake_spec::step(c, f, s, super::post_handshake_spec::Input::Bytes(wire)).2
            == wire.len(),
        super::post_handshake_spec::step(c, f, s, super::post_handshake_spec::Input::Closed).0
            == super::post_handshake_spec::quiet(),
        super::post_handshake_spec::step(c, f, s, super::post_handshake_spec::Input::Closed).1 == s,
        super::post_handshake_spec::step(c, f, s, super::post_handshake_spec::Input::Closed).2 == 0,
        super::post_handshake_spec::actions(super::post_handshake_spec::quiet()) == Seq::<super::post_handshake_spec::Action>::empty(),
{
    assert(super::post_handshake_spec::actions(super::post_handshake_spec::quiet())
        =~= Seq::<super::post_handshake_spec::Action>::empty());
}

/// No message of a record delivers plaintext.
pub proof fn lemma_message_no_delivery(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State, m: Seq<u8>, last: bool)
    ensures super::post_handshake_spec::message(c, f, s, m, last).0.delivered.len() == 0,
{}

/// No sequence of messages of a record delivers plaintext.
pub proof fn lemma_messages_no_delivery(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State, ms: Seq<Seq<u8>>)
    ensures super::post_handshake_spec::messages(c, f, s, ms).0.delivered.len() == 0,
    decreases ms.len(),
{
    if ms.len() > 0 {
        lemma_message_no_delivery(c, f, s, ms[0], ms.len() == 1);
        let r = super::post_handshake_spec::message(c, f, s, ms[0], ms.len() == 1);
        if r.1.phase == super::post_handshake_spec::Phase::Open {
            lemma_messages_no_delivery(c, f, r.1, ms.skip(1));
        }
    }
}

/// §5, §6: a record delivers plaintext only if its inner type is
/// `application_data`, and then exactly its content.
pub proof fn lemma_record_delivery(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: super::post_handshake_spec::State, typ: u8, content: Seq<u8>)
    ensures
        super::post_handshake_spec::record(c, f, s, typ, content).0.delivered.len() > 0
            ==> typ == crate::spec::CT_APPLICATION_DATA
                && super::post_handshake_spec::record(c, f, s, typ, content).0.delivered == content,
{
    match crate::spec::feed_record(s.reassembly, crate::spec::Record { ctype: typ, fragment: content }) {
        crate::spec::Res::Ok((crate::spec::Event::Messages(ms), r)) => {
            lemma_messages_no_delivery(c, f, super::post_handshake_spec::State { reassembly: r, ..s }, ms);
        },
        _ => {},
    }
}

/// No `Deliver` from a record that failed to open: if the receive epoch's
/// decryption of `wire` is not a record (it is incomplete, or it fails),
/// the step delivers nothing.
pub proof fn lemma_failed_open_delivers_nothing(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State, wire: Seq<u8>,
    rx: crate::traffic::spec::State)
    requires
        s.phase == super::post_handshake_spec::Phase::Open,
        s.receiver == Some(rx),
        !(crate::traffic::spec::receive(super::post_handshake_spec::open_of(f, rx), rx, wire).1
            is Record),
    ensures
        super::post_handshake_spec::step(c, f, s, super::post_handshake_spec::Input::Bytes(wire))
            .0.delivered.len() == 0,
{}

/// Plaintext is delivered only from a record that opened with inner type
/// `application_data`, and what is delivered is that record's content.
pub proof fn lemma_delivered_is_application_data(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State, wire: Seq<u8>,
    rx: crate::traffic::spec::State)
    requires
        s.phase == super::post_handshake_spec::Phase::Open,
        s.receiver == Some(rx),
        super::post_handshake_spec::step(c, f, s, super::post_handshake_spec::Input::Bytes(wire))
            .0.delivered.len() > 0,
    ensures
        match crate::traffic::spec::receive(super::post_handshake_spec::open_of(f, rx), rx, wire).1 {
            crate::traffic::spec::Read::Record(typ, content, _) => typ == crate::spec::CT_APPLICATION_DATA
                && super::post_handshake_spec::step(c, f, s,
                    super::post_handshake_spec::Input::Bytes(wire)).0.delivered == content,
            _ => false,
        },
{
    match crate::traffic::spec::receive(super::post_handshake_spec::open_of(f, rx), rx, wire) {
        (rx2, crate::traffic::spec::Read::Record(typ, content, used)) => {
            lemma_record_delivery(c, f,
                super::post_handshake_spec::State { receiver: Some(rx2), ..s }, typ, content);
        },
        _ => {},
    }
}

/// A fatal error ends the connection.
pub proof fn lemma_fatal_ends(f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State,
    alert: u8)
    ensures
        super::post_handshake_spec::fatal(f, s, alert).1 == super::post_handshake_spec::failed(),
        super::post_handshake_spec::fatal(f, s, alert).0.end
            == super::post_handshake_spec::End::Fail(alert),
{}

/// A key update that ends the connection leaves a connection that is not open.
pub proof fn lemma_send_key_update_end(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: super::post_handshake_spec::State, request: u8)
    ensures
        super::post_handshake_spec::send_key_update(c, f, s, request).0.end
            != super::post_handshake_spec::End::Continue
            ==> super::post_handshake_spec::send_key_update(c, f, s, request).1.phase
                != super::post_handshake_spec::Phase::Open,
{}

/// A message that ends the connection leaves a connection that is not open.
pub proof fn lemma_message_end(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: super::post_handshake_spec::State, m: Seq<u8>, last: bool)
    ensures
        super::post_handshake_spec::message(c, f, s, m, last).0.end
            != super::post_handshake_spec::End::Continue
            ==> super::post_handshake_spec::message(c, f, s, m, last).1.phase
                != super::post_handshake_spec::Phase::Open,
{
    if m.len() > 0 && (m[0] == crate::spec::HS_KEY_UPDATE) {
        let t = crate::spec::parse_handshake(m, crate::schedule::spec::HASH_LEN as nat);
        match t {
            crate::spec::Res::Ok(crate::spec::HsMsg::KeyUpdate(r)) => {
                lemma_send_key_update_end(c, f, s, crate::spec::UPDATE_NOT_REQUESTED);
                if let Ok(s1) = super::post_handshake_spec::rotated_receiver(c, s) {
                    lemma_send_key_update_end(c, f, s1, crate::spec::UPDATE_NOT_REQUESTED);
                }
            },
            _ => {},
        }
    }
}

/// A sequence of messages that ends the connection leaves a connection that
/// is not open.
pub proof fn lemma_messages_end(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: super::post_handshake_spec::State, ms: Seq<Seq<u8>>)
    ensures
        super::post_handshake_spec::messages(c, f, s, ms).0.end
            != super::post_handshake_spec::End::Continue
            ==> super::post_handshake_spec::messages(c, f, s, ms).1.phase
                != super::post_handshake_spec::Phase::Open,
    decreases ms.len(),
{
    if ms.len() > 0 {
        lemma_message_end(c, f, s, ms[0], ms.len() == 1);
        let r = super::post_handshake_spec::message(c, f, s, ms[0], ms.len() == 1);
        if r.1.phase == super::post_handshake_spec::Phase::Open {
            lemma_messages_end(c, f, r.1, ms.skip(1));
        }
    }
}

/// A record that ends the connection leaves a connection that is not open.
pub proof fn lemma_record_end(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: super::post_handshake_spec::State, typ: u8, content: Seq<u8>)
    ensures
        super::post_handshake_spec::record(c, f, s, typ, content).0.end
            != super::post_handshake_spec::End::Continue
            ==> super::post_handshake_spec::record(c, f, s, typ, content).1.phase
                != super::post_handshake_spec::Phase::Open,
{
    match crate::spec::feed_record(s.reassembly, crate::spec::Record { ctype: typ, fragment: content }) {
        crate::spec::Res::Ok((crate::spec::Event::Messages(ms), r)) => {
            lemma_messages_end(c, f, super::post_handshake_spec::State { reassembly: r, ..s }, ms);
        },
        _ => {},
    }
}

/// A step that ends the connection (`Close` or `Fail`) leaves a connection
/// that is not open, so by [`lemma_terminal_silent`] nothing more happens.
pub proof fn lemma_step_end_ends_connection(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State,
    input: super::post_handshake_spec::Input)
    ensures
        super::post_handshake_spec::step(c, f, s, input).0.end != super::post_handshake_spec::End::Continue
            ==> super::post_handshake_spec::step(c, f, s, input).1.phase
                != super::post_handshake_spec::Phase::Open,
{
    if s.phase == super::post_handshake_spec::Phase::Open {
        match input {
            super::post_handshake_spec::Input::Bytes(wire) => {
                match s.receiver {
                    Some(rx) => {
                        match crate::traffic::spec::receive(super::post_handshake_spec::open_of(f, rx), rx, wire) {
                            (rx2, crate::traffic::spec::Read::Record(typ, content, used)) => {
                                lemma_record_end(c, f,
                                    super::post_handshake_spec::State { receiver: Some(rx2), ..s },
                                    typ, content);
                            },
                            _ => {},
                        }
                    },
                    None => {},
                }
            },
            super::post_handshake_spec::Input::Closed => {},
        }
    }
}

/// §5.2, §5.3, §6.2: the alert a fatal error sends is the encryption of the
/// fatal alert record under the send epoch's next sequence number.
pub proof fn lemma_fatal_wire(f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State,
    alert: u8, tx: crate::traffic::spec::State, n: u64)
    requires
        s.sender == Some(tx),
        tx.next == Some(n),
        !tx.failed,
    ensures
        super::post_handshake_spec::fatal(f, s, alert).0.wires.len() <= 1,
        super::post_handshake_spec::fatal(f, s, alert).0.wires.len() == 1
            ==> super::post_handshake_spec::fatal(f, s, alert).0.wires[0]
                == crate::spec::encrypt_record(super::post_handshake_spec::seal_of(f, tx), 16, tx.iv, n,
                    crate::spec::CT_ALERT,
                    crate::spec::write_alert(crate::spec::Alert {
                        level: crate::spec::LEVEL_FATAL,
                        description: alert,
                    }), 0),
{}

/// §4.6.3, §5.2, §5.3: in a connection that satisfies the invariant, the one
/// record `send_key_update` sends is the encryption of the KeyUpdate message
/// it chose, under the send epoch's next sequence number.
pub proof fn lemma_key_update_wire(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: super::post_handshake_spec::State, request: u8, tx: crate::traffic::spec::State, n: u64)
    requires
        super::post_handshake_spec::wf(s),
        s.phase == super::post_handshake_spec::Phase::Open,
        s.sender == Some(tx),
        tx.next == Some(n),
    ensures
        super::post_handshake_spec::send_key_update(c, f, s, request).0.wires
            == seq![crate::spec::encrypt_record(super::post_handshake_spec::seal_of(f, tx), 16, tx.iv, n,
                crate::spec::CT_HANDSHAKE,
                crate::spec::write_handshake(crate::spec::HS_KEY_UPDATE, crate::spec::write_key_update(request)),
                0)],
{
    crate::lemmas_pl::lemma_be_bytes_len(1, 3);
}

/// §5, §5.2, §5.3: in a connection that satisfies the invariant, away from
/// the last sequence number, the one record `send_application` sends for at
/// most 2^14 bytes of data is the encryption of that data as `application_data`,
/// under the send epoch's next sequence number, and the epoch advances once.
pub proof fn lemma_application_wire(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: super::post_handshake_spec::State, data: Seq<u8>, tx: crate::traffic::spec::State, n: u64)
    requires
        super::post_handshake_spec::wf(s),
        s.phase == super::post_handshake_spec::Phase::Open,
        s.sender == Some(tx),
        tx.next == Some(n),
        n != u64::MAX,
        data.len() <= crate::spec::MAX_PLAINTEXT,
    ensures
        super::post_handshake_spec::send_application(c, f, s, data).0.wires
            == seq![crate::spec::encrypt_record(super::post_handshake_spec::seal_of(f, tx), 16, tx.iv, n,
                crate::spec::CT_APPLICATION_DATA, data, 0)],
        super::post_handshake_spec::send_application(c, f, s, data).1.sender
            == Some(crate::traffic::spec::advance(tx)),
{}

/// §6.1: the close_notify the transducer sends is the encryption of the
/// warning-level `close_notify` alert under the send epoch's next sequence
/// number.
pub proof fn lemma_close_notify_wire(f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State,
    tx: crate::traffic::spec::State, n: u64)
    requires
        super::post_handshake_spec::wf(s),
        s.phase == super::post_handshake_spec::Phase::Open,
        s.sender == Some(tx),
        tx.next == Some(n),
    ensures
        super::post_handshake_spec::close(f, s).0.wires
            == seq![crate::spec::encrypt_record(super::post_handshake_spec::seal_of(f, tx), 16, tx.iv, n,
                crate::spec::CT_ALERT,
                crate::spec::write_alert(crate::spec::Alert {
                    level: crate::spec::LEVEL_WARNING,
                    description: crate::spec::CLOSE_NOTIFY,
                }), 0)],
        super::post_handshake_spec::close(f, s).0.end == super::post_handshake_spec::End::Close,
        super::post_handshake_spec::close(f, s).1 == super::post_handshake_spec::closed(),
{}

/// §7.2, §7.3: sending a KeyUpdate replaces the send epoch by one derived
/// from the next client traffic secret, at sequence number 0, and leaves the
/// receive epoch and the server secret alone.
pub proof fn lemma_send_key_update_resets(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State, request: u8)
    requires
        super::post_handshake_spec::wf(s),
        s.phase == super::post_handshake_spec::Phase::Open,
        super::post_handshake_spec::send_key_update(c, f, s, request).0.end
            == super::post_handshake_spec::End::Continue,
    ensures ({
        let r = super::post_handshake_spec::send_key_update(c, f, s, request);
        r.1.client_secret == crate::schedule::spec::next_traffic_secret(c, s.client_secret)
            && r.1.sender == Some(crate::traffic::spec::start(c, r.1.client_secret).unwrap())
            && (match r.1.sender { Some(tx) => tx.next == Some(0u64), None => false })
            && r.1.receiver == s.receiver
            && r.1.server_secret == s.server_secret
            && r.1.reassembly == s.reassembly
    }),
{}

/// §7.2, §7.3: receiving a valid KeyUpdate at the end of a record, at a
/// message boundary, replaces the receive epoch by one derived from the
/// next server traffic secret, at sequence number 0; without
/// `update_requested` nothing else changes.
pub proof fn lemma_receive_key_update_resets(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State, request: u8)
    requires
        super::post_handshake_spec::wf(s),
        s.phase == super::post_handshake_spec::Phase::Open,
        crate::spec::at_message_boundary(s.reassembly),
        super::post_handshake_spec::rotated_receiver(c, s) is Ok,
    ensures ({
        let s1 = super::post_handshake_spec::rotated_receiver(c, s).unwrap();
        s1.server_secret == crate::schedule::spec::next_traffic_secret(c, s.server_secret)
            && (match s1.receiver { Some(rx) => rx.next == Some(0u64) && !rx.failed, None => false })
            && s1.sender == s.sender
            && s1.client_secret == s.client_secret
            && (request != crate::spec::UPDATE_REQUESTED
                ==> super::post_handshake_spec::key_update_received(c, f, s, request, true)
                    == (super::post_handshake_spec::quiet(), s1))
    }),
{}

/// §5.3, §7.2: an application data record leaves the send epoch and both
/// secrets alone and advances only the receive epoch's counter; nothing is
/// rekeyed by it.
pub proof fn lemma_application_data_leaves_send_keys(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State, content: Seq<u8>)
    requires s.reassembly.buf.len() == 0,
    ensures ({
        let r = super::post_handshake_spec::record(c, f, s, crate::spec::CT_APPLICATION_DATA, content);
        r.1.sender == s.sender && r.1.receiver == s.receiver
            && r.1.client_secret == s.client_secret && r.1.server_secret == s.server_secret
            && r.0.delivered == content && r.1.phase == s.phase
    }),
{}

/// §5.3: on the last sequence number the send epoch may use, a data record
/// is preceded by KeyUpdate(`update_not_requested`), which uses that number
/// and starts a fresh epoch, and the data goes out under the fresh epoch at
/// sequence number 0, so the epoch's nonces are never reused and the counter
/// never wraps.
pub proof fn lemma_last_sequence_number_rekeys(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, s: super::post_handshake_spec::State, data: Seq<u8>,
    tx: crate::traffic::spec::State)
    requires
        super::post_handshake_spec::wf(s),
        s.phase == super::post_handshake_spec::Phase::Open,
        s.sender == Some(tx),
        tx.next == Some(u64::MAX),
        data.len() <= crate::spec::MAX_PLAINTEXT,
        super::post_handshake_spec::send_key_update(c, f, s, crate::spec::UPDATE_NOT_REQUESTED).0.end
            == super::post_handshake_spec::End::Continue,
    ensures ({
        let r = super::post_handshake_spec::send_application(c, f, s, data);
        r.0.wires.len() == 2
            && r.0.wires[0] == crate::spec::encrypt_record(super::post_handshake_spec::seal_of(f, tx), 16,
                tx.iv, u64::MAX, crate::spec::CT_HANDSHAKE,
                crate::spec::write_handshake(crate::spec::HS_KEY_UPDATE,
                    crate::spec::write_key_update(crate::spec::UPDATE_NOT_REQUESTED)), 0)
            && r.1.client_secret == crate::schedule::spec::next_traffic_secret(c, s.client_secret)
            && (match r.1.sender { Some(t2) => t2.next == Some(1u64), None => false })
            && super::post_handshake_spec::wf(r.1)
    }),
{
    crate::lemmas_pl::lemma_be_bytes_len(1, 3);
}
} // verus!
