//! Concrete RFC 8446 §4.6, §5, §6.1 and §7.2 facts about
//! [`super::post_handshake_spec`], proven by evaluating the spec on literal
//! bytes. Each quotes the rule it shows; `mutations.json` breaks each rule in
//! turn and a certificate calls one of these lemmas on the broken spec.
//!
//! The fixtures are input-sensitive protocol stand-ins, not cryptography.
//! The key schedule is `traffic::examples::crypto` (a traffic secret of 11
//! gives key octets 11^116 and so on: the next secret differs from the
//! current one); the AEAD seals `p` to `p` followed by 16 zero octets, so a
//! sent record shows its inner plaintext: five header octets, the content,
//! the content type, the tag.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// The key schedule fixture shared with the record-epoch examples.
pub open spec fn crypto() -> crate::schedule::spec::Crypto { crate::traffic::examples::crypto() }

/// A key-explicit AEAD that appends a zero tag and opens nothing.
pub open spec fn cipher() -> crate::traffic::spec::Cipher {
    crate::traffic::spec::Cipher {
        seal: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| p + Seq::new(16, |i: int| 0u8),
        open: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| None,
    }
}

/// A client secret of eleven and a server secret of seven.
pub open spec fn ready() -> super::post_handshake_spec::State {
    super::post_handshake_spec::start(crypto(), Seq::new(32, |i: int| 11u8), Seq::new(32, |i: int| 7u8))
        .unwrap()
}

/// The same connection with its send epoch on the last sequence number.
pub open spec fn at_last_number() -> super::post_handshake_spec::State {
    super::post_handshake_spec::State {
        sender: Some(crate::traffic::spec::State { next: Some(u64::MAX), ..ready().sender.unwrap() }),
        ..ready()
    }
}

/// The same connection with its receive epoch exhausted.
pub open spec fn receiver_exhausted() -> super::post_handshake_spec::State {
    super::post_handshake_spec::State {
        receiver: Some(crate::traffic::spec::State { next: None, ..ready().receiver.unwrap() }),
        ..ready()
    }
}

/// The same connection part-way through a handshake message.
pub open spec fn mid_message() -> super::post_handshake_spec::State {
    super::post_handshake_spec::State { reassembly: crate::spec::Reasm { buf: seq![4u8] }, ..ready() }
}

/// §4.6.3: a KeyUpdate message with this `request_update`.
pub open spec fn ku(request: u8) -> Seq<u8> { seq![24u8, 0, 0, 1, request] }

/// §4.6.1: a NewSessionTicket with a one-byte ticket and no extensions.
pub open spec fn ticket() -> Seq<u8> { seq![4u8, 0, 0, 14, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 1, 9, 0, 0] }

/// One message of a record on the ready connection.
pub open spec fn msg(m: Seq<u8>, last: bool) -> (super::post_handshake_spec::Out, super::post_handshake_spec::State) {
    super::post_handshake_spec::message(crypto(), cipher(), ready(), m, last)
}

/// One decrypted record of type `typ` on the ready connection.
pub open spec fn rec(typ: u8, content: Seq<u8>) -> (super::post_handshake_spec::Out, super::post_handshake_spec::State) {
    super::post_handshake_spec::record(crypto(), cipher(), ready(), typ, content)
}

/// A KeyUpdate on the ready connection, at the end of its record or not.
pub open spec fn ku_rx(request: u8, last: bool, s: super::post_handshake_spec::State)
    -> (super::post_handshake_spec::Out, super::post_handshake_spec::State)
{
    super::post_handshake_spec::key_update_received(crypto(), cipher(), s, request, last)
}

/// §4.6.1: a NewSessionTicket is parsed and then ignored: no output, no
/// state change.
pub proof fn lemma_ticket_ignored()
    ensures
        msg(ticket(), true).0 == super::post_handshake_spec::quiet(),
        msg(ticket(), true).1 == ready(),
{
    assert(msg(ticket(), true).0 == super::post_handshake_spec::quiet()) by (compute_only);
    assert(msg(ticket(), true).1 == ready()) by (compute_only);
}

/// §4.6: "If the server ... sends any other message after the handshake" the
/// type is wrong: any handshake message but NewSessionTicket and KeyUpdate is
/// `unexpected_message` (10), before its body is read: ClientHello,
/// EndOfEarlyData, Certificate, an unknown type, and an empty message.
pub proof fn lemma_other_handshake_messages_unexpected()
    ensures
        msg(seq![1u8, 0, 0, 0], true).0.end == super::post_handshake_spec::End::Fail(10u8),
        msg(seq![5u8, 0, 0, 0], true).0.end == super::post_handshake_spec::End::Fail(10u8),
        msg(seq![11u8, 0, 0, 0], true).0.end == super::post_handshake_spec::End::Fail(10u8),
        msg(seq![99u8, 0, 0, 0], true).0.end == super::post_handshake_spec::End::Fail(10u8),
        msg(seq![], true).0.end == super::post_handshake_spec::End::Fail(10u8),
{
    assert(msg(seq![1u8, 0, 0, 0], true).0.end == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
    assert(msg(seq![5u8, 0, 0, 0], true).0.end == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
    assert(msg(seq![11u8, 0, 0, 0], true).0.end == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
    assert(msg(seq![99u8, 0, 0, 0], true).0.end == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
    assert(msg(seq![], true).0.end == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
}

/// §4.6.3: "If the request_update field is set to any other value than the
/// defined ones, the receiver MUST terminate the connection with an
/// "illegal_parameter" alert" (47), and send it protected.
pub proof fn lemma_invalid_request_update()
    ensures
        msg(ku(2), true).0.end == super::post_handshake_spec::End::Fail(47u8),
        msg(ku(2), true).0.wires.len() == 1,
        msg(ku(255), true).0.end == super::post_handshake_spec::End::Fail(47u8),
{
    assert(msg(ku(2), true).0.end == super::post_handshake_spec::End::Fail(47u8)) by (compute_only);
    assert(msg(ku(2), true).0.wires.len() == 1) by (compute_only);
    assert(msg(ku(255), true).0.end == super::post_handshake_spec::End::Fail(47u8)) by (compute_only);
}

/// §4.6.3, §7.2: on KeyUpdate(`update_not_requested`) the server traffic
/// secret becomes the next generation and the read epoch is fresh, at
/// sequence number 0; the write side and the output are untouched.
pub proof fn lemma_key_update_rotates_read_keys()
    ensures
        msg(ku(0), true).1.server_secret
            == crate::schedule::spec::next_traffic_secret(crypto(), ready().server_secret),
        msg(ku(0), true).1.server_secret != ready().server_secret,
        msg(ku(0), true).1.receiver.unwrap().next == Some(0u64),
        msg(ku(0), true).1.sender == ready().sender,
        msg(ku(0), true).1.client_secret == ready().client_secret,
        msg(ku(0), true).0 == super::post_handshake_spec::quiet(),
{
    assert(msg(ku(0), true).1.server_secret
        == crate::schedule::spec::next_traffic_secret(crypto(), ready().server_secret)) by (compute_only);
    assert(msg(ku(0), true).1.server_secret != ready().server_secret) by (compute_only);
    assert(msg(ku(0), true).1.receiver.unwrap().next == Some(0u64)) by (compute_only);
    assert(msg(ku(0), true).1.sender == ready().sender) by (compute_only);
    assert(msg(ku(0), true).1.client_secret == ready().client_secret) by (compute_only);
    assert(msg(ku(0), true).0 == super::post_handshake_spec::quiet()) by (compute_only);
}

/// §4.6.3: on KeyUpdate(`update_requested`) the client sends one record and
/// then updates its own write keys: the client secret is the next
/// generation and the new send epoch is at sequence number 0. The read keys
/// are updated as well.
pub proof fn lemma_key_update_requested_is_answered()
    ensures
        msg(ku(1), true).0.wires.len() == 1,
        msg(ku(1), true).0.end == super::post_handshake_spec::End::Continue,
        msg(ku(1), true).1.client_secret
            == crate::schedule::spec::next_traffic_secret(crypto(), ready().client_secret),
        msg(ku(1), true).1.sender.unwrap().next == Some(0u64),
        msg(ku(1), true).1.server_secret
            == crate::schedule::spec::next_traffic_secret(crypto(), ready().server_secret),
{
    assert(msg(ku(1), true).0.wires.len() == 1) by (compute_only);
    assert(msg(ku(1), true).0.end == super::post_handshake_spec::End::Continue) by (compute_only);
    assert(msg(ku(1), true).1.client_secret
        == crate::schedule::spec::next_traffic_secret(crypto(), ready().client_secret)) by (compute_only);
    assert(msg(ku(1), true).1.sender.unwrap().next == Some(0u64)) by (compute_only);
    assert(msg(ku(1), true).1.server_secret
        == crate::schedule::spec::next_traffic_secret(crypto(), ready().server_secret)) by (compute_only);
}

/// §4.6.3: the answer is KeyUpdate(`update_not_requested`): "the
/// request_update field" of the reply, the ninth octet of the sent record
/// (five header octets, then the 24, the length, the value), is 0.
pub proof fn lemma_key_update_answer_does_not_ask_again()
    ensures msg(ku(1), true).0.wires[0][9] == 0u8,
{
    assert(msg(ku(1), true).0.wires[0][9] == 0u8) by (compute_only);
}

/// §4.6.3 and the client-initiated update: asking the peer to update sends
/// KeyUpdate(`update_requested`), not asking sends `update_not_requested`;
/// either way the write keys move on.
pub proof fn lemma_client_initiated_update()
    ensures
        super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), true).0.wires[0][9] == 1u8,
        super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), false).0.wires[0][9] == 0u8,
        super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), true).1.client_secret
            == crate::schedule::spec::next_traffic_secret(crypto(), ready().client_secret),
        super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), true).1.sender.unwrap().next
            == Some(0u64),
        super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), true).1.server_secret
            == ready().server_secret,
{
    assert(super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), true).0.wires[0][9] == 1u8)
        by (compute_only);
    assert(super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), false).0.wires[0][9] == 0u8)
        by (compute_only);
    assert(super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), true).1.client_secret
        == crate::schedule::spec::next_traffic_secret(crypto(), ready().client_secret)) by (compute_only);
    assert(super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), true).1.sender.unwrap().next
        == Some(0u64)) by (compute_only);
    assert(super::post_handshake_spec::update_keys(crypto(), cipher(), ready(), true).1.server_secret
        == ready().server_secret) by (compute_only);
}

/// §5.1: "Handshake messages MUST NOT span key changes. Implementations
/// MUST verify that all messages immediately preceding a key change align
/// with a record boundary; if not, then they MUST terminate the connection
/// with an "unexpected_message" alert." A KeyUpdate that is not the last
/// message of its record, or that arrives while a message is unfinished, is
/// `unexpected_message`; the one that is last at a boundary is not.
pub proof fn lemma_key_update_must_end_its_record()
    ensures
        ku_rx(0, false, ready()).0.end == super::post_handshake_spec::End::Fail(10u8),
        ku_rx(0, true, mid_message()).0.end == super::post_handshake_spec::End::Fail(10u8),
        ku_rx(0, true, ready()).0.end == super::post_handshake_spec::End::Continue,
{
    assert(ku_rx(0, false, ready()).0.end == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
    assert(ku_rx(0, true, mid_message()).0.end == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
    assert(ku_rx(0, true, ready()).0.end == super::post_handshake_spec::End::Continue) by (compute_only);
}

/// §6.1: `close_notify` ends the connection: the client answers with its own
/// `close_notify` and the output ends in `Close`; the state keeps no key.
pub proof fn lemma_close_notify_closes()
    ensures
        rec(21, seq![1u8, 0]).0.end == super::post_handshake_spec::End::Close,
        rec(21, seq![1u8, 0]).0.wires.len() == 1,
        rec(21, seq![1u8, 0]).1 == super::post_handshake_spec::closed(),
{
    assert(rec(21, seq![1u8, 0]).0.end == super::post_handshake_spec::End::Close) by (compute_only);
    assert(rec(21, seq![1u8, 0]).0.wires.len() == 1) by (compute_only);
    assert(rec(21, seq![1u8, 0]).1 == super::post_handshake_spec::closed()) by (compute_only);
}

/// §6: every alert but `close_notify` is fatal and, being the peer's, is not
/// answered: `Fail` with its description, nothing sent, the connection
/// failed. That includes `user_canceled` (90), whatever the level.
pub proof fn lemma_other_alerts_are_fatal()
    ensures
        rec(21, seq![2u8, 40]).0
            == (super::post_handshake_spec::Out { wires: seq![], delivered: seq![],
                end: super::post_handshake_spec::End::Fail(40u8) }),
        rec(21, seq![1u8, 90]).0.end == super::post_handshake_spec::End::Fail(90u8),
        rec(21, seq![1u8, 40]).0.end == super::post_handshake_spec::End::Fail(40u8),
        rec(21, seq![2u8, 40]).1 == super::post_handshake_spec::failed(),
{
    assert(rec(21, seq![2u8, 40]).0
        == (super::post_handshake_spec::Out { wires: seq![], delivered: seq![],
            end: super::post_handshake_spec::End::Fail(40u8) })) by (compute_only);
    assert(rec(21, seq![1u8, 90]).0.end == super::post_handshake_spec::End::Fail(90u8)) by (compute_only);
    assert(rec(21, seq![1u8, 40]).0.end == super::post_handshake_spec::End::Fail(40u8)) by (compute_only);
    assert(rec(21, seq![2u8, 40]).1 == super::post_handshake_spec::failed()) by (compute_only);
}

/// §5: application data is delivered as it is, in the record's order, and
/// changes no key.
pub proof fn lemma_application_data_is_delivered()
    ensures
        rec(23, seq![5u8, 6]).0.delivered == seq![5u8, 6],
        rec(23, seq![5u8, 6]).0.wires.len() == 0,
        rec(23, seq![5u8, 6]).1 == ready(),
{
    assert(rec(23, seq![5u8, 6]).0.delivered == seq![5u8, 6]) by (compute_only);
    assert(rec(23, seq![5u8, 6]).0.wires.len() == 0) by (compute_only);
    assert(rec(23, seq![5u8, 6]).1 == ready()) by (compute_only);
}

/// §5: a change_cipher_spec record after the handshake, protected (inner
/// type 20) or an unknown type, is `unexpected_message`; so is a record that
/// interleaves another with an unfinished handshake message (§5.1).
pub proof fn lemma_unexpected_records()
    ensures
        rec(20, seq![1u8]).0.end == super::post_handshake_spec::End::Fail(10u8),
        rec(99, seq![1u8]).0.end == super::post_handshake_spec::End::Fail(10u8),
        super::post_handshake_spec::record(crypto(), cipher(), mid_message(), 23, seq![5u8]).0.end
            == super::post_handshake_spec::End::Fail(10u8),
{
    assert(rec(20, seq![1u8]).0.end == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
    assert(rec(99, seq![1u8]).0.end == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
    assert(super::post_handshake_spec::record(crypto(), cipher(), mid_message(), 23, seq![5u8]).0.end
        == super::post_handshake_spec::End::Fail(10u8)) by (compute_only);
}

/// §6.1: the transport closing before `close_notify` is a truncation:
/// `Fail(internal_error)` (80), nothing sent, no input consumed; once the
/// connection ended, the transport closing is not an error.
pub proof fn lemma_transport_closing()
    ensures
        super::post_handshake_spec::step(crypto(), cipher(), ready(), super::post_handshake_spec::Input::Closed).0.end
            == super::post_handshake_spec::End::Fail(80u8),
        super::post_handshake_spec::step(crypto(), cipher(), ready(), super::post_handshake_spec::Input::Closed).2 == 0,
        super::post_handshake_spec::step(crypto(), cipher(), super::post_handshake_spec::closed(),
            super::post_handshake_spec::Input::Closed).0 == super::post_handshake_spec::quiet(),
{
    assert(super::post_handshake_spec::step(crypto(), cipher(), ready(),
        super::post_handshake_spec::Input::Closed).0.end == super::post_handshake_spec::End::Fail(80u8))
        by (compute_only);
    assert(super::post_handshake_spec::step(crypto(), cipher(), ready(),
        super::post_handshake_spec::Input::Closed).2 == 0) by (compute_only);
    assert(super::post_handshake_spec::step(crypto(), cipher(), super::post_handshake_spec::closed(),
        super::post_handshake_spec::Input::Closed).0 == super::post_handshake_spec::quiet()) by (compute_only);
}

/// §6.1: "Any data received after a closure alert has been received MUST be
/// ignored": bytes after the connection ended are consumed and ignored.
pub proof fn lemma_data_after_the_end_is_ignored()
    ensures
        super::post_handshake_spec::step(crypto(), cipher(), super::post_handshake_spec::closed(),
            super::post_handshake_spec::Input::Bytes(seq![1u8, 2, 3])).0 == super::post_handshake_spec::quiet(),
        super::post_handshake_spec::step(crypto(), cipher(), super::post_handshake_spec::failed(),
            super::post_handshake_spec::Input::Bytes(seq![1u8, 2, 3])).2 == 3,
{
    assert(super::post_handshake_spec::step(crypto(), cipher(), super::post_handshake_spec::closed(),
        super::post_handshake_spec::Input::Bytes(seq![1u8, 2, 3])).0 == super::post_handshake_spec::quiet())
        by (compute_only);
    assert(super::post_handshake_spec::step(crypto(), cipher(), super::post_handshake_spec::failed(),
        super::post_handshake_spec::Input::Bytes(seq![1u8, 2, 3])).2 == 3) by (compute_only);
}

/// §5.3: an exhausted receive epoch is never used again: the next record,
/// whatever it is, is `Fail(internal_error)` (80); the counter does not wrap.
pub proof fn lemma_exhausted_receive_epoch_closes()
    ensures
        super::post_handshake_spec::step(crypto(), cipher(), receiver_exhausted(),
            super::post_handshake_spec::Input::Bytes(seq![23u8, 3, 3, 0, 17])).0.end
            == super::post_handshake_spec::End::Fail(80u8),
{
    assert(super::post_handshake_spec::step(crypto(), cipher(), receiver_exhausted(),
        super::post_handshake_spec::Input::Bytes(seq![23u8, 3, 3, 0, 17])).0.end
        == super::post_handshake_spec::End::Fail(80u8)) by (compute_only);
}

/// §5.3: "if the sequence number would wrap, the implementation MUST either
/// rekey or terminate": a data record on the last sequence number is
/// preceded by a KeyUpdate that uses it, and the data goes out under the new
/// epoch at sequence number 0 (so the epoch is at 1 afterwards). Away from
/// the last number one record is sent.
pub proof fn lemma_last_sequence_number_rekeys_example()
    ensures
        super::post_handshake_spec::needs_rekey(at_last_number()),
        !super::post_handshake_spec::needs_rekey(ready()),
        super::post_handshake_spec::send_application(crypto(), cipher(), at_last_number(), seq![5u8]).0.wires.len() == 2,
        super::post_handshake_spec::send_application(crypto(), cipher(), at_last_number(), seq![5u8]).1.sender.unwrap().next
            == Some(1u64),
        super::post_handshake_spec::send_application(crypto(), cipher(), at_last_number(), seq![5u8]).0.wires[0][9]
            == 0u8,
        super::post_handshake_spec::send_application(crypto(), cipher(), ready(), seq![5u8]).0.wires.len() == 1,
{
    assert(super::post_handshake_spec::needs_rekey(at_last_number())) by (compute_only);
    assert(!super::post_handshake_spec::needs_rekey(ready())) by (compute_only);
    assert(super::post_handshake_spec::send_application(crypto(), cipher(), at_last_number(), seq![5u8]).0.wires.len() == 2)
        by (compute_only);
    assert(super::post_handshake_spec::send_application(crypto(), cipher(), at_last_number(), seq![5u8]).1.sender.unwrap().next
        == Some(1u64)) by (compute_only);
    assert(super::post_handshake_spec::send_application(crypto(), cipher(), at_last_number(), seq![5u8]).0.wires[0][9]
        == 0u8) by (compute_only);
    assert(super::post_handshake_spec::send_application(crypto(), cipher(), ready(), seq![5u8]).0.wires.len() == 1)
        by (compute_only);
}

/// §6.1: closing sends `close_notify` and ends the connection; once ended,
/// closing does nothing.
pub proof fn lemma_local_close()
    ensures
        super::post_handshake_spec::close(cipher(), ready()).0.wires.len() == 1,
        super::post_handshake_spec::close(cipher(), ready()).0.end == super::post_handshake_spec::End::Close,
        super::post_handshake_spec::close(cipher(), ready()).1 == super::post_handshake_spec::closed(),
        super::post_handshake_spec::close(cipher(), super::post_handshake_spec::closed()).0
            == super::post_handshake_spec::quiet(),
{
    assert(super::post_handshake_spec::close(cipher(), ready()).0.wires.len() == 1) by (compute_only);
    assert(super::post_handshake_spec::close(cipher(), ready()).0.end == super::post_handshake_spec::End::Close)
        by (compute_only);
    assert(super::post_handshake_spec::close(cipher(), ready()).1 == super::post_handshake_spec::closed())
        by (compute_only);
    assert(super::post_handshake_spec::close(cipher(), super::post_handshake_spec::closed()).0
        == super::post_handshake_spec::quiet()) by (compute_only);
}

/// §5.1, §5.2: a record of more than 2^14 bytes of data is not sent:
/// `Fail(record_overflow)` (22) with nothing sent.
pub proof fn lemma_oversized_data_is_refused()
    ensures
        super::post_handshake_spec::send_application(crypto(), cipher(), ready(),
            Seq::new(16385, |i: int| 5u8)).0.end == super::post_handshake_spec::End::Fail(22u8),
        super::post_handshake_spec::send_application(crypto(), cipher(), ready(),
            Seq::new(16385, |i: int| 5u8)).0.wires.len() == 0,
{
    assert(super::post_handshake_spec::send_application(crypto(), cipher(), ready(),
        Seq::new(16385, |i: int| 5u8)).0.end == super::post_handshake_spec::End::Fail(22u8)) by (compute_only);
    assert(super::post_handshake_spec::send_application(crypto(), cipher(), ready(),
        Seq::new(16385, |i: int| 5u8)).0.wires.len() == 0) by (compute_only);
}

/// The actions of an output are every `Send`, then the `Deliver`, then the
/// end; a `Deliver` of nothing is no action.
pub proof fn lemma_actions_order()
    ensures
        super::post_handshake_spec::actions(super::post_handshake_spec::Out {
            wires: seq![seq![1u8], seq![2u8]],
            delivered: seq![3u8],
            end: super::post_handshake_spec::End::Fail(40u8),
        }) == seq![
            super::post_handshake_spec::Action::Send(seq![1u8]),
            super::post_handshake_spec::Action::Send(seq![2u8]),
            super::post_handshake_spec::Action::Deliver(seq![3u8]),
            super::post_handshake_spec::Action::Fail(40u8),
        ],
        super::post_handshake_spec::actions(super::post_handshake_spec::quiet()).len() == 0,
{
    assert(super::post_handshake_spec::actions(super::post_handshake_spec::Out {
        wires: seq![seq![1u8], seq![2u8]],
        delivered: seq![3u8],
        end: super::post_handshake_spec::End::Fail(40u8),
    }) =~= seq![
        super::post_handshake_spec::Action::Send(seq![1u8]),
        super::post_handshake_spec::Action::Send(seq![2u8]),
        super::post_handshake_spec::Action::Deliver(seq![3u8]),
        super::post_handshake_spec::Action::Fail(40u8),
    ]);
    assert(super::post_handshake_spec::actions(super::post_handshake_spec::quiet()).len() == 0);
}
} // verus!
