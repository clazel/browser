//! Concrete RFC 8446 §4.4.4, §5, §5.1, §6 and §7.3 facts about one step of the
//! dispatcher ([`super::dispatcher_spec::feed`], `acknowledge`), evaluated by
//! Verus on the fixtures of `dispatcher_certificates`. `mutations.json` breaks
//! each rule in turn and a certificate calls one of these lemmas on the broken
//! spec.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// §5.1: an unfinished record is kept in the framing buffer: all of it is
/// consumed, nothing else happens, and the next call goes on from there.
pub proof fn lemma_feed_keeps_partial_record()
    ensures
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![23u8, 3u8]).0 == 2,
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![23u8, 3u8]).1 == super::dispatcher_spec::Action::None,
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![23u8, 3u8]).2.framing == seq![23u8, 3u8],
{
    hide(super::dispatcher_certificates::fed);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![23u8, 3u8]).0 == 2) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![23u8, 3u8]).1 == super::dispatcher_spec::Action::None) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![23u8, 3u8]).2.framing == seq![23u8, 3u8]) by (compute_only);
}

/// §5: one call takes one record and leaves the rest with the caller. Here the
/// record is a dummy change_cipher_spec, which is dropped.
pub proof fn lemma_feed_stops_at_the_record_boundary()
    ensures
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![20u8, 3, 3, 0, 1, 1, 99]).0 == 6,
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![20u8, 3, 3, 0, 1, 1, 99]).1 == super::dispatcher_spec::Action::Ignored,
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![20u8, 3, 3, 0, 1, 1, 99]).2.framing.len() == 0,
{
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![20u8, 3, 3, 0, 1, 1, 99]).0 == 6) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![20u8, 3, 3, 0, 1, 1, 99]).1 == super::dispatcher_spec::Action::Ignored) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), seq![20u8, 3, 3, 0, 1, 1, 99]).2.framing.len() == 0) by (compute_only);
}

/// §5: a record that arrived in two calls leaves no prefix behind it.
pub proof fn lemma_feed_clears_the_framing_buffer()
    ensures
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_part_framed(), seq![1u8]).0 == 1,
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_part_framed(), seq![1u8]).1 == super::dispatcher_spec::Action::Ignored,
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_part_framed(), seq![1u8]).2.framing.len() == 0,
{
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_part_framed(), seq![1u8]).0 == 1) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_part_framed(), seq![1u8]).1 == super::dispatcher_spec::Action::Ignored) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_part_framed(), seq![1u8]).2.framing.len() == 0) by (compute_only);
}

/// §5.1: a dummy change_cipher_spec between the fragments of one handshake
/// message is refused, through the whole step.
pub proof fn lemma_feed_refuses_ccs_mid_message()
    ensures super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_mid_message(), seq![20u8, 3, 3, 0, 1, 1]).2.mode == super::dispatcher_spec::Mode::Failed,
{
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_mid_message(), seq![20u8, 3, 3, 0, 1, 1]).2.mode == super::dispatcher_spec::Mode::Failed) by (compute_only);
}

/// §5: no application data before the handshake ends: unexpected_message,
/// sealed under the client handshake epoch.
pub proof fn lemma_feed_refuses_application_data()
    ensures
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![7u8], 23)).1
            == super::dispatcher_spec::Action::Fail(10u8, super::dispatcher_spec::alert_wire(super::dispatcher_certificates::flight_ciphers(), super::dispatcher_certificates::flight_start(), 10)),
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![7u8], 23)).2.mode == super::dispatcher_spec::Mode::Failed,
{
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![7u8], 23)).1
        == super::dispatcher_spec::Action::Fail(10u8, super::dispatcher_spec::alert_wire(super::dispatcher_certificates::flight_ciphers(), super::dispatcher_certificates::flight_start(), 10))) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![7u8], 23)).2.mode == super::dispatcher_spec::Mode::Failed) by (compute_only);
}

/// §6: user_canceled changes nothing but the read sequence number, which moves
/// on (§5.3: a record is opened under each number once).
pub proof fn lemma_feed_user_canceled_goes_on()
    ensures
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 90], 21)).1 == super::dispatcher_spec::Action::Cancelled,
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 90], 21)).2.mode == super::dispatcher_spec::Mode::Handshake,
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 90], 21)).2.handshake_receiver == Some(super::dispatcher_certificates::alert_epoch_at(1)),
{
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 90], 21)).1 == super::dispatcher_spec::Action::Cancelled) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 90], 21)).2.mode == super::dispatcher_spec::Mode::Handshake) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 90], 21)).2.handshake_receiver == Some(super::dispatcher_certificates::alert_epoch_at(1))) by (compute_only);
}

/// §6.1: the server's close_notify is answered with ours, and ends the flight.
pub proof fn lemma_feed_close_notify_closes()
    ensures
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 0], 21)).1
            == super::dispatcher_spec::Action::Close(super::dispatcher_spec::close_wire(super::dispatcher_certificates::flight_ciphers(), super::dispatcher_certificates::flight_start())),
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 0], 21)).2.mode == super::dispatcher_spec::Mode::Closed,
{
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 0], 21)).1
        == super::dispatcher_spec::Action::Close(super::dispatcher_spec::close_wire(super::dispatcher_certificates::flight_ciphers(), super::dispatcher_certificates::flight_start()))) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![1u8, 0], 21)).2.mode == super::dispatcher_spec::Mode::Closed) by (compute_only);
}

/// §6: any other alert from the server is fatal and not answered.
pub proof fn lemma_feed_peer_alert_is_fatal()
    ensures
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![2u8, 40], 21)).1 == super::dispatcher_spec::Action::PeerAlert(40u8),
        super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![2u8, 40], 21)).2.mode == super::dispatcher_spec::Mode::Failed,
{
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![2u8, 40], 21)).1 == super::dispatcher_spec::Action::PeerAlert(40u8)) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::flight_start(), super::dispatcher_certificates::record_of(seq![2u8, 40], 21)).2.mode == super::dispatcher_spec::Mode::Failed) by (compute_only);
}

/// §5.1: a Finished that is not the last message of its record, or that leaves
/// part of a message behind it, is refused, even though it is the right
/// Finished. The key change after it falls on a record boundary.
pub proof fn lemma_feed_finished_must_end_the_record()
    ensures
        super::dispatcher_certificates::fed(super::dispatcher_certificates::before_finished(false), super::dispatcher_certificates::record_of(super::dispatcher_certificates::finished() + seq![8u8, 0, 0, 0], 22)).2.mode == super::dispatcher_spec::Mode::Failed,
        super::dispatcher_certificates::fed(super::dispatcher_certificates::before_finished(false), super::dispatcher_certificates::record_of(super::dispatcher_certificates::finished() + seq![8u8, 0], 22)).2.mode == super::dispatcher_spec::Mode::Failed,
{
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::before_finished(false), super::dispatcher_certificates::record_of(super::dispatcher_certificates::finished() + seq![8u8, 0, 0, 0], 22)).2.mode == super::dispatcher_spec::Mode::Failed) by (compute_only);
    assert(super::dispatcher_certificates::fed(super::dispatcher_certificates::before_finished(false), super::dispatcher_certificates::record_of(super::dispatcher_certificates::finished() + seq![8u8, 0], 22)).2.mode == super::dispatcher_spec::Mode::Failed) by (compute_only);
}

/// §4.4.4: the right Finished, alone in its record: the client flight goes out
/// and waits for its acknowledgement. With the compatibility CCS owed, it comes
/// first (Appendix D.4), and it is owed no longer.
pub proof fn lemma_feed_finished_sends_the_flight()
    ensures
        super::dispatcher_certificates::awaiting(false).mode == super::dispatcher_spec::Mode::AwaitClientFlight,
        super::dispatcher_certificates::awaiting(false).pending_flight == super::dispatcher_certificates::sent(super::dispatcher_certificates::fed(super::dispatcher_certificates::before_finished(false), super::dispatcher_certificates::record_of(super::dispatcher_certificates::finished(), 22)).1),
        super::dispatcher_certificates::awaiting(false).pending_flight[0] == 23,
        super::dispatcher_certificates::awaiting(true).pending_flight.take(6) == seq![20u8, 3, 3, 0, 1, 1],
        super::dispatcher_certificates::awaiting(true).pending_flight.skip(6) == super::dispatcher_certificates::awaiting(false).pending_flight,
        !super::dispatcher_certificates::awaiting(true).ccs_pending,
        super::dispatcher_certificates::awaiting(false).handshake_sender == Some(super::dispatcher_certificates::alert_epoch_at(1)),
{
    assert(super::dispatcher_certificates::awaiting(false).handshake_sender == Some(super::dispatcher_certificates::alert_epoch_at(1))) by (compute_only);
    assert(super::dispatcher_certificates::awaiting(false).mode == super::dispatcher_spec::Mode::AwaitClientFlight) by (compute_only);
    assert(super::dispatcher_certificates::awaiting(false).pending_flight == super::dispatcher_certificates::sent(super::dispatcher_certificates::fed(super::dispatcher_certificates::before_finished(false), super::dispatcher_certificates::record_of(super::dispatcher_certificates::finished(), 22)).1)) by (compute_only);
    assert(super::dispatcher_certificates::awaiting(false).pending_flight[0] == 23) by (compute_only);
    assert(super::dispatcher_certificates::awaiting(true).pending_flight.take(6) == seq![20u8, 3, 3, 0, 1, 1]) by (compute_only);
    assert(super::dispatcher_certificates::awaiting(true).pending_flight.skip(6) == super::dispatcher_certificates::awaiting(false).pending_flight) by (compute_only);
    assert(!super::dispatcher_certificates::awaiting(true).ccs_pending) by (compute_only);
}

/// §7.1, §7.3: the acknowledgement derives each application secret under its
/// own label from the hash through the server Finished, and drops the handshake
/// epochs and the master secret.
pub proof fn lemma_acknowledge_derives_the_secrets()
    ensures
        super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).0 == super::dispatcher_spec::Action::Ready,
        super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.mode == super::dispatcher_spec::Mode::Ready,
        super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.client_application_secret
            == crate::schedule::spec::expand_label(crate::auth::examples::crypto(), Seq::new(32, |_i: int| 5u8),
                crate::schedule::spec::Label::ClientApplication, Seq::new(32, |_i: int| 75u8), 32),
        super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.server_application_secret
            == crate::schedule::spec::expand_label(crate::auth::examples::crypto(), Seq::new(32, |_i: int| 5u8),
                crate::schedule::spec::Label::ServerApplication, Seq::new(32, |_i: int| 75u8), 32),
        super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.handshake_sender == None::<crate::traffic::spec::State>,
        super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.master.len() == 0,
{
    assert(super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).0 == super::dispatcher_spec::Action::Ready) by (compute_only);
    assert(super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.mode == super::dispatcher_spec::Mode::Ready) by (compute_only);
    assert(super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.client_application_secret
        == crate::schedule::spec::expand_label(crate::auth::examples::crypto(), Seq::new(32, |_i: int| 5u8),
            crate::schedule::spec::Label::ClientApplication, Seq::new(32, |_i: int| 75u8), 32)) by (compute_only);
    assert(super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.server_application_secret
        == crate::schedule::spec::expand_label(crate::auth::examples::crypto(), Seq::new(32, |_i: int| 5u8),
            crate::schedule::spec::Label::ServerApplication, Seq::new(32, |_i: int| 75u8), 32)) by (compute_only);
    assert(super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.handshake_sender == None::<crate::traffic::spec::State>) by (compute_only);
    assert(super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), super::dispatcher_certificates::awaiting(false).pending_flight).1.master.len() == 0) by (compute_only);
}

/// Application keys wait for the exact bytes: anything else is internal_error
/// with no alert, because the client Finished is sealed but not settled.
pub proof fn lemma_acknowledge_refuses_other_bytes()
    ensures
        super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), seq![1u8]).0 == super::dispatcher_spec::Action::Fail(80u8, None::<Seq<u8>>),
        super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), seq![1u8]).1.mode == super::dispatcher_spec::Mode::Failed,
{
    assert(super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), seq![1u8]).0 == super::dispatcher_spec::Action::Fail(80u8, None::<Seq<u8>>)) by (compute_only);
    assert(super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false), seq![1u8]).1.mode == super::dispatcher_spec::Mode::Failed) by (compute_only);
}
} // verus!
