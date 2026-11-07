//! RFC 8446 KeyUpdate and fatal-alert facts about the dispatcher spec, used
//! by proofs and mutation certificates: general lemmas, and concrete ones
//! evaluated on the fixtures of `dispatcher_certificates`.
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// §5.2: a protected client flight starts with the record header, so it is
/// never empty, and `AwaitClientFlight` always has something to wait for.
pub proof fn lemma_protected_flight_nonempty(ciphers: super::dispatcher_spec::Ciphers,
    s: super::dispatcher_spec::State, flight: Seq<u8>)
    ensures match super::dispatcher_spec::protect_client_flight(ciphers, s, flight).1 {
        Ok(wire) => wire.len() > 0,
        Err(_) => true,
    },
{
    if let Some(sender) = s.handshake_sender {
        let (_, sealed) = crate::traffic::spec::send(super::dispatcher_spec::seal_with(ciphers, sender), sender,
            crate::spec::CT_HANDSHAKE, flight, 0);
        if let Ok(record) = sealed {
            let n = sender.next->Some_0;
            let inner = crate::spec::write_inner_plaintext(flight, crate::spec::CT_HANDSHAKE, 0);
            let ad = crate::spec::additional_data(inner.len() + 16);
            assert(ad.len() > 0);
            assert(record ==crate::spec::encrypt_record(super::dispatcher_spec::seal_with(ciphers, sender), 16,
                sender.iv, n, crate::spec::CT_HANDSHAKE, flight, 0));
            assert(record.len() >= ad.len());
        }
    }
}

/// RFC 8446 §5.1: a compatibility CCS between the fragments of one handshake
/// message interleaves another record type and is refused; at a boundary the
/// same record is still dropped.
pub proof fn lemma_compatibility_ccs_not_dropped_mid_message()
    ensures
        !super::dispatcher_spec::compatibility_ccs_dropped(super::dispatcher_spec::Mode::Handshake,
            Some(crate::auth::spec::Phase::Finished), crate::spec::Reasm { buf: seq![1u8] }),
        super::dispatcher_spec::compatibility_ccs_dropped(super::dispatcher_spec::Mode::Handshake,
            Some(crate::auth::spec::Phase::Finished), crate::spec::reasm_new()),
{
    reveal(crate::spec::reasm_new);
}

// ---------------------------------------------------------------------------
// RFC 8446 §5.3, §6, §6.1, §6.2: the fatal alerts the dispatcher sends.
// ---------------------------------------------------------------------------

/// §5.3, §6.2: a locally detected fatal error sends the fatal alert sealed
/// under the settled write epoch's next sequence number, the one no record
/// has used, with the key-explicit AEAD at that epoch's key.
pub proof fn lemma_alert_uses_next_sequence_number(ciphers: super::dispatcher_spec::Ciphers,
    s: super::dispatcher_spec::State, description: u8, epoch: crate::traffic::spec::State, n: u64)
    requires
        super::dispatcher_spec::alert_epoch(s) == Some(epoch),
        epoch.next == Some(n),
        !epoch.failed,
    ensures
        super::dispatcher_spec::fatal(ciphers, s, description).0 == super::dispatcher_spec::Action::Fail(
            description, Some(crate::spec::encrypt_record(super::dispatcher_spec::seal_with(ciphers, epoch), 16,
                epoch.iv, n, crate::spec::CT_ALERT, super::dispatcher_spec::fatal_alert(description), 0))),
{
    assert(super::dispatcher_spec::fatal_alert(description).len() == 2);
}

/// §5.3, §6.2: the alert is the last record under its key. The state after a
/// fatal error holds no key at all, so nothing is sealed after the alert
/// under the sequence number it took, or any other.
pub proof fn lemma_alert_is_the_last_record(ciphers: super::dispatcher_spec::Ciphers,
    s: super::dispatcher_spec::State, description: u8)
    ensures
        super::dispatcher_spec::fatal(ciphers, s, description).1 == super::dispatcher_spec::failed(),
        super::dispatcher_spec::no_live_secrets(super::dispatcher_spec::fatal(ciphers, s, description).1),
        super::dispatcher_spec::alert_epoch(super::dispatcher_spec::fatal(ciphers, s, description).1) is None,
{}

/// The epoch an alert is sealed under is a write epoch the client holds, in
/// a phase where the peer reads it next: the handshake epoch during the
/// server's flight. Awaiting the Finished acknowledgement, at the handoff,
/// failed and closed, there is none.
pub proof fn lemma_alert_epoch_is_held(s: super::dispatcher_spec::State)
    ensures
        match super::dispatcher_spec::alert_epoch(s) {
            Some(e) => s.mode == super::dispatcher_spec::Mode::Handshake && s.handshake_sender == Some(e),
            None => true,
        },
        (s.mode == super::dispatcher_spec::Mode::AwaitClientFlight
            || s.mode == super::dispatcher_spec::Mode::Ready
            || s.mode == super::dispatcher_spec::Mode::Failed
            || s.mode == super::dispatcher_spec::Mode::Closed)
            ==> super::dispatcher_spec::alert_epoch(s) is None,
{}

/// If no write key is held and settled, no protected alert is sent.
pub proof fn lemma_no_write_key_no_alert(ciphers: super::dispatcher_spec::Ciphers,
    s: super::dispatcher_spec::State, description: u8)
    requires super::dispatcher_spec::alert_epoch(s) is None,
    ensures super::dispatcher_spec::fatal(ciphers, s, description).0
        == super::dispatcher_spec::Action::Fail(description, None),
{}

/// §6, §6.2: a fatal alert from the peer is never answered, in any state.
pub proof fn lemma_peer_alert_not_answered(ciphers: super::dispatcher_spec::Ciphers,
    s: super::dispatcher_spec::State, description: u8)
    ensures super::dispatcher_spec::receive_fatal_alert(ciphers, s, description)
        == (super::dispatcher_spec::Action::PeerAlert(description), super::dispatcher_spec::failed()),
{}

/// §6.1: a truncated connection sends nothing.
pub proof fn lemma_truncation_sends_nothing(description: u8)
    ensures super::dispatcher_spec::die(description)
        == (super::dispatcher_spec::Action::Fail(description, None), super::dispatcher_spec::failed()),
{}

/// §6.2: during the server's flight, a local error (here bad_certificate, 42)
/// is sent as a fatal alert, sealed under the client handshake epoch at
/// sequence number 0. With the fixture AEAD the record is the header
/// (application_data, 0x0303, 19 octets), the nonce (all zero), then the
/// inner plaintext: level 2 (fatal), 42, content type 21 (alert).
pub proof fn lemma_flight_failure_sends_alert()
    ensures super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_state(), 42).0
        == super::dispatcher_spec::Action::Fail(42u8, Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 42, 21])),
{
    assert(super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_state(), 42).0
        == super::dispatcher_spec::Action::Fail(42u8, Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 42, 21]))) by (compute_only);
}

/// §6.1: a close during the server's flight sends close_notify at warning
/// level (1, 0), sealed under the client handshake epoch.
pub proof fn lemma_flight_close_sends_close_notify()
    ensures super::dispatcher_spec::closing(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_state()).0
        == super::dispatcher_spec::Action::Close(Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 21])),
{
    assert(super::dispatcher_spec::closing(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_state()).0
        == super::dispatcher_spec::Action::Close(Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 21]))) by (compute_only);
}

/// §5.3, §6.2: with five records already sent under the client handshake
/// epoch, a local error (unexpected_message, 10) is sealed at sequence number
/// 5, not a number already used: the nonce's last octet is 5.
pub proof fn lemma_failure_sends_alert_at_next_number()
    ensures super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_at(5), 10).0
        == super::dispatcher_spec::Action::Fail(10u8, Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 10, 21])),
{
    assert(super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_at(5), 10).0
        == super::dispatcher_spec::Action::Fail(10u8, Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 10, 21]))) by (compute_only);
}

} // verus!
