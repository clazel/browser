//! RFC 8446 Appendix D.4, the client's sending side: the crate's dummy
//! change_cipher_spec (`hello/bootstrap_spec.rs`'s record before ClientHello2,
//! `traffic/handshake_spec.rs`'s `needs_ccs`, `connection/dispatcher_spec.rs`'s
//! `compatibility_ccs_record` and `protect_client_flight`) against the
//! clean-room `transcription::middlebox` (#140): [`theorem_compatibility_ccs`].
//!
//! The transcription makes compatibility mode a parameter of its
//! `ClientConfig`; the crate derives it from the configuration's session ID
//! (`hello::bootstrap_spec`: `compatibility == (session_id.len() > 0)`,
//! `needs_ccs`). Here the transcription's mode is that.
//!
//! What is proven: the record's bytes, and its placement over the client's
//! writes after the first ClientHello. The transcription applies
//! `before_second_flight` to each batch of records the client writes; the crate
//! puts the record before ClientHello2 after a HelloRetryRequest, and
//! otherwise before the encrypted flight (`ccs_pending`). Both write it exactly
//! once, before the first batch.
//!
//! Tied to the streams: before ClientHello2, by
//! [`super::bootstrap::theorem_bootstrap_equivalence`] (the crate's flight
//! is the flattened `middlebox::client_receive_stream` records); before the
//! encrypted flight, by [`super::dispatcher::theorem_dispatcher_equivalence`]
//! (`dispatcher::sent_agrees`: the crate's bytes are the transcription's
//! `before_second_flight` batch, its flight coalesced into one record).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The crate's compatibility mode for a configuration.
pub open spec fn mode(config: crate::hello::client_spec::Config) -> bool {
    config.session_id.len() > 0
}

/// Whether the transcription has written the dummy record before the
/// encrypted flight: in the mode, before ClientHello2, after a retry.
pub open spec fn sent_before(config: crate::hello::client_spec::Config, transcript: crate::transcript::spec::State) -> bool {
    transcript.retried && mode(config)
}

/// The bytes of a batch of records.
pub open spec fn flatten(records: Seq<Seq<u8>>) -> Seq<u8>
    decreases records.len(),
{
    if records.len() == 0 { seq![] } else { records[0] + flatten(records.skip(1)) }
}

/// §5's dummy record: the same six bytes on all three sides.
pub proof fn lemma_ccs_bytes()
    ensures
        crate::hello::bootstrap_spec::compatibility_ccs() == crate::transcription::middlebox::dummy_change_cipher_spec_record(),
        crate::connection::dispatcher_spec::compatibility_ccs_record()
            == crate::transcription::middlebox::dummy_change_cipher_spec_record(),
{
    assert(crate::transcription::middlebox::dummy_change_cipher_spec_record() =~= seq![20u8, 3u8, 3u8, 0u8, 1u8, 1u8])
        by (compute);
}

/// One record, or the dummy record and one record, as bytes.
pub proof fn lemma_flatten(a: Seq<u8>, b: Seq<u8>)
    ensures
        flatten(seq![a]) == a,
        flatten(seq![a, b]) == a + b,
{
    assert(seq![a].skip(1) =~= Seq::<Seq<u8>>::empty());
    assert(seq![a, b].skip(1) =~= seq![b]);
    assert(seq![b].skip(1) =~= Seq::<Seq<u8>>::empty());
    assert(flatten(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
    assert(b + Seq::<u8>::empty() =~= b);
    assert(seq![b][0] == b);
    assert(flatten(seq![b]) == b);
    assert(seq![a, b][0] == a);
    assert(seq![a][0] == a);
    assert(a + Seq::<u8>::empty() =~= a);
}

/// The encrypted flight the dispatcher writes is the transcription's batch
/// for its one sealed record, with `ccs_pending` as the transcription's "not
/// yet sent in compatibility mode", and the record is then no longer owed.
pub open spec fn protected_as_batch(ciphers: crate::connection::dispatcher_spec::Ciphers,
    s: crate::connection::dispatcher_spec::State, flight: Seq<u8>) -> bool
{
    let (after, out) = crate::connection::dispatcher_spec::protect_client_flight(ciphers, s, flight);
    let sender = s.handshake_sender->Some_0;
    let record = crate::traffic::spec::send(crate::connection::dispatcher_spec::seal_with(ciphers, sender), sender,
        crate::spec::CT_HANDSHAKE, flight, 0).1->Ok_0;
    let (batch, sent) = crate::transcription::middlebox::before_second_flight(s.ccs_pending, false, seq![record]);
    &&& out == Ok::<Seq<u8>, u8>(flatten(batch))
    &&& !after.ccs_pending
    &&& sent == s.ccs_pending
}

/// Appendix D.4, for every configuration, every transcript, every
/// ClientHello2 record and every encrypted-flight record:
/// - after a HelloRetryRequest, the crate's ClientHello2 bytes (the
///   bootstrap's `compatibility_ccs() + record` in the mode, else the record)
///   are the transcription's first batch, and the transcription has then
///   written its record exactly when the crate has;
/// - the crate's encrypted flight (`protect_client_flight` with
///   `ccs_pending == needs_ccs`) carries the record exactly when the
///   transcription's `before_second_flight` puts it before that flight, given
///   what was written before ClientHello2.
pub proof fn theorem_compatibility_ccs()
    ensures
        forall|config: crate::hello::client_spec::Config, ch2: Seq<u8>| {
            let (batch, sent) = #[trigger] crate::transcription::middlebox::before_second_flight(mode(config), false, seq![ch2]);
            &&& flatten(batch) == if mode(config) { crate::hello::bootstrap_spec::compatibility_ccs() + ch2 } else { ch2 }
            &&& sent == mode(config)
        },
        forall|config: crate::hello::client_spec::Config, transcript: crate::transcript::spec::State, flight: Seq<u8>| {
            let (batch, sent) = #[trigger] crate::transcription::middlebox::before_second_flight(mode(config), sent_before(config, transcript),
                seq![flight]);
            &&& flatten(batch) == if crate::traffic::handshake_spec::needs_ccs(config, transcript) {
                crate::connection::dispatcher_spec::compatibility_ccs_record() + flight } else { flight }
            &&& sent == mode(config)
        },
        forall|ciphers: crate::connection::dispatcher_spec::Ciphers, s: crate::connection::dispatcher_spec::State,
            flight: Seq<u8>|
            #[trigger] crate::connection::dispatcher_spec::protect_client_flight(ciphers, s, flight).1 is Ok
                ==> protected_as_batch(ciphers, s, flight),
{
    lemma_ccs_bytes();
    assert forall|config: crate::hello::client_spec::Config, ch2: Seq<u8>| {
        let (batch, sent) = #[trigger] crate::transcription::middlebox::before_second_flight(mode(config), false, seq![ch2]);
        &&& flatten(batch) == if mode(config) { crate::hello::bootstrap_spec::compatibility_ccs() + ch2 } else { ch2 }
        &&& sent == mode(config)
    } by {
        lemma_flatten(crate::transcription::middlebox::dummy_change_cipher_spec_record(), ch2);
        assert(seq![crate::transcription::middlebox::dummy_change_cipher_spec_record()] + seq![ch2]
            =~= seq![crate::transcription::middlebox::dummy_change_cipher_spec_record(), ch2]);
        lemma_flatten(ch2, ch2);
    }
    assert forall|config: crate::hello::client_spec::Config, transcript: crate::transcript::spec::State, flight: Seq<u8>| {
        let (batch, sent) = #[trigger] crate::transcription::middlebox::before_second_flight(mode(config), sent_before(config, transcript),
            seq![flight]);
        &&& flatten(batch) == if crate::traffic::handshake_spec::needs_ccs(config, transcript) {
            crate::connection::dispatcher_spec::compatibility_ccs_record() + flight } else { flight }
        &&& sent == mode(config)
    } by {
        lemma_flatten(crate::transcription::middlebox::dummy_change_cipher_spec_record(), flight);
        assert(seq![crate::transcription::middlebox::dummy_change_cipher_spec_record()] + seq![flight]
            =~= seq![crate::transcription::middlebox::dummy_change_cipher_spec_record(), flight]);
        lemma_flatten(flight, flight);
    }
    assert forall|ciphers: crate::connection::dispatcher_spec::Ciphers, s: crate::connection::dispatcher_spec::State,
        flight: Seq<u8>|
        #[trigger] crate::connection::dispatcher_spec::protect_client_flight(ciphers, s, flight).1 is Ok
        implies protected_as_batch(ciphers, s, flight) by {
        let sender = s.handshake_sender->Some_0;
        let record = crate::traffic::spec::send(crate::connection::dispatcher_spec::seal_with(ciphers, sender), sender,
            crate::spec::CT_HANDSHAKE, flight, 0).1->Ok_0;
        lemma_flatten(crate::transcription::middlebox::dummy_change_cipher_spec_record(), record);
        assert(seq![crate::transcription::middlebox::dummy_change_cipher_spec_record()] + seq![record]
            =~= seq![crate::transcription::middlebox::dummy_change_cipher_spec_record(), record]);
        lemma_flatten(record, record);
    }
}

} // verus!
