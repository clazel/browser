//! Concrete fatal-alert fixtures used by certified mutations.
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
pub open spec fn dummy_open(_key: Seq<u8>, _nonce: Seq<u8>, _ad: Seq<u8>, _ciphertext: Seq<u8>) -> Option<Seq<u8>> { None }

/// An AEAD stand-in whose output shows its nonce: the nonce, then the
/// plaintext. A record sealed with it shows the sequence number it used and
/// its inner plaintext (content, then content type).
pub open spec fn nonce_seal(_key: Seq<u8>, nonce: Seq<u8>, _ad: Seq<u8>, plaintext: Seq<u8>) -> Seq<u8> {
    nonce + plaintext
}

pub open spec fn alert_ciphers() -> super::dispatcher_spec::Ciphers {
    super::dispatcher_spec::Ciphers {
        seal: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>| nonce_seal(key, nonce, ad, plaintext),
        open: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, ciphertext: Seq<u8>| dummy_open(key, nonce, ad, ciphertext),
    }
}

/// A send epoch with an all-zero IV, so its nonce is the sequence number
/// (§5.3), at sequence number `next`.
pub open spec fn alert_epoch_at(next: u64) -> crate::traffic::spec::State {
    crate::traffic::spec::State {
        key: Seq::new(32, |_i: int| 7u8),
        iv: seq![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        next: Some(next),
        failed: false,
    }
}

/// The server's flight: the client handshake epoch has sealed nothing yet.
pub open spec fn sample_flight_state() -> super::dispatcher_spec::State { sample_flight_at(0) }

/// The server's flight, with `next` records sealed under the client handshake
/// epoch.
pub open spec fn sample_flight_at(next: u64) -> super::dispatcher_spec::State {
    super::dispatcher_spec::State {
        mode: super::dispatcher_spec::Mode::Handshake,
        handshake_sender: Some(alert_epoch_at(next)),
        handshake_receiver: Some(alert_epoch_at(0)),
        ..super::dispatcher_spec::failed()
    }
}

/// §5.2: an AEAD stand-in that opens what [`record_of`] built: it takes the
/// 16-octet tag off and returns the inner plaintext.
pub open spec fn tag_open(_key: Seq<u8>, _nonce: Seq<u8>, _ad: Seq<u8>, ciphertext: Seq<u8>) -> Option<Seq<u8>> {
    if ciphertext.len() >= 16 { Some(ciphertext.take(ciphertext.len() - 16)) } else { None }
}

/// Seals so that a record shows its nonce and inner plaintext, and opens
/// [`record_of`]'s records.
pub open spec fn flight_ciphers() -> super::dispatcher_spec::Ciphers {
    super::dispatcher_spec::Ciphers {
        seal: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>| nonce_seal(key, nonce, ad, plaintext),
        open: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, ciphertext: Seq<u8>| tag_open(key, nonce, ad, ciphertext),
    }
}

/// §5.2: a protected record of this content and inner type, for [`tag_open`].
pub open spec fn record_of(content: Seq<u8>, typ: u8) -> Seq<u8> {
    let inner = content + seq![typ];
    crate::spec::additional_data(inner.len() + 16) + inner + Seq::new(16, |_i: int| 0u8)
}

/// §4.4.4: the Finished that `auth::examples::after_signature` expects.
pub open spec fn finished() -> Seq<u8> { seq![20u8, 0, 0, 32] + Seq::new(32, |_i: int| 112u8) }

/// The server's flight over the authentication fixtures, in this Auth state.
pub open spec fn flight_with(auth: crate::auth::spec::State, ccs_pending: bool) -> super::dispatcher_spec::State {
    super::dispatcher_spec::State {
        mode: super::dispatcher_spec::Mode::Handshake,
        auth: Some(auth),
        handshake_sender: Some(alert_epoch_at(0)),
        handshake_receiver: Some(alert_epoch_at(0)),
        master: Seq::new(32, |_i: int| 5u8),
        ccs_pending,
        ..super::dispatcher_spec::failed()
    }
}

/// The start of the flight.
pub open spec fn flight_start() -> super::dispatcher_spec::State {
    flight_with(crate::auth::examples::initial(), false)
}

/// The start of the flight, with all but the last octet of a dummy
/// change_cipher_spec record in the framing buffer.
pub open spec fn flight_part_framed() -> super::dispatcher_spec::State {
    super::dispatcher_spec::State { framing: seq![20u8, 3, 3, 0, 1], ..flight_start() }
}

/// The start of the flight, part-way through a handshake message.
pub open spec fn flight_mid_message() -> super::dispatcher_spec::State {
    super::dispatcher_spec::State { reassembly: crate::spec::Reasm { buf: seq![8u8] }, ..flight_start() }
}

/// The flight just before the server's Finished.
pub open spec fn before_finished(ccs_pending: bool) -> super::dispatcher_spec::State {
    flight_with(crate::auth::examples::after_signature(), ccs_pending)
}

/// One `feed` over the fixtures.
pub open spec fn fed(s: super::dispatcher_spec::State, input: Seq<u8>)
    -> (nat, super::dispatcher_spec::Action, super::dispatcher_spec::State)
{
    super::dispatcher_spec::feed(crate::auth::examples::crypto(), crate::auth::examples::verifier(), flight_ciphers(), s, input)
}

/// What an action sends, if it is `Send`.
pub open spec fn sent(action: super::dispatcher_spec::Action) -> Seq<u8> {
    match action { super::dispatcher_spec::Action::Send(wire) => wire, _ => seq![] }
}

/// The state after the server's Finished: the client flight is waiting.
pub open spec fn awaiting(ccs_pending: bool) -> super::dispatcher_spec::State {
    fed(before_finished(ccs_pending), record_of(finished(), 22)).2
}

/// The acknowledgement over the fixtures.
pub open spec fn acked(s: super::dispatcher_spec::State, wire: Seq<u8>)
    -> (super::dispatcher_spec::Action, super::dispatcher_spec::State)
{
    super::dispatcher_spec::acknowledge(crate::auth::examples::crypto(), crate::auth::examples::verifier(),
        flight_ciphers(), s, wire)
}

} // verus!
