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

} // verus!
