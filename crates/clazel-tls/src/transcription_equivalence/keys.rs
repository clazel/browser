//! RFC 8446 §7.1, §7.4.2 and §4.4.4 at the points where the handshake uses
//! them: `hello/join_spec.rs`'s `derive` (the X25519 shared secret, its
//! all-zero check, the handshake traffic secrets and the master secret), the
//! server and client Finished of `auth/spec.rs`'s `accept_finished`, and
//! the application traffic secrets of `connection/dispatcher_spec.rs`'s
//! `acknowledge`, proven equal to what the clean-room transcription's
//! `state_machine::accept_server_hello` and `receive_finished` compute, for
//! every transcript, key and secret: [`theorem_handshake_keys_equivalence`].
//!
//! How the two are related:
//! - The crate's transcript state stands for the transcription's message list
//!   and retry flag ([`super::transcript::represents`]), so a secret derived
//!   from the crate's bytes is the transcription's derived from the list.
//! - X25519. The crate's provider is two functions, `public_key(private)` and
//!   `shared_secret(private, peer)`, the second partial; the transcription's
//!   is one total function `x25519(scalar, u)`. They agree when
//!   `shared_secret(private, peer) == Some(x25519(private, peer))` and
//!   `public_key(private) == x25519(private, basepoint)` ([`x25519_agrees`]),
//!   and X25519's outputs are 32 bytes (RFC 7748; both sides model it so).
//! - Local consistency the transcription presumes: the crate refuses, with
//!   `internal_error`, a private key that is not 32 bytes or whose public key
//!   is not the one the ClientHello offered. The transcription holds the
//!   private key of the share it offered by construction, so it has no such
//!   failure; the theorem assumes the crate's caller is consistent the same
//!   way.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The crate's X25519 provider is the transcription's `x25519`.
pub open spec fn x25519_agrees(k: crate::hello::join_spec::KeyExchange, p: crate::transcription::primitives::Primitives) -> bool {
    &&& forall|private: Seq<u8>, peer: Seq<u8>|
        #[trigger] (k.shared_secret)(private, peer) == Some((p.x25519)(private, peer))
    &&& forall|private: Seq<u8>|
        #[trigger] (k.public_key)(private) == (p.x25519)(private, crate::transcription::primitives::x25519_basepoint())
    &&& forall|private: Seq<u8>, peer: Seq<u8>| #[trigger] (p.x25519)(private, peer).len() == 32
}

/// §7.4.2: the crate's `nonzero` is the negation of the transcription's
/// `all_zero`.
pub proof fn lemma_nonzero(bytes: Seq<u8>)
    ensures crate::hello::join_spec::nonzero(bytes) == !crate::transcription::presentation::all_zero(bytes),
    decreases bytes.len(),
{
    lemma_all_zero_iff(bytes);
    lemma_nonzero_iff(bytes);
}

/// `all_zero` is "every byte is zero".
pub proof fn lemma_all_zero_iff(bytes: Seq<u8>)
    ensures crate::transcription::presentation::all_zero(bytes) <==> forall|i: int| 0 <= i < bytes.len() ==> bytes[i] == 0,
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        let tail = bytes.subrange(1, bytes.len() as int);
        lemma_all_zero_iff(tail);
        if crate::transcription::presentation::all_zero(bytes) {
            assert forall|i: int| 0 <= i < bytes.len() implies bytes[i] == 0 by {
                if i > 0 { assert(bytes[i] == tail[i - 1]); }
            }
        } else if bytes[0] == 0 {
            let j = choose|j: int| 0 <= j < tail.len() && tail[j] != 0;
            assert(bytes[j + 1] != 0);
        }
    }
}

/// `nonzero` is "some byte is not zero".
pub proof fn lemma_nonzero_iff(bytes: Seq<u8>)
    ensures crate::hello::join_spec::nonzero(bytes) <==> exists|i: int| 0 <= i < bytes.len() && bytes[i] != 0,
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        let d = bytes.drop_last();
        lemma_nonzero_iff(d);
        if crate::hello::join_spec::nonzero(bytes) {
            if bytes.last() == 0 {
                let j = choose|j: int| 0 <= j < d.len() && d[j] != 0;
                assert(bytes[j] != 0);
            } else {
                assert(bytes[bytes.len() - 1] != 0);
            }
        } else {
            assert forall|i: int| 0 <= i < bytes.len() implies bytes[i] == 0 by {
                if i < bytes.len() - 1 { assert(bytes[i] == d[i]); }
            }
        }
    }
}

/// §7.1 Derive-Secret over the crate's transcript bytes is the
/// transcription's over the list they stand for, retried or not.
pub proof fn lemma_derive_on_transcript(c: crate::schedule::spec::Crypto, p: crate::transcription::primitives::Primitives,
    secret: Seq<u8>, label: crate::schedule::spec::Label, s: crate::transcript::spec::State, messages: Seq<Seq<u8>>, retried: bool)
    requires
        super::schedule::crypto_agrees(c, p),
        super::transcript::hash_is_32(p.hash),
        super::transcript::represents(p, s, messages, retried),
    ensures
        crate::schedule::spec::derive_secret(c, secret, label, s.messages)
            == crate::transcription::key_schedule::derive_secret(p, secret, super::schedule::transcription_label(label), messages, retried),
        crate::schedule::spec::finished(c, secret, s.messages)
            == crate::transcription::authentication::verify_data(p, secret, messages, retried),
        crate::schedule::spec::expand_label(c, secret, label, (c.hash)(s.messages), 32)
            == crate::transcription::key_schedule::derive_secret(p, secret, super::schedule::transcription_label(label), messages, retried),
{
    super::schedule::theorem_schedule_equivalence(c, p);
    super::transcript::theorem_transcript_equivalence(p);
    assert((p.hash)(s.messages) == crate::transcription::authentication::transcript_hash(p, messages, retried));
    assert(crate::schedule::spec::expand_label(c, secret, label, (c.hash)(s.messages), 32)
        == crate::transcription::key_schedule::hkdf_expand_label(p, secret, super::schedule::transcription_label(label), (c.hash)(s.messages), 32));
    assert(crate::schedule::spec::expand_label(c, secret, crate::schedule::spec::Label::Finished, seq![], 32)
        == crate::transcription::authentication::finished_key(p, secret));
}

/// RFC 8446 §7.1, §7.4.2 and §4.4.4, for every offer, transcript, key and
/// secret:
/// - `join_spec::derive` refuses exactly when the transcription's
///   `accept_server_hello` aborts for an all-zero shared secret, with the
///   same alert; otherwise its handshake traffic secrets and master secret
///   are the transcription's;
/// - the server Finished the crate expects, and the client Finished it sends,
///   are the transcription's `verify_data` over the same transcript;
/// - the application traffic secrets the dispatcher derives from the hash
///   through the server Finished are the transcription's.
pub proof fn theorem_handshake_keys_equivalence(c: crate::schedule::spec::Crypto, k: crate::hello::join_spec::KeyExchange,
    p: crate::transcription::primitives::Primitives)
    requires
        super::schedule::crypto_agrees(c, p),
        super::transcript::hash_is_32(p.hash),
        x25519_agrees(k, p),
    ensures
        forall|config: crate::hello::client_spec::Config, s: crate::transcript::spec::State, messages: Seq<Seq<u8>>,
            retried: bool, peer: Seq<u8>, private: Seq<u8>|
            #[trigger] super::transcript::represents(p, s, messages, retried) && private.len() == 32
                && (k.public_key)(private) == config.public_key ==> {
                let shared = (p.x25519)(private, peer);
                let handshake = crate::transcription::key_schedule::handshake_secret(p,
                    crate::transcription::key_schedule::early_secret(p, crate::transcription::primitives::zero_value()), shared);
                match #[trigger] crate::hello::join_spec::derive(c, k, config, s, peer, private) {
                    Err(alert) => crate::transcription::presentation::all_zero(shared)
                        && alert as nat == crate::transcription::alerts::required_alert(
                            crate::transcription::alerts::ClientError::SharedSecretAllZero),
                    Ok((auth, master)) => !crate::transcription::presentation::all_zero(shared)
                        && auth.server_secret == crate::transcription::key_schedule::server_handshake_traffic_secret(p, handshake, messages, retried)
                        && auth.client_secret == crate::transcription::key_schedule::client_handshake_traffic_secret(p, handshake, messages, retried)
                        && master == crate::transcription::key_schedule::master_secret(p, handshake),
                }
            },
        forall|secret: Seq<u8>, s: crate::transcript::spec::State, messages: Seq<Seq<u8>>, retried: bool|
            #[trigger] super::transcript::represents(p, s, messages, retried) ==>
                #[trigger] crate::schedule::spec::finished(c, secret, s.messages)
                    == crate::transcription::authentication::verify_data(p, secret, messages, retried),
        forall|master: Seq<u8>, s: crate::transcript::spec::State, messages: Seq<Seq<u8>>, retried: bool|
            #[trigger] super::transcript::represents(p, s, messages, retried) ==> {
                &&& #[trigger] crate::schedule::spec::expand_label(c, master, crate::schedule::spec::Label::ClientApplication, (c.hash)(s.messages), 32)
                    == crate::transcription::key_schedule::client_application_traffic_secret_0(p, master, messages, retried)
                &&& crate::schedule::spec::expand_label(c, master, crate::schedule::spec::Label::ServerApplication, (c.hash)(s.messages), 32)
                    == crate::transcription::key_schedule::server_application_traffic_secret_0(p, master, messages, retried)
            },
{
    super::schedule::theorem_schedule_equivalence(c, p);
    assert forall|config: crate::hello::client_spec::Config, s: crate::transcript::spec::State, messages: Seq<Seq<u8>>,
        retried: bool, peer: Seq<u8>, private: Seq<u8>|
        #[trigger] super::transcript::represents(p, s, messages, retried) && private.len() == 32
            && (k.public_key)(private) == config.public_key implies {
            let shared = (p.x25519)(private, peer);
            let handshake = crate::transcription::key_schedule::handshake_secret(p,
                crate::transcription::key_schedule::early_secret(p, crate::transcription::primitives::zero_value()), shared);
            match #[trigger] crate::hello::join_spec::derive(c, k, config, s, peer, private) {
                Err(alert) => crate::transcription::presentation::all_zero(shared)
                    && alert as nat == crate::transcription::alerts::required_alert(
                        crate::transcription::alerts::ClientError::SharedSecretAllZero),
                Ok((auth, master)) => !crate::transcription::presentation::all_zero(shared)
                    && auth.server_secret == crate::transcription::key_schedule::server_handshake_traffic_secret(p, handshake, messages, retried)
                    && auth.client_secret == crate::transcription::key_schedule::client_handshake_traffic_secret(p, handshake, messages, retried)
                    && master == crate::transcription::key_schedule::master_secret(p, handshake),
            }
        }
    by {
        let shared = (p.x25519)(private, peer);
        assert((k.shared_secret)(private, peer) == Some(shared));
        lemma_nonzero(shared);
        let early = crate::schedule::spec::early_secret(c);
        let handshake = crate::schedule::spec::handshake_secret(c, early, shared);
        lemma_derive_on_transcript(c, p, handshake, crate::schedule::spec::Label::ServerHandshake, s, messages, retried);
        lemma_derive_on_transcript(c, p, handshake, crate::schedule::spec::Label::ClientHandshake, s, messages, retried);
    }
    assert forall|secret: Seq<u8>, s: crate::transcript::spec::State, messages: Seq<Seq<u8>>, retried: bool|
        #[trigger] super::transcript::represents(p, s, messages, retried) implies
            #[trigger] crate::schedule::spec::finished(c, secret, s.messages)
                == crate::transcription::authentication::verify_data(p, secret, messages, retried)
    by {
        lemma_derive_on_transcript(c, p, secret, crate::schedule::spec::Label::Finished, s, messages, retried);
    }
    assert forall|master: Seq<u8>, s: crate::transcript::spec::State, messages: Seq<Seq<u8>>, retried: bool|
        #[trigger] super::transcript::represents(p, s, messages, retried) implies {
            &&& #[trigger] crate::schedule::spec::expand_label(c, master, crate::schedule::spec::Label::ClientApplication, (c.hash)(s.messages), 32)
                == crate::transcription::key_schedule::client_application_traffic_secret_0(p, master, messages, retried)
            &&& crate::schedule::spec::expand_label(c, master, crate::schedule::spec::Label::ServerApplication, (c.hash)(s.messages), 32)
                == crate::transcription::key_schedule::server_application_traffic_secret_0(p, master, messages, retried)
        }
    by {
        lemma_derive_on_transcript(c, p, master, crate::schedule::spec::Label::ClientApplication, s, messages, retried);
        lemma_derive_on_transcript(c, p, master, crate::schedule::spec::Label::ServerApplication, s, messages, retried);
    }
}

} // verus!
