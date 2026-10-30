//! RFC 8446 §7.3: handshake record-direction binding, with concrete witnesses.
//! Fixture crypto/key agreement come from hello::client_examples; they make no
//! cryptographic claim and deliberately distinguish client/server labels.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Installing record keys preserves the existing authentication handoff exactly.
pub proof fn lemma_direction_binding(c: crate::schedule::spec::Crypto, k: crate::hello::join_spec::KeyExchange,
    config: crate::hello::client_spec::Config, transcript: crate::transcript::spec::State,
    peer_key: Seq<u8>, private_key: Seq<u8>, auth: crate::auth::spec::State,
    sender: super::spec::State, receiver: super::spec::State, master: Seq<u8>)
    requires super::handshake_spec::start(c, k, config, transcript, peer_key, private_key) == Ok((auth, sender, receiver, master)),
    ensures crate::hello::join_spec::into_auth(c, k, config, transcript, peer_key, private_key) == Ok((auth, master)),
        super::spec::start(c, auth.config.client_secret) == Ok(sender),
        super::spec::start(c, auth.config.server_secret) == Ok(receiver),
{}
/// Fixture handoff: client/server traffic secrets 25/9 produce write keys 114/98.
pub open spec fn handoff() -> super::handshake_spec::Handoff {
    super::handshake_spec::start(crate::hello::client_examples::crypto(), crate::hello::client_examples::exchange(),
        crate::hello::client_examples::config(), crate::hello::client_examples::transcript(),
        Seq::new(32, |i: int| 17u8), Seq::new(32, |i: int| 5u8)).unwrap()
}
/// §7.3 client_write_key uses client_handshake_traffic_secret, not the server's.
pub proof fn lemma_client_write_key()
    ensures handoff().1.key == Seq::new(32, |i: int| 114u8),
{
    assert(handoff().1.key == Seq::new(32, |i: int| 114u8)) by (compute_only);
}
/// §7.3 server_write_key decrypts records received by the client.
pub proof fn lemma_server_read_key()
    ensures handoff().2.key == Seq::new(32, |i: int| 98u8),
{
    assert(handoff().2.key == Seq::new(32, |i: int| 98u8)) by (compute_only);
}
} // verus!
