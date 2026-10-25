//! Contracts for the owned Hello-to-authentication key-exchange join.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// The Hello controller establishes these facts before key derivation.
pub open spec fn established_wf(config: super::client_spec::Config,
    transcript: crate::transcript::spec::State, peer_key: Seq<u8>) -> bool
{
    super::client_spec::config_ok(config) && crate::transcript::spec::wf(transcript)
        && transcript.phase == crate::transcript::spec::Phase::Handshake && peer_key.len() == 32
}
/// Exact key/target/offer/transcript binding, preserving the authentication invariant.
pub open spec fn into_auth_ensures(c: crate::schedule::spec::Crypto, k: super::join_spec::KeyExchange,
    config: super::client_spec::Config, transcript: crate::transcript::spec::State,
    peer_key: Seq<u8>, private_key: Seq<u8>, out: Result<(crate::auth::spec::State, Seq<u8>), u8>) -> bool
{
    out == super::join_spec::into_auth(c, k, config, transcript, peer_key, private_key)
        && match out { Ok((auth, master)) => crate::auth::contract::exec_wf(auth) && master.len() == 32,
            Err(_) => true }
}
} // verus!
