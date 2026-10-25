//! RFC 8446 §7.1/§7.4.2: parameterized X25519 and authentication handoff.
use super::client::Config;
use super::key_exchange::KeyExchange;
use crate::auth::exec::Auth;
use crate::schedule::crypto::Crypto;
use crate::schedule::spec::Label;
use crate::transcript::exec::Transcript;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// RFC 8446 §7.4.2: inspect every shared-secret byte for an all-zero result.
/// This functional proof does not establish compiled-code timing properties.
pub fn nonzero(bytes: &[u8]) -> (out: bool)
    ensures out == super::join_spec::nonzero(bytes@),
{
    let mut found = false;
    let mut i = 0;
    while i < bytes.len()
        invariant i <= bytes.len(), found == (exists|j: int| 0 <= j < i && #[trigger] bytes@[j] != 0),
        decreases bytes.len() - i,
    {
        let byte = match bytes.get(i) { Some(b) => *b, None => return found };
        let ghost before = i;
        found |= byte != 0;
        i = i.saturating_add(1);
        proof {
            if byte != 0 { assert(bytes@[before as int] != 0); }
            assert forall|j: int| 0 <= j < i && #[trigger] bytes@[j] != 0
                implies j < before || j == before by {}
        }
    }
    proof { super::client_lemmas::lemma_nonzero_exists(bytes@); }
    found
}
/// Actual offered extension types, including the cookie added in ClientHello2.
pub fn extension_types(config: &Config, retried: bool) -> (out: Vec<u16>)
    ensures out@ == super::join_spec::extension_types(config@, retried),
{
    let mut out = super::client::extension_types(config);
    if retried { out.push(44); }
    proof { assert(out@ =~= super::join_spec::extension_types(config@, retried)); }
    out
}
/// View of an authentication machine and retained application master secret.
pub open spec fn result_view(out: Result<(Auth, Vec<u8>), u8>) -> Result<(crate::auth::spec::State, Seq<u8>), u8> {
    match out { Err(e) => Err(e), Ok((auth, master)) => Ok((auth@, master@)) }
}
/// View of derived authentication configuration and master secret.
pub open spec fn derived_view(out: Result<(crate::auth::exec::Config, Vec<u8>), u8>) -> Result<(crate::auth::spec::Config, Seq<u8>), u8> {
    match out { Err(e) => Err(e), Ok((config, master)) => Ok((config@, master@)) }
}
/// §7.1/§7.4.2: derive the same checked inputs for authentication and records.
pub fn derive<C: Crypto, K: KeyExchange>(config: Config, transcript: &Transcript,
    peer_key: Vec<u8>, crypto: &C, exchange: &K, private_key: &[u8]) -> (out: Result<(crate::auth::exec::Config, Vec<u8>), u8>)
    requires super::join_contract::established_wf(config@, transcript@, peer_key@),
    ensures super::join_contract::derive_ensures(crypto.functions(), exchange.functions(),
        config@, transcript@, peer_key@, private_key@, derived_view(out)),
{
    if private_key.len() != 32 { return Err(80); }
    let public_key = exchange.public_key(private_key);
    if !crate::handshake::bytes_eq(public_key.as_slice(), config.public_key.as_slice()) { return Err(80); }
    let shared = match exchange.shared_secret(private_key, peer_key.as_slice()) {
        Some(s) => s,
        None => return Err(47),
    };
    if !nonzero(shared.as_slice()) { return Err(47); }
    let early = crate::schedule::exec::early_secret(crypto);
    let handshake = crate::schedule::exec::handshake_secret(crypto, early.as_slice(), shared.as_slice());
    let master = crate::schedule::exec::master_secret(crypto, handshake.as_slice());
    let server_secret = crate::schedule::exec::derive_secret(crypto, handshake.as_slice(), Label::ServerHandshake, transcript.messages());
    let client_secret = crate::schedule::exec::derive_secret(crypto, handshake.as_slice(), Label::ClientHandshake, transcript.messages());
    let signatures = super::client::signatures();
    let extensions = extension_types(&config, transcript.retried());
    let auth_config = crate::auth::exec::Config { host: config.host, now: config.now,
        server_secret, client_secret, signatures, extensions };
    Ok((auth_config, master))
}
/// §7.1/§4.4: transfer checked secrets and the exact prefix into authentication.
pub fn into_auth<C: Crypto, K: KeyExchange>(config: Config, transcript: Transcript,
    peer_key: Vec<u8>, crypto: &C, exchange: &K, private_key: &[u8]) -> (out: Result<(Auth, Vec<u8>), u8>)
    requires super::join_contract::established_wf(config@, transcript@, peer_key@),
    ensures super::join_contract::into_auth_ensures(crypto.functions(), exchange.functions(),
        config@, transcript@, peer_key@, private_key@, result_view(out)),
{
    let (auth_config, master) = derive(config, &transcript, peer_key, crypto, exchange, private_key)?;
    match Auth::start(auth_config, transcript) { Err(e) => Err(e), Ok(auth) => Ok((auth, master)) }
}

} // verus!
