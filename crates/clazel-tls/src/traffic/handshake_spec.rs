//! RFC 8446 (August 2018) §7.1/§7.3: bind handshake secrets to record directions.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-7.3>.
//!
//! Modelling choices:
//! - Reuse the Hello join's checked key exchange and exact transcript/offer
//!   capture. Derive the client sender and server receiver before starting Auth.
//! - This is a consuming key/state handoff, not a socket driver. The later
//!   driver must feed receiver plaintext through reassembly/Auth, fragment and
//!   send the client's exact flight, propagate fatal errors to both epochs,
//!   handle compatibility CCS, and install application keys at the proper
//!   message boundaries. Encryptor alone does not enforce application gating.
//! - No production AEAD, transport, timing or erasure claim is introduced.
//!   Private scalar ownership stays with the caller. RFC equations have no
//!   numbered steps.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Auth state, client send epoch, server receive epoch and application master secret.
pub type Handoff = (crate::auth::spec::State, super::spec::State, super::spec::State, Seq<u8>);
/// §7.1/§7.3: use the client secret for writing and the server secret for reading.
pub open spec fn start(c: crate::schedule::spec::Crypto, k: crate::hello::join_spec::KeyExchange,
    config: crate::hello::client_spec::Config, transcript: crate::transcript::spec::State,
    peer_key: Seq<u8>, private_key: Seq<u8>) -> Result<Handoff, u8>
{
    match crate::hello::join_spec::derive(c, k, config, transcript, peer_key, private_key) {
        Err(alert) => Err(alert),
        Ok((auth_config, master)) => {
            match super::spec::start(c, auth_config.client_secret) {
                Err(alert) => Err(alert),
                Ok(sender) => match super::spec::start(c, auth_config.server_secret) {
                    Err(alert) => Err(alert),
                    Ok(receiver) => match crate::auth::spec::start(auth_config, transcript) {
                        Err(alert) => Err(alert),
                        Ok(auth) => Ok((auth, sender, receiver, master)),
                    },
                },
            }
        },
    }
}
} // verus!
