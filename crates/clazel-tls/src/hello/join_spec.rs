//! RFC 8446 (August 2018) §7.1/§7.4.2: Hello-to-authentication handoff.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-7.4.2>.
//!
//! Modelling choices:
//! - X25519 is a provider parameter with explicit private/public inputs;
//!   no production crypto implementation or security axiom is introduced.
//! - The retained public share must equal public_key(private_key). Local
//!   mismatches are internal_error. Rejected/zero shared secrets use
//!   illegal_parameter, the chosen fatal alert for an invalid DH exchange.
//! - Reject an all-zero *shared secret*, not a zero raw peer public input.
//!   Functional proofs make no timing or secret-erasure claim.
//! - The caller owns the private scalar until this consuming handoff. It
//!   must supply fresh entropy and immutable providers in production.
//! - The auth machine starts waiting for EncryptedExtensions; this handoff
//!   does not authenticate the peer. Its chain/signature providers and the
//!   record-I/O driver remain separate. RFC equations have no step numbers.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Public-key derivation parameter with an explicit private scalar.
pub type PublicKey = spec_fn(Seq<u8>) -> Seq<u8>;
/// Shared-secret parameter with explicit private and peer public inputs.
pub type SharedSecret = spec_fn(Seq<u8>, Seq<u8>) -> Option<Seq<u8>>;
/// Pure X25519 provider functions; successful outputs are checked by the trait.
pub struct KeyExchange {
    /// Public input derived from the exact private scalar.
    pub public_key: PublicKey,
    /// Shared secret from the exact private scalar and received peer public input.
    pub shared_secret: SharedSecret,
}
/// Functional all-zero rejection (§7.4.2).
pub open spec fn nonzero(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    bytes.len() > 0 && (bytes.last() != 0 || nonzero(bytes.drop_last()))
}
/// Actual extension types in the final sent ClientHello, including any HRR cookie.
pub open spec fn extension_types(c: super::client_spec::Config, retried: bool) -> Seq<u16> {
    (if c.send_sni { seq![0u16] } else { seq![] }) + seq![43u16, 13u16, 10u16, 51u16]
        + (if retried { seq![44u16] } else { seq![] })
}
/// §7.1: both handshake traffic secrets share exactly the final-SH prefix.
pub open spec fn auth_config(c: crate::schedule::spec::Crypto, config: super::client_spec::Config,
    transcript: crate::transcript::spec::State, handshake: Seq<u8>) -> crate::auth::spec::Config
{
    crate::auth::spec::Config { host: config.host, now: config.now,
        server_secret: crate::schedule::spec::derive_secret(c, handshake, crate::schedule::spec::Label::ServerHandshake, transcript.messages),
        client_secret: crate::schedule::spec::derive_secret(c, handshake, crate::schedule::spec::Label::ClientHandshake, transcript.messages),
        signatures: super::client_spec::signatures(), extensions: extension_types(config, transcript.retried) }
}
/// §7.1 and §7.4.2: bind keys, derive non-PSK secrets, and transfer ownership.
pub open spec fn into_auth(c: crate::schedule::spec::Crypto, k: KeyExchange,
    config: super::client_spec::Config, transcript: crate::transcript::spec::State,
    peer_key: Seq<u8>, private_key: Seq<u8>) -> Result<(crate::auth::spec::State, Seq<u8>), u8>
{
    if private_key.len() != 32 || (k.public_key)(private_key) != config.public_key { Err(80) }
    else {
        match (k.shared_secret)(private_key, peer_key) {
            None => Err(47),
            Some(shared) => if shared.len() != 32 || !nonzero(shared) { Err(47) }
                else {
                    let early = crate::schedule::spec::early_secret(c);
                    let handshake = crate::schedule::spec::handshake_secret(c, early, shared);
                    let master = crate::schedule::spec::master_secret(c, handshake);
                    match crate::auth::spec::start(auth_config(c, config, transcript, handshake), transcript) {
                        Err(alert) => Err(alert),
                        Ok(auth) => Ok((auth, master)),
                    }
                },
        }
    }
}
} // verus!
