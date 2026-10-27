//! RFC 8446 (August 2018) §4.1.2, §4.1.4, §4.2 and §4.4.1:
//! the initial ClientHello and the cookie-only retry exchange.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-4.1.2>.
//!
//! Modelling choices:
//! - Fixed TLS 1.3, ChaCha20-Poly1305/SHA-256 and X25519 profile, matching
//!   hello::spec. No PSK, early data, ALPN, padding or client identity.
//! - Entropy, the clock, canonical host and an X25519 public input are
//!   explicit configuration. Entropy sourcing remains external; the key-
//!   exchange join checks the private/public binding after this controller.
//! - send_sni is supplied by the URL layer (DNS host versus IP address).
//!   The captured host is retained unchanged for future certificate checks.
//! - Caller entropy/random and public input are exactly 32 bytes. Session ID
//!   is at most 32 bytes; a nonempty ID requests middlebox compatibility.
//!   The record driver must implement Appendix D.4's dummy CCS rules later.
//! - Signature schemes include TLS 1.3 schemes and RSA PKCS#1 for certificate
//!   signatures only. The auth machine already excludes PKCS#1 in CV.
//!   rsa_pss_pss_* (0x0809-0x080b, certificates with an RSASSA-PSS key) are
//!   not offered: verifying them needs an RFC 4055 RSASSA-PSS-params parser,
//!   and we offer only what the signature verifier accepts.
//! - HRR cookie extension_data is capped at 4098 bytes (4096-byte cookie),
//!   a resource policy, so ClientHello2's extension vector stays representable.
//! - The controller is consumed on receive. A fatal error discards it;
//!   success returns a new retry controller or the established parameters.
//!   There is no clone/recovery operation after failure or establishment.
//! - Transport fragmentation, record authentication and exact-send ordering
//!   remain the record driver's responsibility. It must send each returned
//!   flight before receiving the next server Hello. Outputs are handshake
//!   encodings; transcript inputs are bodies. RFC prose has no step numbers.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Maximum retained cookie extension_data, a local resource policy.
pub const MAX_COOKIE: usize = 4098;
/// Captured configuration; a production key-exchange join supplies the share.
pub struct Config {
    /// Canonical target identity for later authentication.
    pub host: Seq<u8>,
    /// Captured validity-check time.
    pub now: u64,
    /// Fresh random from the entropy source.
    pub random: Seq<u8>,
    /// Legacy session identifier; empty disables middlebox compatibility.
    pub session_id: Seq<u8>,
    /// X25519 public input, not a shared secret.
    pub public_key: Seq<u8>,
    /// Whether the URL layer classified the target as a DNS name.
    pub send_sni: bool,
}
/// Local inputs representable by this client profile.
pub open spec fn config_ok(c: Config) -> bool {
    1 <= c.host.len() <= 253 && c.random.len() == 32
        && c.session_id.len() <= 32 && c.public_key.len() == 32
}
/// §4.2.3: schemes offered for CV and certificate signatures.
pub open spec fn signatures() -> Seq<u16> {
    seq![0x0403u16, 0x0804u16, 0x0805u16, 0x0806u16, 0x0807u16,
        0x0401u16, 0x0501u16, 0x0601u16]
}
/// §4.2.2: an absent initial cookie or a structurally valid bounded retry cookie.
pub open spec fn cookie_ok(cookie: Seq<u8>) -> bool {
    cookie.len() == 0 || (cookie.len() <= MAX_COOKIE && crate::spec::read_cookie(cookie) is Some)
}
/// §4.2, RFC 6066 §3: the exact ordered extensions put on the wire.
pub open spec fn extensions(c: Config, cookie: Seq<u8>) -> Seq<crate::spec::Ext> {
    (if c.send_sni { seq![crate::spec::Ext { etype: 0,
        data: crate::spec::write_server_name_ch(seq![crate::spec::ServerName { host_name: c.host }]) }] }
        else { seq![] })
    + seq![crate::spec::Ext { etype: 43, data: seq![2u8, 3u8, 4u8] },
        crate::spec::Ext { etype: 13, data: crate::spec::write_signature_schemes(signatures()) },
        crate::spec::Ext { etype: 10, data: seq![0u8, 2u8, 0u8, 29u8] },
        crate::spec::Ext { etype: 51, data: crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: c.public_key }]) }]
    + (if cookie.len() == 0 { seq![] } else { seq![crate::spec::Ext { etype: 44, data: cookie }] })
}
/// §4.1.2: stable fields across initial and retry ClientHello; only cookie changes.
pub open spec fn client_hello(c: Config, cookie: Seq<u8>) -> crate::spec::ClientHello {
    crate::spec::ClientHello { legacy_version: 0x0303, random: c.random,
        session_id: c.session_id, cipher_suites: seq![0x1303u16], compression: seq![0u8],
        extensions: extensions(c, cookie) }
}
/// §4.1.2: the ClientHello body, without its handshake header.
pub open spec fn body(c: Config, cookie: Seq<u8>) -> Seq<u8> {
    crate::spec::write_client_hello(client_hello(c, cookie))
}
/// A pending exchange binds validation to exactly the session/profile emitted.
pub struct State {
    /// Original configuration, never changed during retry.
    pub config: Config,
    /// Initial CH or message_hash/HRR/CH2 prefix.
    pub transcript: crate::transcript::spec::State,
}
/// Only a first or second server Hello can be received here.
pub open spec fn wf(s: State) -> bool {
    config_ok(s.config) && crate::transcript::spec::wf(s.transcript)
        && (s.transcript.phase == crate::transcript::spec::Phase::FirstServerHello
            || s.transcript.phase == crate::transcript::spec::Phase::SecondServerHello)
}
/// Initial output: retain exactly the body whose handshake encoding is sent.
pub open spec fn start(c: Config) -> Result<(State, Seq<u8>), u8> {
    if !config_ok(c) { Err(80) }
    else {
        let b = body(c, seq![]);
        match crate::transcript::spec::start(b) {
            Err(_) => Err(80),
            Ok(transcript) => Ok((State { config: c, transcript }, crate::spec::write_handshake(1, b))),
        }
    }
}
/// Consuming receive either yields the next flight or completes Hello negotiation.
pub enum Outcome {
    /// Original configuration and rewritten transcript, with exact CH2 encoding.
    Retry(State, Seq<u8>),
    /// Final SH prefix and exact selected raw X25519 input; not authentication.
    Established(Config, crate::transcript::spec::State, Seq<u8>),
}
/// §4.1.4/§4.4.1: record HRR, build only the permitted update, then record CH2.
pub open spec fn retry(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, server: Seq<u8>, cookie: Seq<u8>) -> Result<Outcome, u8> {
    if !cookie_ok(cookie) { Err(80) }
    else {
        match crate::transcript::spec::step(hash, s.transcript, crate::transcript::spec::Kind::HelloRetryRequest, server) {
            Err(_) => Err(80),
            Ok(t) => {
                let b = body(s.config, cookie);
                match crate::transcript::spec::step(hash, t, crate::transcript::spec::Kind::ClientHello, b) {
                    Err(_) => Err(80),
                    Ok(transcript) => Ok(Outcome::Retry(State { config: s.config, transcript }, crate::spec::write_handshake(1, b))),
                }
            },
        }
    }
}
/// §4.1.3/§4.4.1: only accepted final SH parameters enter the transcript.
pub open spec fn established(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, server: Seq<u8>, key: Seq<u8>) -> Result<Outcome, u8> {
    match crate::transcript::spec::step(hash, s.transcript, crate::transcript::spec::Kind::ServerHello, server) {
        Err(_) => Err(80),
        Ok(transcript) => Ok(Outcome::Established(s.config, transcript, key)),
    }
}
/// §4.1.3/§4.1.4: session/retry validation uses retained, not caller-supplied state.
pub open spec fn receive(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, server: Seq<u8>) -> Result<Outcome, u8> {
    match super::spec::validate(s.config.session_id, s.transcript.retried, server) {
        Err(alert) => Err(alert),
        Ok(super::spec::Selection::Share(key)) => established(hash, s, server, key),
        Ok(super::spec::Selection::Retry(cookie)) => retry(hash, s, server, cookie),
    }
}
} // verus!
