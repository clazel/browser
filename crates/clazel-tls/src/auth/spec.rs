//! RFC 8446 (August 2018) §4.3, §4.4 and Appendix A.1: the client's
//! certificate-authentication flight after the final ServerHello.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-4.4>.
//!
//! Modelling choices:
//! - Start with the negotiated handshake secrets and the transcript through
//!   ServerHello. ClientHello/ServerHello negotiation and record I/O are a
//!   separate layer, not established by this authentication machine.
//! - Complete handshake bodies come from the existing reassembler. Alerts,
//!   TCP fragmentation and AEAD authentication are handled by the record layer.
//! - SHA-256, no PSK/early data, no client identity. A CertificateRequest is
//!   answered with an empty Certificate and Finished, never CertificateVerify.
//! - Only server_name and supported_groups responses are negotiated in EE;
//!   the ClientHello profile offers no other EE features (no ALPN or early data).
//! - Chain/name/time validation and signature verification are parameters.
//!   A successful chain result is an opaque end-entity verification key.
//!   No X.509 implementation, crypto axiom or production provider is added.
//! - The clock and target host are captured at start. The validator's pure
//!   functions capture the trust store. Signature algorithms are strictly
//!   restricted to the client's offered, supported TLS 1.3 algorithms.
//! - A SendFinished acknowledgement means the I/O driver sent the exact
//!   pending handshake flight. Application delivery also waits for this ack.
//! - KeyUpdate, tickets and post-handshake authentication are not dispatched
//!   here: this is the initial authentication flight and application gate.
//! - Limits are inherited from transcript and body parsing; key handles are
//!   at most 16 KiB, host identifiers at most 253 bytes, offers at most 64.
//! - RFC prose/equations have no numbered steps; comments name the clause.

use crate::schedule::spec as kdf;
use crate::spec::{Ext, HsMsg, Res};
use crate::transcript::spec as tr;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// Maximum opaque public verification-key representation.
pub const MAX_KEY: usize = 16384;
/// Peer certificate-validation outcomes (§6.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertificateError {
    /// Malformed or unacceptable certificate/key.
    BadCertificate,
    /// No acceptable trust anchor/path.
    UnknownCa,
    /// Certificate outside its validity interval.
    Expired,
    /// Unsupported certificate type/algorithm.
    Unsupported,
}
/// §6.2 certificate alerts, preserved from the chain validator.
pub open spec fn certificate_alert(error: CertificateError) -> u8 {
    match error {
        CertificateError::BadCertificate => 42,
        CertificateError::UnknownCa => 48,
        CertificateError::Expired => 45,
        CertificateError::Unsupported => 43,
    }
}
/// Pure verification parameters, not assumptions about real cryptography.
pub struct Verification {
    /// Validates chain, identity and time and returns the end-entity key.
    pub chain: spec_fn(Seq<u8>, u64, Seq<u8>) -> Result<Seq<u8>, CertificateError>,
    /// Verifies this signature with that end-entity key and TLS scheme.
    pub signature: spec_fn(Seq<u8>, u16, Seq<u8>, Seq<u8>) -> bool,
}
/// Stages of the certificate-based, non-PSK client flight (Appendix A.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Await EncryptedExtensions.
    EncryptedExtensions,
    /// CertificateRequest is optional, Certificate is mandatory.
    CertificateOrRequest,
    /// One request was received; the next message must be Certificate.
    Certificate,
    /// Chain accepted; require CertificateVerify.
    CertificateVerify,
    /// Chain and signature accepted; require server Finished.
    Finished,
    /// Server Finished accepted and client flight emitted; await I/O ack.
    SendFinished,
    /// Both Finished conditions met; application data may be delivered.
    Ready,
    /// Fatal failure, absorbing.
    Failed,
    /// Transport closed, absorbing.
    Closed,
}
/// Captured negotiation context; the Hello layer must supply the actual offers.
pub struct Config {
    /// Canonical host identity for certificate validation.
    pub host: Seq<u8>,
    /// Clock reading used by certificate validity policy.
    pub now: u64,
    /// Server handshake traffic secret (not the client secret).
    pub server_secret: Seq<u8>,
    /// Client handshake traffic secret.
    pub client_secret: Seq<u8>,
    /// Signature schemes from the actual ClientHello.
    pub signatures: Seq<u16>,
    /// Extension types from the actual ClientHello.
    pub extensions: Seq<u16>,
}
/// Authentication state. Check flags record successful validation transitions.
pub struct State {
    /// Immutable per-connection context.
    pub config: Config,
    /// Transcript owned by this machine through each accepted message.
    pub transcript: tr::State,
    /// Next protocol stage.
    pub phase: Phase,
    /// End-entity key returned by chain validation.
    pub key: Seq<u8>,
    /// The peer requested client authentication.
    pub requested: bool,
    /// Chain, name and time validation succeeded.
    pub chain_checked: bool,
    /// CertificateVerify passed with the validated end-entity key.
    pub signature_checked: bool,
    /// Server Finished matched the expected MAC over the current transcript.
    pub finished_checked: bool,
    /// The I/O driver acknowledged the exact emitted client flight.
    pub client_sent: bool,
    /// Transcript-Hash through server Finished, for application traffic secrets.
    pub application_hash: Seq<u8>,
}
/// Inputs from the record layer and I/O driver.
pub enum Input {
    /// A complete handshake body and its authenticated record-layer type.
    Handshake(u8, Seq<u8>),
    /// Application plaintext from authenticated record decryption.
    Application(Seq<u8>),
    /// The pending client Finished flight was sent successfully.
    SentFinished,
    /// Transport close.
    Closed,
    /// I/O failure.
    Error,
}
/// One ordered effect; Send is acknowledged before Ready/application delivery.
pub enum Action {
    /// No I/O effect.
    None,
    /// Handshake encodings to protect with the client handshake key and send.
    Send(Seq<u8>),
    /// Handshake authentication completed.
    Ready,
    /// Authenticated application plaintext released to the caller.
    Deliver(Seq<u8>),
    /// Fatal TLS alert description; the driver terminates the connection.
    Fail(u8),
    /// Close with no further delivery.
    Close,
}
/// Membership used for actual ClientHello offers (bounded by Config policy).
pub open spec fn member(values: Seq<u16>, value: u16) -> bool
    decreases values.len(),
{
    values.len() > 0 && (values[0] == value || member(values.skip(1), value))
}
/// This client's extension-offer profile; no feature-bearing EE extensions.
pub open spec fn profile_extensions(es: Seq<u16>) -> bool
    decreases es.len(),
{
    es.len() == 0 || ((es[0] == 0 || es[0] == 10 || es[0] == 13 || es[0] == 43
        || es[0] == 44 || es[0] == 50 || es[0] == 51) && profile_extensions(es.skip(1)))
}
/// §4.4.3: permitted TLS 1.3 schemes in the selected library profile.
pub open spec fn signature_scheme(scheme: u16) -> bool {
    scheme == 0x0403 || scheme == 0x0804 || scheme == 0x0805 || scheme == 0x0806
        || scheme == 0x0807 || scheme == 0x0809 || scheme == 0x080a || scheme == 0x080b
}
/// §4.2: EE responses must have been offered. Placement/body rules are parsed first.
pub open spec fn extensions_offered(es: Seq<Ext>, offers: Seq<u16>) -> bool
    decreases es.len(),
{
    es.len() == 0 || (member(offers, es[0].etype) && extensions_offered(es.skip(1), offers))
}
/// Captured parameter bounds and supported profile.
pub open spec fn config_ok(c: Config) -> bool {
    0 < c.host.len() <= 253 && c.server_secret.len() == 32 && c.client_secret.len() == 32
        && 0 < c.signatures.len() <= 64 && c.extensions.len() <= 64 && profile_extensions(c.extensions)
}
/// Authentication gate invariant; no claim about the validator's cryptography.
pub open spec fn wf(s: State) -> bool {
    config_ok(s.config) && tr::wf(s.transcript) && s.transcript.phase == tr::Phase::Handshake
        && s.key.len() <= MAX_KEY
        && (s.signature_checked ==> s.chain_checked)
        && (s.finished_checked ==> s.chain_checked && s.signature_checked)
        && (s.client_sent ==> s.finished_checked)
        && (s.phase == Phase::CertificateVerify ==> s.chain_checked)
        && (s.phase == Phase::Finished ==> s.chain_checked && s.signature_checked)
        && (s.phase == Phase::SendFinished ==> s.finished_checked)
        && (s.phase == Phase::Ready ==> s.finished_checked && s.client_sent)
}
/// Begin after the Hello layer supplied its negotiated secrets and transcript.
pub open spec fn start(config: Config, transcript: tr::State) -> Result<State, u8> {
    if !config_ok(config) || !tr::wf(transcript) || transcript.phase != tr::Phase::Handshake {
        Err(crate::spec::INTERNAL_ERROR)
    } else {
        Ok(State { config, transcript, phase: Phase::EncryptedExtensions, key: Seq::empty(),
            requested: false, chain_checked: false, signature_checked: false,
            finished_checked: false, client_sent: false, application_hash: Seq::empty() })
    }
}
/// Fatal errors are absorbing; no later input can revive this state.
pub open spec fn fail(s: State, alert: u8) -> (State, Action) {
    (State { phase: Phase::Failed, ..s }, Action::Fail(alert))
}
/// Append exactly one accepted handshake encoding, enforcing the transcript bound.
pub open spec fn record(c: kdf::Crypto, s: State, kind: tr::Kind, body: Seq<u8>, phase: Phase) -> (State, Action) {
    match tr::step(c.hash, s.transcript, kind, body) {
        Ok(transcript) => (State { transcript, phase, ..s }, Action::None),
        Err(_) => fail(s, crate::spec::INTERNAL_ERROR),
    }
}
/// §4.4.2: an empty client Certificate has zero-length context and certificate_list.
pub open spec fn empty_certificate() -> Seq<u8> { seq![0u8, 0u8, 0u8, 0u8] }
/// §4.4.4: verify the server before building or sending any client handshake flight.
pub open spec fn accept_finished(c: kdf::Crypto, s: State, verify_data: Seq<u8>) -> (State, Action) {
    if verify_data != kdf::finished(c, s.config.server_secret, s.transcript.messages) {
        fail(s, crate::spec::DECRYPT_ERROR)
    } else {
        let (s1, a1) = record(c, State { finished_checked: true, ..s }, tr::Kind::Finished, verify_data, Phase::SendFinished);
        if a1 is Fail { (s1, a1) } else {
            let s1 = State { application_hash: (c.hash)(s1.transcript.messages), ..s1 };
            let (s2, a2) = if s1.requested {
                record(c, s1, tr::Kind::Certificate, empty_certificate(), Phase::SendFinished)
            } else { (s1, Action::None) };
            if a2 is Fail { (s2, a2) } else {
                let own = kdf::finished(c, s2.config.client_secret, s2.transcript.messages);
                let (s3, a3) = record(c, s2, tr::Kind::Finished, own, Phase::SendFinished);
                if a3 is Fail { (s3, a3) } else {
                    let certificate = if s3.requested { crate::spec::write_handshake(11, empty_certificate()) } else { Seq::empty() };
                    (s3, Action::Send(certificate + crate::spec::write_handshake(20, own)))
                }
            }
        }
    }
}
/// §4.3/§4.4: parse and authenticate a complete initial-flight handshake body.
pub open spec fn receive(c: kdf::Crypto, v: Verification, s: State, typ: u8, body: Seq<u8>) -> (State, Action) {
    if body.len() > tr::MAX_BODY { fail(s, crate::spec::INTERNAL_ERROR) } else {
        match crate::spec::parse_handshake_body(typ, body, 32) {
            Res::Err(error) => fail(s, crate::spec::alert_for(error).description),
            Res::Ok(message) => match message {
                HsMsg::EncryptedExtensions(es) => {
                    if s.phase != Phase::EncryptedExtensions { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
                    else if !extensions_offered(es, s.config.extensions) { fail(s, crate::spec::UNSUPPORTED_EXTENSION) }
                    else { record(c, s, tr::Kind::EncryptedExtensions, body, Phase::CertificateOrRequest) }
                },
                HsMsg::CertificateRequest(request) => {
                    if s.phase != Phase::CertificateOrRequest { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
                    else if request.context.len() != 0 { fail(s, crate::spec::ILLEGAL_PARAMETER) }
                    else if !crate::spec::has_ext(request.extensions, 13) { fail(s, crate::spec::MISSING_EXTENSION) }
                    else { record(c, State { requested: true, ..s }, tr::Kind::CertificateRequest, body, Phase::Certificate) }
                },
                HsMsg::Certificate(certificate) => {
                    if s.phase != Phase::CertificateOrRequest && s.phase != Phase::Certificate { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
                    else if certificate.entries.len() == 0 { fail(s, crate::spec::DECODE_ERROR) }
                    else {
                        match (v.chain)(s.config.host, s.config.now, body) {
                            Err(error) => fail(s, certificate_alert(error)),
                            Ok(key) => {
                                if key.len() > MAX_KEY { fail(s, crate::spec::INTERNAL_ERROR) }
                                else { record(c, State { key, chain_checked: true, ..s }, tr::Kind::Certificate, body, Phase::CertificateVerify) }
                            },
                        }
                    }
                },
                HsMsg::CertificateVerify(cv) => {
                    if s.phase != Phase::CertificateVerify { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
                    else if !signature_scheme(cv.algorithm) || !member(s.config.signatures, cv.algorithm) { fail(s, crate::spec::ILLEGAL_PARAMETER) }
                    else {
                        let input = tr::certificate_verify_input(true, (c.hash)(s.transcript.messages));
                        if !(v.signature)(s.key, cv.algorithm, input, cv.signature) { fail(s, crate::spec::DECRYPT_ERROR) }
                        else { record(c, State { signature_checked: true, ..s }, tr::Kind::CertificateVerify, body, Phase::Finished) }
                    }
                },
                HsMsg::Finished(verify_data) => {
                    if s.phase != Phase::Finished { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
                    else { accept_finished(c, s, verify_data) }
                },
                _ => fail(s, crate::spec::UNEXPECTED_MESSAGE),
            },
        }
    }
}
/// Appendix A.1 initial-flight client effects and the application-data gate.
pub open spec fn step(c: kdf::Crypto, v: Verification, s: State, input: Input) -> (State, Action) {
    if s.phase == Phase::Failed || s.phase == Phase::Closed { (s, Action::None) }
    else {
        match input {
            Input::Closed => (State { phase: Phase::Closed, ..s }, Action::Close),
            Input::Error => fail(s, crate::spec::INTERNAL_ERROR),
            Input::SentFinished => {
                if s.phase == Phase::SendFinished { (State { phase: Phase::Ready, client_sent: true, ..s }, Action::Ready) }
                else { fail(s, crate::spec::INTERNAL_ERROR) }
            },
            Input::Application(bytes) => {
                if s.phase == Phase::Ready { (s, Action::Deliver(bytes)) }
                else { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
            },
            Input::Handshake(typ, body) => receive(c, v, s, typ, body),
        }
    }
}
} // verus!
