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
//!   Certificate entry extensions follow the same offered-type rule; the
//!   profile offers neither status_request nor signed_certificate_timestamp,
//!   so a server chain must carry none.
//! - Chain/name/time validation and signature verification are parameters.
//!   A successful chain result is an opaque end-entity verification key.
//!   No X.509 implementation, crypto axiom or production provider is added.
//! - The clock and target host are captured at start. The host is typed
//!   (`crate::host::spec::Host`, a DNS name or an IP address; design Q2),
//!   so the validator receives the reference identity's type and never
//!   re-parses host text. The validator's pure functions capture the trust
//!   store. Signature algorithms are strictly
//!   restricted to the client's offered, supported TLS 1.3 algorithms.
//! - A SendFinished acknowledgement means the I/O driver sent the exact
//!   pending handshake flight. Application delivery also waits for this ack.
//! - KeyUpdate, tickets and post-handshake authentication are not dispatched
//!   here: this is the initial authentication flight and application gate.
//! - Limits are inherited from transcript and body parsing; key handles are
//!   at most 16 KiB, hosts as `crate::host::spec::host_ok` bounds them,
//!   offers at most 64.
//! - RFC prose/equations have no numbered steps; comments name the clause.

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
/// Chain/name/time validation parameter: the typed target host (the
/// reference identity, design Q2), the captured clock in Unix seconds and
/// the Certificate message body (§4.4.2), returning an opaque end-entity key.
pub type ChainValidation = spec_fn(crate::host::spec::Host, u64, Seq<u8>) -> Result<Seq<u8>, CertificateError>;
/// Signature-verification parameter bound to an end-entity key and TLS scheme.
pub type SignatureVerification = spec_fn(Seq<u8>, u16, Seq<u8>, Seq<u8>) -> bool;
/// Pure verification parameters, not assumptions about real cryptography.
pub struct Verification {
    /// Validates chain, identity and time and returns the end-entity key.
    pub chain: ChainValidation,
    /// Verifies this signature with that end-entity key and TLS scheme.
    pub signature: SignatureVerification,
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
    /// The typed target host, for certificate validation (design Q2).
    pub host: crate::host::spec::Host,
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
    pub transcript: crate::transcript::spec::State,
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
    /// A complete handshake body and its HandshakeType, after record-layer authentication.
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
/// §4.4.3: permitted TLS 1.3 schemes in the selected library profile:
/// ecdsa_secp256r1_sha256, rsa_pss_rsae_sha256/384/512 and ed25519. The
/// rsa_pss_pss_* schemes are not offered (see hello::client_spec).
pub open spec fn signature_scheme(scheme: u16) -> bool {
    scheme == 0x0403 || scheme == 0x0804 || scheme == 0x0805 || scheme == 0x0806
        || scheme == 0x0807
}
/// §4.2: EE responses must have been offered. Placement/body rules are parsed first.
pub open spec fn extensions_offered(es: Seq<crate::spec::Ext>, offers: Seq<u16>) -> bool
    decreases es.len(),
{
    es.len() == 0 || (member(offers, es[0].etype) && extensions_offered(es.skip(1), offers))
}
/// §4.4.2: "extensions in the Certificate message from the server MUST
/// correspond to ones from the ClientHello message", the same offered-type
/// rule as EncryptedExtensions, applied to every CertificateEntry.
pub open spec fn certificate_extensions_offered(entries: Seq<crate::spec::CertificateEntry>, offers: Seq<u16>) -> bool
    decreases entries.len(),
{
    entries.len() == 0 || (extensions_offered(entries[0].extensions, offers)
        && certificate_extensions_offered(entries.skip(1), offers))
}
/// Captured parameter bounds and supported profile.
pub open spec fn config_ok(c: Config) -> bool {
    crate::host::spec::host_ok(c.host) && c.server_secret.len() == 32 && c.client_secret.len() == 32
        && 0 < c.signatures.len() <= 64 && c.extensions.len() <= 64 && profile_extensions(c.extensions)
}
/// Authentication gate invariant; no claim about the validator's cryptography.
pub open spec fn wf(s: State) -> bool {
    config_ok(s.config) && crate::transcript::spec::wf(s.transcript) && s.transcript.phase == crate::transcript::spec::Phase::Handshake
        && s.key.len() <= MAX_KEY
        && (s.signature_checked ==> s.chain_checked)
        && (s.finished_checked ==> s.chain_checked && s.signature_checked)
        && (s.client_sent ==> s.finished_checked)
        && (s.client_sent ==> s.phase == Phase::Ready || s.phase == Phase::Failed || s.phase == Phase::Closed)
        && (s.phase == Phase::CertificateVerify ==> s.chain_checked)
        && (s.phase == Phase::Finished ==> s.chain_checked && s.signature_checked)
        && (s.phase == Phase::SendFinished ==> s.finished_checked)
        && (s.phase == Phase::Ready ==> s.finished_checked && s.client_sent)
}
/// Begin after the Hello layer supplied its negotiated secrets and transcript.
pub open spec fn start(config: Config, transcript: crate::transcript::spec::State) -> Result<State, u8> {
    if !config_ok(config) || !crate::transcript::spec::wf(transcript) || transcript.phase != crate::transcript::spec::Phase::Handshake {
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
pub open spec fn record(c: crate::schedule::spec::Crypto, s: State, kind: crate::transcript::spec::Kind, body: Seq<u8>, phase: Phase) -> (State, Action) {
    match crate::transcript::spec::step(c.hash, s.transcript, kind, body) {
        Ok(transcript) => (State { transcript, phase, ..s }, Action::None),
        Err(_) => fail(s, crate::spec::INTERNAL_ERROR),
    }
}
/// §4.4.2: an empty client Certificate has zero-length context and certificate_list.
pub open spec fn empty_certificate() -> Seq<u8> { seq![0u8, 0u8, 0u8, 0u8] }
/// §4.4.4: verify the server before building or sending any client handshake flight.
pub open spec fn accept_finished(c: crate::schedule::spec::Crypto, s: State, verify_data: Seq<u8>) -> (State, Action) {
    if verify_data != crate::schedule::spec::finished(c, s.config.server_secret, s.transcript.messages) {
        fail(s, crate::spec::DECRYPT_ERROR)
    } else {
        let (s1, a1) = record(c, State { finished_checked: true, ..s }, crate::transcript::spec::Kind::Finished, verify_data, Phase::SendFinished);
        if a1 is Fail { (s1, a1) } else {
            let s1 = State { application_hash: (c.hash)(s1.transcript.messages), ..s1 };
            let (s2, a2) = if s1.requested {
                record(c, s1, crate::transcript::spec::Kind::Certificate, empty_certificate(), Phase::SendFinished)
            } else { (s1, Action::None) };
            if a2 is Fail { (s2, a2) } else {
                let own = crate::schedule::spec::finished(c, s2.config.client_secret, s2.transcript.messages);
                let (s3, a3) = record(c, s2, crate::transcript::spec::Kind::Finished, own, Phase::SendFinished);
                if a3 is Fail { (s3, a3) } else {
                    let certificate = if s3.requested { crate::spec::write_handshake(11, empty_certificate()) } else { Seq::empty() };
                    (s3, Action::Send(certificate + crate::spec::write_handshake(20, own)))
                }
            }
        }
    }
}
/// §4.3.1 and §4.2: accepted EncryptedExtensions must answer actual offers.
pub open spec fn on_extensions(c: crate::schedule::spec::Crypto, s: State, body: Seq<u8>, es: Seq<crate::spec::Ext>) -> (State, Action) {
    if s.phase != Phase::EncryptedExtensions { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
    else if !extensions_offered(es, s.config.extensions) { fail(s, crate::spec::UNSUPPORTED_EXTENSION) }
    else { record(c, s, crate::transcript::spec::Kind::EncryptedExtensions, body, Phase::CertificateOrRequest) }
}
/// RFC 8446 §4.3.2: an initial-handshake CertificateRequest uses empty context.
pub open spec fn initial_request_context_valid(context: Seq<u8>) -> bool {
    context.len() == 0
}
/// RFC 8446 §4.4.2: server Certificate uses empty context in initial auth.
pub open spec fn initial_certificate_context_valid(context: Seq<u8>) -> bool {
    context.len() == 0
}
/// §4.3.2: one initial CertificateRequest, with empty context and signature_algorithms.
pub open spec fn on_request(c: crate::schedule::spec::Crypto, s: State, body: Seq<u8>, empty_context: bool, has_algorithms: bool) -> (State, Action) {
    if s.phase != Phase::CertificateOrRequest { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
    else if !empty_context { fail(s, crate::spec::ILLEGAL_PARAMETER) }
    else if !has_algorithms { fail(s, crate::spec::MISSING_EXTENSION) }
    else { record(c, State { requested: true, ..s }, crate::transcript::spec::Kind::CertificateRequest, body, Phase::Certificate) }
}
/// §4.4.2: nonempty server chain whose entry extensions were all offered
/// (§4.2: an unsolicited one is aborted with unsupported_extension),
/// validated for this captured host and time.
pub open spec fn on_certificate(c: crate::schedule::spec::Crypto, v: Verification, s: State, body: Seq<u8>, empty_context: bool, empty_chain: bool, entries_offered: bool) -> (State, Action) {
    if s.phase != Phase::CertificateOrRequest && s.phase != Phase::Certificate { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
    else if !empty_context { fail(s, crate::spec::ILLEGAL_PARAMETER) }
    else if empty_chain { fail(s, crate::spec::DECODE_ERROR) }
    else if !entries_offered { fail(s, crate::spec::UNSUPPORTED_EXTENSION) }
    else {
        match (v.chain)(s.config.host, s.config.now, body) {
            Err(error) => fail(s, certificate_alert(error)),
            Ok(key) => {
                if key.len() > MAX_KEY { fail(s, crate::spec::INTERNAL_ERROR) }
                else { record(c, State { key, chain_checked: true, ..s }, crate::transcript::spec::Kind::Certificate, body, Phase::CertificateVerify) }
            },
        }
    }
}
/// §4.4.3: use the validated leaf key and the transcript through Certificate.
pub open spec fn on_verify(c: crate::schedule::spec::Crypto, v: Verification, s: State, body: Seq<u8>, algorithm: u16, signature: Seq<u8>) -> (State, Action) {
    if s.phase != Phase::CertificateVerify { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
    else if !signature_scheme(algorithm) || !member(s.config.signatures, algorithm) { fail(s, crate::spec::ILLEGAL_PARAMETER) }
    else {
        let input = crate::transcript::spec::certificate_verify_input(true, (c.hash)(s.transcript.messages));
        if !(v.signature)(s.key, algorithm, input, signature) { fail(s, crate::spec::DECRYPT_ERROR) }
        else { record(c, State { signature_checked: true, ..s }, crate::transcript::spec::Kind::CertificateVerify, body, Phase::Finished) }
    }
}
/// §4.3/§4.4: dispatch the actual parsed fields, with an explicit Finished-length guard.
pub open spec fn dispatch(c: crate::schedule::spec::Crypto, v: Verification, s: State, body: Seq<u8>, message: crate::spec::HsMsg) -> (State, Action) {
    match message {
        crate::spec::HsMsg::EncryptedExtensions(es) => on_extensions(c, s, body, es),
        crate::spec::HsMsg::CertificateRequest(request) => on_request(c, s, body, initial_request_context_valid(request.context), crate::spec::has_ext(request.extensions, 13)),
        crate::spec::HsMsg::Certificate(certificate) => on_certificate(c, v, s, body,
            initial_certificate_context_valid(certificate.context), certificate.entries.len() == 0,
            certificate_extensions_offered(certificate.entries, s.config.extensions)),
        crate::spec::HsMsg::CertificateVerify(cv) => on_verify(c, v, s, body, cv.algorithm, cv.signature),
        crate::spec::HsMsg::Finished(verify_data) => {
            if s.phase != Phase::Finished { fail(s, crate::spec::UNEXPECTED_MESSAGE) }
            else if verify_data.len() != 32 { fail(s, crate::spec::DECODE_ERROR) }
            else { accept_finished(c, s, verify_data) }
        },
        _ => fail(s, crate::spec::UNEXPECTED_MESSAGE),
    }
}
/// §4.3/§4.4: parse a complete body before authentication dispatch.
pub open spec fn receive(c: crate::schedule::spec::Crypto, v: Verification, s: State, typ: u8, body: Seq<u8>) -> (State, Action) {
    if body.len() > crate::transcript::spec::MAX_BODY { fail(s, crate::spec::INTERNAL_ERROR) } else {
        match crate::spec::parse_handshake_body(typ, body, 32) {
            crate::spec::Res::Err(error) => fail(s, crate::spec::alert_for(error).description),
            crate::spec::Res::Ok(message) => dispatch(c, v, s, body, message),
        }
    }
}
/// Appendix A.1 initial-flight client effects and the application-data gate.
pub open spec fn step(c: crate::schedule::spec::Crypto, v: Verification, s: State, input: Input) -> (State, Action) {
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
/// Finite authentication traces, for invariants over arbitrary peer/I/O inputs.
pub open spec fn run(c: crate::schedule::spec::Crypto, v: Verification, s: State, inputs: Seq<Input>) -> State
    decreases inputs.len(),
{
    if inputs.len() == 0 { s } else { run(c, v, step(c, v, s, inputs[0]).0, inputs.skip(1)) }
}
} // verus!
