//! RFC 8446 §4.3/§4.4 authentication effects over explicit verification providers.
//! This module owns the authentication transcript and application-delivery gate.
use super::spec::{CertificateError, MAX_KEY, Phase};
use super::verify::Verifier;
use crate::schedule::crypto::Crypto;
use crate::transcript::exec::Transcript;
use crate::transcript::spec::Kind;
use crate::types::{Extension, HsMsg};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// RFC 8446 §4.3.2: the initial server CertificateRequest has an empty context.
fn initial_request_context_valid(context: &[u8]) -> (result: bool)
    ensures result == super::spec::initial_request_context_valid(context@),
{
    context.is_empty()
}
/// RFC 8446 §4.4.2: the initial server Certificate uses an empty context.
fn initial_certificate_context_valid(context: &[u8]) -> (result: bool)
    ensures result == super::spec::initial_certificate_context_valid(context@),
{
    context.is_empty()
}

/// The actual offers, target and traffic secrets supplied by the Hello layer.
pub struct Config {
    /// Canonical host identity passed unchanged to certificate validation.
    pub host: Vec<u8>,
    /// Captured validity-check time.
    pub now: u64,
    /// Negotiated server handshake traffic secret.
    pub server_secret: Vec<u8>,
    /// Negotiated client handshake traffic secret.
    pub client_secret: Vec<u8>,
    /// Signature schemes in the actual ClientHello.
    pub signatures: Vec<u16>,
    /// Extension types in the actual ClientHello.
    pub extensions: Vec<u16>,
}
impl View for Config {
    type V = super::spec::Config;
    open spec fn view(&self) -> super::spec::Config {
        super::spec::Config { host: self.host@, now: self.now, server_secret: self.server_secret@,
            client_secret: self.client_secret@, signatures: self.signatures@, extensions: self.extensions@ }
    }
}
/// Initial certificate-authentication machine. No production verifier is bundled.
pub struct Auth {
    config: Config,
    transcript: Transcript,
    phase: Phase,
    key: Vec<u8>,
    requested: bool,
    chain_checked: bool,
    signature_checked: bool,
    finished_checked: bool,
    client_sent: bool,
    application_hash: Vec<u8>,
}
impl View for Auth {
    type V = super::spec::State;
    closed spec fn view(&self) -> super::spec::State {
        super::spec::State { config: self.config@, transcript: self.transcript@, phase: self.phase,
            key: self.key@, requested: self.requested, chain_checked: self.chain_checked,
            signature_checked: self.signature_checked, finished_checked: self.finished_checked,
            client_sent: self.client_sent, application_hash: self.application_hash@ }
    }
}
/// Complete, decrypted record-layer inputs and the exact-send acknowledgement.
#[derive(Debug)]
pub enum Input<'a> {
    /// One complete handshake body and its HandshakeType, after record deprotection.
    Handshake(u8, &'a [u8]),
    /// Decrypted application plaintext.
    Application(&'a [u8]),
    /// Driver sent the exact pending client Finished flight.
    SentFinished,
    /// Transport closed.
    Closed,
    /// I/O failed.
    Error,
}
impl<'a> View for Input<'a> {
    type V = super::spec::Input;
    open spec fn view(&self) -> super::spec::Input {
        match self {
            Input::Handshake(t, b) => super::spec::Input::Handshake(*t, b@),
            Input::Application(b) => super::spec::Input::Application(b@),
            Input::SentFinished => super::spec::Input::SentFinished,
            Input::Closed => super::spec::Input::Closed,
            Input::Error => super::spec::Input::Error,
        }
    }
}
/// Ordered effect of one authentication input.
#[derive(Debug, PartialEq, Eq)]
pub enum Action {
    /// No effect.
    None,
    /// Protect and send these handshake encodings with the client handshake key.
    Send(Vec<u8>),
    /// Initial authentication complete.
    Ready,
    /// Authenticated application plaintext.
    Deliver(Vec<u8>),
    /// Fatal TLS alert description; terminate the connection.
    Fail(u8),
    /// Close the connection.
    Close,
}
impl View for Action {
    type V = super::spec::Action;
    open spec fn view(&self) -> super::spec::Action {
        match self {
            Action::None => super::spec::Action::None,
            Action::Send(b) => super::spec::Action::Send(b@),
            Action::Ready => super::spec::Action::Ready,
            Action::Deliver(b) => super::spec::Action::Deliver(b@),
            Action::Fail(a) => super::spec::Action::Fail(*a),
            Action::Close => super::spec::Action::Close,
        }
    }
}
/// View of fallible construction.
pub open spec fn start_view(result: Result<Auth, u8>) -> Result<super::spec::State, u8> {
    match result { Ok(s) => Ok(s@), Err(e) => Err(e) }
}

/// Exact membership in the actual ClientHello offers (§4.2/§4.4.3).
pub fn member(values: &[u16], value: u16) -> (out: bool)
    ensures out == super::spec::member(values@, value),
{
    let mut i: usize = 0;
    proof { assert(values@.skip(0) =~= values@); }
    while i < values.len()
        invariant i <= values.len(), super::spec::member(values@, value) == super::spec::member(values@.skip(i as int), value),
        decreases values.len() - i,
    {
        let current = match values.get(i) { Some(&v) => v, None => { proof { assert(false); } return false; } };
        proof { assert(values@.skip(i as int)[0] == current); }
        if current == value { return true; }
        proof { assert(values@.skip(i as int).skip(1) =~= values@.skip(i as int + 1)); }
        i = i.saturating_add(1);
    }
    proof { assert(values@.skip(i as int) =~= Seq::<u16>::empty()); }
    false
}
/// Supported extension-offer profile; feature-bearing EE negotiation is excluded.
pub fn profile_extensions(values: &[u16]) -> (out: bool)
    ensures out == super::spec::profile_extensions(values@),
{
    let mut i: usize = 0;
    proof { assert(values@.skip(0) =~= values@); }
    while i < values.len()
        invariant i <= values.len(), super::spec::profile_extensions(values@) == super::spec::profile_extensions(values@.skip(i as int)),
        decreases values.len() - i,
    {
        let t = match values.get(i) { Some(&v) => v, None => { proof { assert(false); } return false; } };
        proof { assert(values@.skip(i as int)[0] == t); }
        if !(t == 0 || t == 10 || t == 13 || t == 43 || t == 44 || t == 50 || t == 51) { return false; }
        proof { assert(values@.skip(i as int).skip(1) =~= values@.skip(i as int + 1)); }
        i = i.saturating_add(1);
    }
    proof { assert(values@.skip(i as int) =~= Seq::<u16>::empty()); }
    true
}
/// RFC 8446 §4.4.3: no SHA-1/PKCS#1 v1.5 CertificateVerify schemes.
pub fn signature_scheme(scheme: u16) -> (out: bool)
    ensures out == super::spec::signature_scheme(scheme),
{
    scheme == 0x0403 || scheme == 0x0804 || scheme == 0x0805 || scheme == 0x0806
        || scheme == 0x0807
}
/// RFC 8446 §4.2: every parsed server response answers an actual offer.
pub fn extensions_offered(es: &[Extension<'_>], offers: &[u16]) -> (out: bool)
    ensures out == super::spec::extensions_offered(crate::types::views(es@), offers@),
{
    let mut i: usize = 0;
    let ghost all = crate::types::views(es@);
    proof { assert(all.skip(0) =~= all); }
    while i < es.len()
        invariant i <= es.len(), all == crate::types::views(es@),
            super::spec::extensions_offered(all, offers@) == super::spec::extensions_offered(all.skip(i as int), offers@),
        decreases es.len() - i,
    {
        let e = match es.get(i) { Some(e) => e, None => { proof { assert(false); } return false; } };
        proof { assert(all.skip(i as int)[0] == e@); }
        if !member(offers, e.etype) { return false; }
        proof { assert(all.skip(i as int).skip(1) =~= all.skip(i as int + 1)); }
        i = i.saturating_add(1);
    }
    proof { assert(all.skip(i as int) =~= Seq::<crate::spec::Ext>::empty()); }
    true
}
/// RFC 8446 §4.4.2: every CertificateEntry's extensions answer an actual offer.
pub fn certificate_extensions_offered(entries: &[crate::types::CertificateEntry<'_>], offers: &[u16]) -> (out: bool)
    ensures out == super::spec::certificate_extensions_offered(crate::types::views(entries@), offers@),
{
    let mut i: usize = 0;
    let ghost all = crate::types::views(entries@);
    proof { assert(all.skip(0) =~= all); }
    while i < entries.len()
        invariant i <= entries.len(), all == crate::types::views(entries@),
            super::spec::certificate_extensions_offered(all, offers@) == super::spec::certificate_extensions_offered(all.skip(i as int), offers@),
        decreases entries.len() - i,
    {
        let entry = match entries.get(i) { Some(entry) => entry, None => { proof { assert(false); } return false; } };
        proof { assert(all.skip(i as int)[0] == entry@); }
        if !extensions_offered(entry.extensions.as_slice(), offers) { return false; }
        proof { assert(all.skip(i as int).skip(1) =~= all.skip(i as int + 1)); }
        i = i.saturating_add(1);
    }
    proof { assert(all.skip(i as int) =~= Seq::<crate::spec::CertificateEntry>::empty()); }
    true
}
/// RFC 8446 §6.2: typed certificate-validation alert mapping.
pub fn certificate_alert(error: CertificateError) -> (out: u8)
    ensures out == super::spec::certificate_alert(error),
{
    match error {
        CertificateError::BadCertificate => 42,
        CertificateError::UnknownCa => 48,
        CertificateError::Expired => 45,
        CertificateError::Unsupported => 43,
    }
}

impl Auth {
    /// The invariant established at start and preserved by every public step.
    pub open spec fn wf(&self) -> bool { super::contract::exec_wf(self@) }

    /// Start after final ServerHello with the Hello layer's actual offers/secrets.
    pub fn start(config: Config, transcript: Transcript) -> (out: Result<Self, u8>)
        requires crate::transcript::spec::wf(transcript@),
        ensures super::contract::start_ensures(config@, transcript@, start_view(out)),
    {
        if config.host.is_empty() || config.host.len() > 253 || config.server_secret.len() != 32
            || config.client_secret.len() != 32 || config.signatures.is_empty() || config.signatures.len() > 64
            || config.extensions.len() > 64 || !profile_extensions(config.extensions.as_slice())
        { return Err(crate::spec::INTERNAL_ERROR); }
        let phase = transcript.phase();
        if !matches!(phase, crate::transcript::spec::Phase::Handshake) { return Err(crate::spec::INTERNAL_ERROR); }
        Ok(Auth { config, transcript, phase: Phase::EncryptedExtensions, key: Vec::new(), requested: false,
            chain_checked: false, signature_checked: false, finished_checked: false, client_sent: false,
            application_hash: Vec::new() })
    }
    /// Current authentication stage (not just transcript bookkeeping).
    pub fn phase(&self) -> (out: Phase) ensures out == self@.phase { self.phase }
    /// Exact transcript currently owned by this machine.
    pub fn messages(&self) -> (out: &[u8]) ensures out@ == self@.transcript.messages { self.transcript.messages() }
    /// Hash through server Finished, captured before any client Certificate/Finished.
    pub fn application_hash(&self) -> (out: &[u8]) ensures out@ == self@.application_hash { self.application_hash.as_slice() }

    fn fail(&mut self, alert: u8) -> (out: Action)
        ensures (final(self)@, out@) == super::spec::fail(old(self)@, alert),
    {
        self.phase = Phase::Failed;
        Action::Fail(alert)
    }
    fn record<C: Crypto>(&mut self, crypto: &C, kind: Kind, body: &[u8], phase: Phase) -> (out: Action)
        requires crate::transcript::spec::wf(old(self)@.transcript),
            old(self)@.transcript.phase == crate::transcript::spec::Phase::Handshake,
        ensures (final(self)@, out@) == super::spec::record(crypto.functions(), old(self)@, kind, body@, phase),
            crate::transcript::spec::wf(final(self)@.transcript),
            final(self)@.transcript.phase == crate::transcript::spec::Phase::Handshake,
    {
        match self.transcript.push(crypto, kind, body) {
            Ok(()) => { self.phase = phase; Action::None },
            Err(_) => self.fail(crate::spec::INTERNAL_ERROR),
        }
    }
    fn on_extensions<C: Crypto>(&mut self, crypto: &C, body: &[u8], es: &[Extension<'_>]) -> (out: Action)
        requires old(self).wf(),
        ensures (final(self)@, out@) == super::spec::on_extensions(crypto.functions(), old(self)@, body@, crate::types::views(es@)),
            final(self).wf(),
    {
        if !matches!(self.phase, Phase::EncryptedExtensions) { return self.fail(crate::spec::UNEXPECTED_MESSAGE); }
        if !extensions_offered(es, self.config.extensions.as_slice()) { return self.fail(crate::spec::UNSUPPORTED_EXTENSION); }
        self.record(crypto, Kind::EncryptedExtensions, body, Phase::CertificateOrRequest)
    }
    fn on_request<C: Crypto>(&mut self, crypto: &C, body: &[u8], empty_context: bool, has_algorithms: bool) -> (out: Action)
        requires old(self).wf(),
        ensures (final(self)@, out@) == super::spec::on_request(crypto.functions(), old(self)@, body@, empty_context, has_algorithms),
            final(self).wf(),
    {
        if !matches!(self.phase, Phase::CertificateOrRequest) { return self.fail(crate::spec::UNEXPECTED_MESSAGE); }
        if !empty_context { return self.fail(crate::spec::ILLEGAL_PARAMETER); }
        if !has_algorithms { return self.fail(crate::spec::MISSING_EXTENSION); }
        self.requested = true;
        self.record(crypto, Kind::CertificateRequest, body, Phase::Certificate)
    }
    fn on_certificate<C: Crypto, V: Verifier>(&mut self, crypto: &C, verifier: &V, body: &[u8], empty_context: bool, empty_chain: bool, entries_offered: bool) -> (out: Action)
        requires old(self).wf(),
        ensures (final(self)@, out@) == super::spec::on_certificate(crypto.functions(), verifier.functions(), old(self)@, body@, empty_context, empty_chain, entries_offered),
            final(self).wf(),
    {
        if !matches!(self.phase, Phase::CertificateOrRequest | Phase::Certificate) { return self.fail(crate::spec::UNEXPECTED_MESSAGE); }
        if !empty_context { return self.fail(crate::spec::ILLEGAL_PARAMETER); }
        if empty_chain { return self.fail(crate::spec::DECODE_ERROR); }
        if !entries_offered { return self.fail(crate::spec::UNSUPPORTED_EXTENSION); }
        let key = match verifier.chain(self.config.host.as_slice(), self.config.now, body) {
            Ok(key) => key,
            Err(error) => { let alert = certificate_alert(error); return self.fail(alert); },
        };
        if key.len() > MAX_KEY { return self.fail(crate::spec::INTERNAL_ERROR); }
        self.key = key;
        self.chain_checked = true;
        self.record(crypto, Kind::Certificate, body, Phase::CertificateVerify)
    }
    fn on_verify<C: Crypto, V: Verifier>(&mut self, crypto: &C, verifier: &V, body: &[u8], algorithm: u16, signature: &[u8]) -> (out: Action)
        requires old(self).wf(),
        ensures (final(self)@, out@) == super::spec::on_verify(crypto.functions(), verifier.functions(), old(self)@, body@, algorithm, signature@),
            final(self).wf(),
    {
        if !matches!(self.phase, Phase::CertificateVerify) { return self.fail(crate::spec::UNEXPECTED_MESSAGE); }
        if !signature_scheme(algorithm) || !member(self.config.signatures.as_slice(), algorithm) { return self.fail(crate::spec::ILLEGAL_PARAMETER); }
        let hash = self.transcript.hash(crypto);
        let input = crate::transcript::exec::certificate_verify_input(true, hash.as_slice());
        if !verifier.signature(self.key.as_slice(), algorithm, input.as_slice(), signature) { return self.fail(crate::spec::DECRYPT_ERROR); }
        self.signature_checked = true;
        self.record(crypto, Kind::CertificateVerify, body, Phase::Finished)
    }
    fn accept_finished<C: Crypto, V: Verifier>(&mut self, crypto: &C, verifier: &V, verify_data: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self)@.phase == Phase::Finished, verify_data.len() == 32,
        ensures (final(self)@, out@) == super::spec::accept_finished(crypto.functions(), old(self)@, verify_data@),
            final(self).wf(),
    {
        let expected = crate::schedule::exec::finished(crypto, self.config.server_secret.as_slice(), self.transcript.messages());
        if !verifier.finished_equal(verify_data, expected.as_slice()) { return self.fail(crate::spec::DECRYPT_ERROR); }
        self.finished_checked = true;
        let a1 = self.record(crypto, Kind::Finished, verify_data, Phase::SendFinished);
        if matches!(a1, Action::Fail(_)) { return a1; }
        self.application_hash = self.transcript.hash(crypto);
        let mut flight = Vec::new();
        let empty: &[u8] = &[0u8, 0u8, 0u8, 0u8];
        proof { assert(empty@ =~= super::spec::empty_certificate()); }
        if self.requested {
            let a2 = self.record(crypto, Kind::Certificate, empty, Phase::SendFinished);
            if matches!(a2, Action::Fail(_)) { return a2; }
            crate::encode::write_handshake(&mut flight, 11, empty);
        }
        let own = crate::schedule::exec::finished(crypto, self.config.client_secret.as_slice(), self.transcript.messages());
        let a3 = self.record(crypto, Kind::Finished, own.as_slice(), Phase::SendFinished);
        if matches!(a3, Action::Fail(_)) { return a3; }
        crate::encode::write_handshake(&mut flight, 20, own.as_slice());
        Action::Send(flight)
    }
    fn dispatch<C: Crypto, V: Verifier>(&mut self, crypto: &C, verifier: &V, body: &[u8], message: HsMsg<'_>) -> (out: Action)
        requires old(self).wf(),
        ensures (final(self)@, out@) == super::spec::dispatch(crypto.functions(), verifier.functions(), old(self)@, body@, message@),
            final(self).wf(),
    {
        match message {
            HsMsg::EncryptedExtensions(es) => self.on_extensions(crypto, body, es.as_slice()),
            HsMsg::CertificateRequest(request) => {
                let present = crate::extension::has_ext(request.extensions.as_slice(), 13);
                self.on_request(crypto, body, initial_request_context_valid(request.context), present)
            },
            HsMsg::Certificate(certificate) => {
                let offered = certificate_extensions_offered(certificate.entries.as_slice(), self.config.extensions.as_slice());
                self.on_certificate(crypto, verifier, body,
                    initial_certificate_context_valid(certificate.context), certificate.entries.is_empty(), offered)
            },
            HsMsg::CertificateVerify(cv) => self.on_verify(crypto, verifier, body, cv.algorithm, cv.signature),
            HsMsg::Finished(verify_data) => {
                if !matches!(self.phase, Phase::Finished) { self.fail(crate::spec::UNEXPECTED_MESSAGE) }
                else if verify_data.len() != 32 { self.fail(crate::spec::DECODE_ERROR) }
                else { self.accept_finished(crypto, verifier, verify_data) }
            },
            _ => self.fail(crate::spec::UNEXPECTED_MESSAGE),
        }
    }
    fn receive<C: Crypto, V: Verifier>(&mut self, crypto: &C, verifier: &V, typ: u8, body: &[u8]) -> (out: Action)
        requires old(self).wf(),
        ensures (final(self)@, out@) == super::spec::receive(crypto.functions(), verifier.functions(), old(self)@, typ, body@),
            final(self).wf(),
    {
        hide(crate::spec::parse_handshake_body);
        if body.len() > crate::transcript::spec::MAX_BODY { return self.fail(crate::spec::INTERNAL_ERROR); }
        let message = match crate::handshake::parse_handshake_body(typ, body, 32) {
            Ok(m) => m,
            Err(error) => { let alert = crate::encode::alert_for(error); return self.fail(alert.description); },
        };
        self.dispatch(crypto, verifier, body, message)
    }
    /// RFC 8446 Appendix A.1 and §4.4.4: ordered authentication effects.
    /// The caller must acknowledge the exact Send flight before supplying SentFinished.
    pub fn step<C: Crypto, V: Verifier>(&mut self, crypto: &C, verifier: &V, input: Input<'_>) -> (out: Action)
        requires old(self).wf(),
        ensures super::contract::step_ensures(crypto.functions(), verifier.functions(), old(self)@, input@, final(self)@, out@),
    {
        hide(super::spec::receive);
        hide(super::spec::dispatch);
        hide(crate::spec::parse_handshake_body);
        if matches!(self.phase, Phase::Failed | Phase::Closed) { return Action::None; }
        match input {
            Input::Closed => { self.phase = Phase::Closed; Action::Close },
            Input::Error => self.fail(crate::spec::INTERNAL_ERROR),
            Input::SentFinished => {
                if matches!(self.phase, Phase::SendFinished) {
                    self.phase = Phase::Ready;
                    self.client_sent = true;
                    Action::Ready
                } else { self.fail(crate::spec::INTERNAL_ERROR) }
            },
            Input::Application(bytes) => {
                if matches!(self.phase, Phase::Ready) {
                    let mut out = Vec::new(); out.extend_from_slice(bytes);
                    proof { assert(out@ =~= bytes@); }
                    Action::Deliver(out)
                } else { self.fail(crate::spec::UNEXPECTED_MESSAGE) }
            },
            Input::Handshake(typ, body) => self.receive(crypto, verifier, typ, body),
        }
    }
}
} // verus!
