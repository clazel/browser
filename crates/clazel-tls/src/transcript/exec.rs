//! Executable RFC 8446 §4.4.1 transcript construction and §4.4.3 signature input.
use super::spec::{Error, Kind, MAX_BODY, MAX_TRANSCRIPT, Phase};
use crate::schedule::crypto::Crypto;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// Retained handshake encodings. Construction and accepted pushes preserve wf.
/// Its Hello progression does not imply that a peer has been authenticated.
pub struct Transcript {
    messages: Vec<u8>,
    phase: Phase,
    retried: bool,
}

impl View for Transcript {
    type V = super::spec::State;
    closed spec fn view(&self) -> super::spec::State {
        super::spec::State { messages: self.messages@, phase: self.phase, retried: self.retried }
    }
}

/// View of a fallible accumulator construction.
pub open spec fn construction_view(result: Result<Transcript, Error>) -> Result<super::spec::State, Error> {
    match result { Ok(t) => Ok(t@), Err(e) => Err(e) }
}

/// RFC 8446 §4: handshake type, with HRR encoded as ServerHello (2).
pub fn wire_type(kind: Kind) -> (out: u8)
    ensures out == super::spec::wire_type(kind),
{
    match kind {
        Kind::ClientHello => 1,
        Kind::ServerHello | Kind::HelloRetryRequest => 2,
        Kind::EncryptedExtensions => 8,
        Kind::CertificateRequest => 13,
        Kind::Certificate => 11,
        Kind::CertificateVerify => 15,
        Kind::Finished => 20,
    }
}

/// RFC 8446 §4.1.4, §4.4.1: the Hello progression, with one retry at most.
pub fn next_phase(phase: Phase, kind: Kind) -> (out: Option<Phase>)
    ensures out == super::spec::next_phase(phase, kind),
{
    match phase {
        Phase::FirstServerHello => match kind {
            Kind::HelloRetryRequest => Some(Phase::SecondClientHello),
            Kind::ServerHello => Some(Phase::Handshake),
            _ => None,
        },
        Phase::SecondClientHello => match kind {
            Kind::ClientHello => Some(Phase::SecondServerHello),
            _ => None,
        },
        Phase::SecondServerHello => match kind {
            Kind::ServerHello => Some(Phase::Handshake),
            _ => None,
        },
        Phase::Handshake => match kind {
            Kind::EncryptedExtensions | Kind::CertificateRequest | Kind::Certificate
                | Kind::CertificateVerify | Kind::Finished => Some(Phase::Handshake),
            _ => None,
        },
    }
}

impl Transcript {
    /// RFC 8446 §4.4.1: begin with a ClientHello body and its handshake header.
    pub fn new(client_hello: &[u8]) -> (out: Result<Self, Error>)
        ensures super::contract::start_ensures(client_hello@, construction_view(out)),
    {
        if client_hello.len() > MAX_BODY { return Err(Error::TooLarge); }
        let mut messages = Vec::new();
        crate::encode::write_handshake(&mut messages, 1, client_hello);
        proof { super::lemmas::lemma_start_wf(client_hello@); }
        Ok(Transcript { messages, phase: Phase::FirstServerHello, retried: false })
    }

    /// The exact transcript bytes, including handshake headers and the retry rewrite.
    pub fn messages(&self) -> (out: &[u8])
        ensures out@ == self@.messages,
    { self.messages.as_slice() }

    /// Whether a HelloRetryRequest was accepted.
    pub fn retried(&self) -> (out: bool)
        ensures out == self@.retried,
    { self.retried }

    /// The Hello progression (not the authentication state).
    pub fn phase(&self) -> (out: Phase)
        ensures out == self@.phase,
    { self.phase }

    /// RFC 8446 §4.4.1 Transcript-Hash over the accumulated handshake encodings.
    pub fn hash<C: Crypto>(&self, crypto: &C) -> (out: Vec<u8>)
        ensures out@ == (crypto.functions().hash)(self@.messages), out.len() == 32,
    { crypto.hash(self.messages.as_slice()) }

    /// RFC 8446 §4.4.1: append one classified message body, replacing ClientHello1
    /// with message_hash on a retry. Negotiation and message-body checks belong
    /// to the caller. A rejected operation leaves the accumulator unchanged.
    pub fn push<C: Crypto>(&mut self, crypto: &C, kind: Kind, body: &[u8]) -> (out: Result<(), Error>)
        requires super::spec::wf(old(self)@),
        ensures super::contract::push_ensures(crypto.functions().hash, old(self)@, kind, body@, final(self)@, out),
    {
        if body.len() > MAX_BODY { return Err(Error::TooLarge); }
        let phase = match next_phase(self.phase, kind) {
            Some(p) => p,
            None => return Err(Error::UnexpectedMessage),
        };
        let is_retry = matches!(kind, Kind::HelloRetryRequest);
        let ghost expected_prefix = if kind == Kind::HelloRetryRequest {
            crate::spec::write_handshake(254, (crypto.functions().hash)(old(self)@.messages))
        } else { old(self)@.messages };
        let mut messages = Vec::new();
        if is_retry {
            let hash = crypto.hash(self.messages.as_slice());
            crate::encode::write_handshake(&mut messages, 254, hash.as_slice());
            proof {
                super::lemmas::lemma_message_length(254, hash@);
                assert(hash@ == (crypto.functions().hash)(old(self)@.messages));
                assert(messages@ =~= crate::spec::write_handshake(254, hash@));
                assert(messages@ == expected_prefix);
            }
        } else {
            messages.extend_from_slice(self.messages.as_slice());
            proof {
                assert(messages@ =~= old(self)@.messages);
                assert(messages@ == expected_prefix);
            }
        }
        let ghost prefix = messages@;
        proof {
            assert(prefix == expected_prefix);
            assert(prefix.len() <= MAX_TRANSCRIPT);
            super::lemmas::lemma_message_length(super::spec::wire_type(kind), body@);
        }
        // Both sizes are already bounded; these additions cannot saturate.
        let needed = messages.len().saturating_add(4).saturating_add(body.len());
        proof { assert(needed == prefix.len() + 4 + body@.len()); }
        if needed > MAX_TRANSCRIPT { return Err(Error::TooLarge); }
        let t = wire_type(kind);
        crate::encode::write_handshake(&mut messages, t, body);
        proof {
            assert(messages@ =~= prefix + crate::spec::write_handshake(t, body@));
            super::lemmas::lemma_step_wf(crypto.functions().hash, old(self)@, kind, body@);
        }
        self.messages = messages;
        self.phase = phase;
        self.retried = self.retried || is_retry;
        Ok(())
    }
}

/// RFC 8446 §4.4.3 context strings, without the separator byte.
pub fn context(server: bool) -> (out: &'static [u8])
    ensures out@ == super::spec::context(server), out.len() == 33,
{
    let out: &[u8] = if server { &[84u8, 76u8, 83u8, 32u8, 49u8, 46u8, 51u8, 44u8, 32u8, 115u8, 101u8, 114u8, 118u8, 101u8, 114u8, 32u8, 67u8, 101u8, 114u8, 116u8, 105u8, 102u8, 105u8, 99u8, 97u8, 116u8, 101u8, 86u8, 101u8, 114u8, 105u8, 102u8, 121u8] } else { &[84u8, 76u8, 83u8, 32u8, 49u8, 46u8, 51u8, 44u8, 32u8, 99u8, 108u8, 105u8, 101u8, 110u8, 116u8, 32u8, 67u8, 101u8, 114u8, 116u8, 105u8, 102u8, 105u8, 99u8, 97u8, 116u8, 101u8, 86u8, 101u8, 114u8, 105u8, 102u8, 121u8] };
    proof { assert(out@ =~= super::spec::context(server)); }
    out
}

/// RFC 8446 §4.4.3, four parts of the signature input: pad, context,
/// separator, transcript hash. This constructs the input; it does not verify a signature.
pub fn certificate_verify_input(server: bool, transcript_hash: &[u8]) -> (out: Vec<u8>)
    requires transcript_hash.len() == 32,
    ensures super::contract::certificate_verify_ensures(server, transcript_hash@, out@),
{
    let mut out = Vec::new();
    let mut i: usize = 0;
    while i < 64
        invariant i <= 64, out@ == Seq::new(i as nat, |j: int| 32u8),
        decreases 64 - i,
    {
        out.push(32);
        i = i.saturating_add(1);
        proof { assert(out@ =~= Seq::new(i as nat, |j: int| 32u8)); }
    }
    let context = context(server);
    out.extend_from_slice(context);
    out.push(0);
    out.extend_from_slice(transcript_hash);
    proof { assert(out@ =~= super::spec::certificate_verify_input(server, transcript_hash@)); }
    out
}
} // verus!
