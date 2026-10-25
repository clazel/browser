//! RFC 8446 (August 2018), §4.1.4, §4.4.1 and §4.4.3.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-4.4.1>.
//!
//! Modelling choices:
//! - SHA-256, no PSK, early data or post-handshake authentication.
//! - Store handshake encodings rather than a running hash state; both
//!   compute the same Transcript-Hash. Record headers are never inputs.
//! - Inputs are classified message bodies from the caller. Negotiation,
//!   semantic validation and the order of authentication messages are the
//!   future handshake machine's responsibility, not this accumulator's.
//! - Enforce the first/second Hello order to make the §4.4.1 replacement
//!   possible exactly once. Authentication messages can only follow the
//!   final ServerHello. The caller supplies its own encoded ClientHello.
//! - A body is at most the existing 2^18-octet handshake limit; transcript
//!   storage is capped at 4 MiB, a resource policy, not an RFC limit.
//! - Rejected operations leave the executable accumulator unchanged.
//! - RFC equations and prose have no numbered steps; comments name them.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// Resource policy for retained handshake encodings.
pub const MAX_TRANSCRIPT: usize = 4_194_304;
/// Same body limit as the existing TLS handshake reassembler.
pub const MAX_BODY: usize = 262_144;

/// Transcript progression, not an authentication state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Initial ClientHello is the only message accumulated.
    FirstServerHello,
    /// A retry was received; the second ClientHello must be sent next.
    SecondClientHello,
    /// Second ClientHello was sent; await the final ServerHello.
    SecondServerHello,
    /// Final ServerHello accumulated; authentication order belongs to the caller.
    Handshake,
}

/// The non-PSK profile's transcript message classes (§4.4.1's list).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Initial/second ClientHello.
    ClientHello,
    /// A final ServerHello, already distinguished from HelloRetryRequest.
    ServerHello,
    /// HelloRetryRequest, identified by the parsed ServerHello random.
    HelloRetryRequest,
    /// EncryptedExtensions.
    EncryptedExtensions,
    /// Server CertificateRequest.
    CertificateRequest,
    /// Server/client Certificate.
    Certificate,
    /// Server/client CertificateVerify.
    CertificateVerify,
    /// Server/client Finished.
    Finished,
}

/// A transcript operation can fail without changing the accumulator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// Resource policy would be exceeded.
    TooLarge,
    /// Message class does not belong at this point in the Hello exchange.
    UnexpectedMessage,
}

/// Executable accumulator's abstract state.
pub struct State {
    /// Concatenated handshake encodings (with the synthetic retry message).
    pub messages: Seq<u8>,
    /// Hello progression.
    pub phase: Phase,
    /// A HelloRetryRequest has already been accumulated.
    pub retried: bool,
}

/// Invariant supplied by start and preserved by every accepted operation.
pub open spec fn wf(s: State) -> bool {
    s.messages.len() <= MAX_TRANSCRIPT
        && (s.phase == Phase::FirstServerHello ==> !s.retried)
        && (s.phase == Phase::SecondClientHello || s.phase == Phase::SecondServerHello ==> s.retried)
}

/// §4: a HelloRetryRequest has the ServerHello wire type, not a new type.
pub open spec fn wire_type(kind: Kind) -> u8 {
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

/// §4.1.4 and §4.4.1: first/second Hello progression; no second retry.
pub open spec fn next_phase(phase: Phase, kind: Kind) -> Option<Phase> {
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

/// §4.4.1 Transcript-Hash input starts with the encoded ClientHello.
pub open spec fn start(client_hello: Seq<u8>) -> Result<State, Error> {
    if client_hello.len() > MAX_BODY {
        Err(Error::TooLarge)
    } else {
        Ok(State { messages: crate::spec::write_handshake(1, client_hello),
            phase: Phase::FirstServerHello, retried: false })
    }
}

/// §4.4.1: append the handshake encoding; replace ClientHello1 on retry.
pub open spec fn step(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State,
    kind: Kind, body: Seq<u8>) -> Result<State, Error>
{
    if body.len() > MAX_BODY {
        Err(Error::TooLarge)
    } else {
        match next_phase(s.phase, kind) {
            None => Err(Error::UnexpectedMessage),
            Some(phase) => {
                let message = crate::spec::write_handshake(wire_type(kind), body);
                let messages = if kind == Kind::HelloRetryRequest {
                    // §4.4.1 synthetic message_hash || uint24(Hash.length) || Hash(ClientHello1).
                    crate::spec::write_handshake(254, hash(s.messages)) + message
                } else {
                    s.messages + message
                };
                if messages.len() > MAX_TRANSCRIPT {
                    Err(Error::TooLarge)
                } else {
                    Ok(State { messages, phase, retried: s.retried || kind == Kind::HelloRetryRequest })
                }
            },
        }
    }
}

/// §4.4.3: distinct server/client context strings, without a trailing NUL.
pub open spec fn context(server: bool) -> Seq<u8> {
    if server { seq![84u8, 76u8, 83u8, 32u8, 49u8, 46u8, 51u8, 44u8, 32u8, 115u8, 101u8, 114u8, 118u8, 101u8, 114u8, 32u8, 67u8, 101u8, 114u8, 116u8, 105u8, 102u8, 105u8, 99u8, 97u8, 116u8, 101u8, 86u8, 101u8, 114u8, 105u8, 102u8, 121u8] } else { seq![84u8, 76u8, 83u8, 32u8, 49u8, 46u8, 51u8, 44u8, 32u8, 99u8, 108u8, 105u8, 101u8, 110u8, 116u8, 32u8, 67u8, 101u8, 114u8, 116u8, 105u8, 102u8, 105u8, 99u8, 97u8, 116u8, 101u8, 86u8, 101u8, 114u8, 105u8, 102u8, 121u8] }
}

/// §4.4.3: the four concatenated parts of the content covered by the signature.
pub open spec fn certificate_verify_input(server: bool, transcript_hash: Seq<u8>) -> Seq<u8> {
    Seq::new(64, |i: int| 32u8) + context(server) + seq![0u8] + transcript_hash
}
} // verus!
