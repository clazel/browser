//! RFC 8446 Appendix A.1, the client state machine: the order of messages and the
//! transitions, with the actions of §4 and §7 attached.
//!
//! Modelling choices:
//! - A.1's state names, "(in all capitals ...) have no formal meaning": [`ClientState`]
//!   is `Start` for START, `WaitSh` for WAIT_SH, and so on. "Using PSK", "[K_send =
//!   early data]" and "[Send EndOfEarlyData]" are not reachable, since the client
//!   offers no PSK.
//! - One function, [`receive_handshake_message`], takes one complete handshake
//!   message in a state and gives the next state and the actions, in A.1's order, as
//!   a list of [`Action`]s. Reassembly and the record layer are `connection`'s.
//! - A.1's "K_recv = handshake" and so on are `Action::SetReceiveSecret` and
//!   `Action::SetSendSecret`, the secret of §7.3's table, from which the keys follow.
//! - A.1 folds into one step everything between one receive and the next: on
//!   Finished, the Certificate if any, the Finished, and both key changes.
//! - The arrows "WAIT_SH ---Recv HelloRetryRequest---> START ---Send
//!   ClientHello---> WAIT_SH" are one step from `WaitSh` to `WaitSh`, with
//!   `retry` recording that it happened. `Start` is only the state before
//!   [`start_handshake`].
//! - **Order within a message.** "unexpected in this state" comes first (§4 says the
//!   order rule without regard to content, and `select`'s arm cannot be chosen
//!   otherwise). Then syntax. Then the failure list of the message.
//! - In CONNECTED, §4.6's messages are handled: A.1 ends at CONNECTED, and §4.6 says
//!   what may follow. The transcript is not extended: "subsequent post-handshake
//!   authentications do not include each other, just the messages through the end of
//!   the main handshake", and NewSessionTicket and KeyUpdate are not in §4.4.1's list
//!   of messages.
//! - A.1's note, "clients may send alerts that derive from post-ServerHello messages
//!   in the clear or with the early data keys. If clients need to send such alerts,
//!   they SHOULD first rekey to the handshake keys if possible": that SHOULD is
//!   followed in `connection::alert_record`, so A.1's "K_send = handshake" stays where
//!   the diagram draws it, and the alert does not move it.
//! - The private key material the client generates (§4.2.8.2) comes in as an
//!   argument: the first share's and the one to use if a HelloRetryRequest selects a
//!   group, chosen in advance because a spec function cannot draw randomness. "The
//!   key_exchange values for each KeyShareEntry MUST be generated independently" is
//!   the caller's obligation.

#[allow(unused_imports)]
use vstd::prelude::*;

use super::alerts::ClientError;
use super::key_exchange::{ClientHello, RetryRecord};

#[cfg(verus_only)]
use super::alerts::*;
#[cfg(verus_only)]
use super::authentication::*;
#[cfg(verus_only)]
use super::extensions::*;
#[cfg(verus_only)]
use super::key_exchange::*;
#[cfg(verus_only)]
use super::key_schedule::*;
#[cfg(verus_only)]
use super::post_handshake::*;
#[cfg(verus_only)]
use super::presentation::*;
#[cfg(verus_only)]
use super::primitives::*;

verus! {

/// Appendix A.1's states.
pub enum ClientState {
    /// START.
    Start,
    /// WAIT_SH.
    WaitSh,
    /// WAIT_EE.
    WaitEe,
    /// WAIT_CERT_CR.
    WaitCertCr,
    /// WAIT_CERT.
    WaitCert,
    /// WAIT_CV.
    WaitCv,
    /// WAIT_FINISHED.
    WaitFinished,
    /// CONNECTED.
    Connected,
}

/// What the client remembers of the handshake, A.1's implicit state. Fields not yet
/// set are empty sequences.
pub struct ClientHandshake {
    /// A.1's state.
    pub state: ClientState,
    /// §4.2.8's "the original ClientHello": the first one sent.
    pub first_hello: ClientHello,
    /// The ClientHello most recently sent.
    pub hello: ClientHello,
    /// What a HelloRetryRequest fixed, if one came. That it is `Some` is also "the
    /// ClientHello was itself in response to a HelloRetryRequest" (§4.1.4) and
    /// §4.4.1's condition for the synthetic message.
    pub retry: Option<RetryRecord>,
    /// §4.4.1: the raw handshake messages of the transcript so far.
    pub transcript: Seq<Seq<u8>>,
    /// §7.4.2: the private key of the share the current ClientHello offers.
    pub x25519_private_key: Seq<u8>,
    /// §7.4.2: the private key to use if a HelloRetryRequest selects a group.
    pub retry_private_key: Seq<u8>,
    /// §7.1: Handshake Secret.
    pub handshake_secret: Seq<u8>,
    /// §7.1: client_handshake_traffic_secret.
    pub client_handshake_traffic_secret: Seq<u8>,
    /// §7.1: server_handshake_traffic_secret, §4.4's Base Key of the server.
    pub server_handshake_traffic_secret: Seq<u8>,
    /// §4.4.3: "The public key contained in the end-entity certificate".
    pub server_public_key: Seq<u8>,
    /// §4.3.2: the context of a CertificateRequest, if one came.
    pub certificate_request_context: Option<Seq<u8>>,
    /// §7.1: resumption_master_secret, once computed.
    pub resumption_master_secret: Seq<u8>,
    /// §7.1: exporter_master_secret, once computed.
    pub exporter_master_secret: Seq<u8>,
}

/// One action of A.1, in the order it is taken.
pub enum Action {
    /// "Send ...": a handshake message, with the §5.1 legacy_record_version of its
    /// record if not yet protected.
    SendHandshake(Seq<u8>, nat),
    /// "K_recv = ...": this secret's keys protect what is read from now on.
    SetReceiveSecret(Seq<u8>),
    /// "K_send = ...": this secret's keys protect what is written from now on.
    SetSendSecret(Seq<u8>),
    /// §4.6.3: "Upon receiving a KeyUpdate, the receiver MUST update its receiving
    /// keys."
    UpdateReceiveSecret,
    /// §4.6.3: "the receiver MUST send a KeyUpdate of its own with request_update set
    /// to 'update_not_requested' prior to sending its next Application Data record."
    RespondToKeyUpdate,
}

/// The result of one handshake message.
pub enum HandshakeStep {
    /// The handshake aborts.
    Abort(ClientError),
    /// It continues.
    Proceed {
        /// The state after the message.
        handshake: ClientHandshake,
        /// A.1's actions.
        actions: Seq<Action>,
        /// §5.1: "ClientHello, EndOfEarlyData, ServerHello, Finished, and KeyUpdate
        /// messages can immediately precede a key change". For the reader here,
        /// whether the receive key changes after this message.
        receive_key_changes: bool,
    },
}

/// §4.1.2: "When a client first connects to a server, it is REQUIRED to send the
/// ClientHello as its first TLS message." The state after that, from START to WAIT_SH.
pub open spec fn start_handshake(hello: ClientHello, x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>) -> ClientHandshake {
    ClientHandshake {
        state: ClientState::WaitSh,
        first_hello: hello,
        hello,
        retry: None,
        transcript: seq![write_client_hello(hello)],
        x25519_private_key,
        retry_private_key,
        handshake_secret: seq![],
        client_handshake_traffic_secret: seq![],
        server_handshake_traffic_secret: seq![],
        server_public_key: seq![],
        certificate_request_context: None,
        resumption_master_secret: seq![],
        exporter_master_secret: seq![],
    }
}

/// §5.1: "a record containing an initial ClientHello SHOULD have version 0x0301
/// (reflecting TLS 1.0)".
pub open spec fn initial_client_hello_record_version() -> nat { 0x0301 }

/// §5.1: "a record containing a second ClientHello or a ServerHello MUST have version
/// 0x0303".
pub open spec fn other_record_version() -> nat { 0x0303 }

/// A handshake that keeps going in the same way: no key change.
pub open spec fn proceed(handshake: ClientHandshake, actions: Seq<Action>) -> HandshakeStep {
    HandshakeStep::Proceed { handshake, actions, receive_key_changes: false }
}

/// WAIT_SH, "Recv HelloRetryRequest", after its failures: §4.1.4's "the client MUST
/// process all extensions in the HelloRetryRequest and send a second updated
/// ClientHello."
pub open spec fn accept_hello_retry_request(p: Primitives, hs: ClientHandshake, hello: super::key_exchange::ServerHello, raw: Seq<u8>) -> HandshakeStep {
    let selects_group = find_extension(hello.extensions, ext_key_share()) is Some;
    let private_key = if selects_group { hs.retry_private_key } else { hs.x25519_private_key };
    // §7.4.2: "The public key to put into the KeyShareEntry.key_exchange structure is
    // the result of applying the ECDH scalar multiplication function to the secret
    // key ... and the standard public basepoint".
    let public_key = (p.x25519)(private_key, x25519_basepoint());
    let second = second_client_hello(hs.hello, hello.extensions, public_key);
    let second_raw = write_client_hello(second);
    proceed(
        ClientHandshake {
            hello: second,
            retry: Some(retry_record(hello)),
            transcript: hs.transcript.push(raw).push(second_raw),
            x25519_private_key: private_key,
            ..hs
        },
        seq![Action::SendHandshake(second_raw, other_record_version())],
    )
}

/// WAIT_SH, "Recv ServerHello", after its failures. "K_recv = handshake". §7.1 for the
/// secrets; §7.4.2 for X25519: "Implementations MUST check whether the computed
/// Diffie-Hellman shared secret is the all-zero value and abort if so".
pub open spec fn accept_server_hello(p: Primitives, hs: ClientHandshake, hello: super::key_exchange::ServerHello, raw: Seq<u8>) -> HandshakeStep {
    let server_share_data = match find_extension(hello.extensions, ext_key_share()) {
        Some(data) => data,
        None => seq![],
    };
    let peer_public_key = match read_key_share_server_hello(server_share_data) {
        Some(server_share) => server_share.key_exchange,
        None => seq![],
    };
    // §7.4.2: "The ECDH shared secret is the result of applying the ECDH scalar
    // multiplication function to the secret key (into scalar input) and the peer's
    // public key (into u-coordinate point input). The output is used raw".
    let shared_secret = (p.x25519)(hs.x25519_private_key, peer_public_key);
    if all_zero(shared_secret) {
        HandshakeStep::Abort(ClientError::SharedSecretAllZero)
    } else {
        let transcript = hs.transcript.push(raw);
        let retried = hs.retry is Some;
        // §7.1: "if PSK is not in use, Early Secret will still be HKDF-Extract(0, 0)."
        let handshake = handshake_secret(p, early_secret(p, zero_value()), shared_secret);
        let client_secret = client_handshake_traffic_secret(p, handshake, transcript, retried);
        let server_secret = server_handshake_traffic_secret(p, handshake, transcript, retried);
        HandshakeStep::Proceed {
            handshake: ClientHandshake {
                state: ClientState::WaitEe,
                transcript,
                handshake_secret: handshake,
                client_handshake_traffic_secret: client_secret,
                server_handshake_traffic_secret: server_secret,
                ..hs
            },
            actions: seq![Action::SetReceiveSecret(server_secret)],
            receive_key_changes: true,
        }
    }
}

/// WAIT_SH: a message of type server_hello. §4.1.3: "Upon receiving a message with
/// type server_hello, implementations MUST first examine the Random value and, if it
/// matches this value, process it as described in Section 4.1.4".
pub open spec fn receive_server_hello(p: Primitives, hs: ClientHandshake, body: Seq<u8>, raw: Seq<u8>) -> HandshakeStep {
    match read_server_hello_any_version(body) {
        None => HandshakeStep::Abort(ClientError::Malformed),
        Some(any_version) =>
            if is_hello_retry_request(any_version) {
                // §4.1.4: "If a client receives a second HelloRetryRequest in the same
                // connection".
                if hs.retry is Some {
                    HandshakeStep::Abort(ClientError::SecondHelloRetryRequest)
                } else {
                    match read_server_hello(body) {
                        None => HandshakeStep::Abort(ClientError::Malformed),
                        Some(hello) => {
                            let failures = hello_retry_request_failures(hs.hello, hello);
                            if failures.len() > 0 {
                                HandshakeStep::Abort(failures[0])
                            } else {
                                accept_hello_retry_request(p, hs, hello, raw)
                            }
                        },
                    }
                }
            } else if find_extension(any_version.extensions, ext_supported_versions()) is None {
                // §4.2.1: "Clients MUST check for this extension prior to processing
                // the rest of the ServerHello". §4.1.3, D.1: it cannot continue.
                HandshakeStep::Abort(older_server_hello_failures(any_version)[0])
            } else {
                match read_server_hello(body) {
                    None => HandshakeStep::Abort(ClientError::Malformed),
                    Some(hello) => {
                        let failures = server_hello_failures(hs.hello, hello, hs.retry);
                        if failures.len() > 0 {
                            HandshakeStep::Abort(failures[0])
                        } else {
                            accept_server_hello(p, hs, hello, raw)
                        }
                    },
                }
            },
    }
}

/// WAIT_EE, "Recv EncryptedExtensions". To WAIT_CERT_CR ("Using certificate", the only
/// way without PSK).
pub open spec fn receive_encrypted_extensions(hs: ClientHandshake, body: Seq<u8>, raw: Seq<u8>) -> HandshakeStep {
    match read_encrypted_extensions(body) {
        None => HandshakeStep::Abort(ClientError::Malformed),
        Some(message) => {
            let failures = encrypted_extensions_failures(hs.hello, message);
            if failures.len() > 0 {
                HandshakeStep::Abort(failures[0])
            } else {
                proceed(ClientHandshake { state: ClientState::WaitCertCr, transcript: hs.transcript.push(raw), ..hs }, seq![])
            }
        },
    }
}

/// WAIT_CERT_CR, "Recv CertificateRequest". To WAIT_CERT.
pub open spec fn receive_certificate_request(hs: ClientHandshake, body: Seq<u8>, raw: Seq<u8>) -> HandshakeStep {
    match read_certificate_request(body) {
        None => HandshakeStep::Abort(ClientError::Malformed),
        Some(message) => {
            let failures = certificate_request_failures(message);
            if failures.len() > 0 {
                HandshakeStep::Abort(failures[0])
            } else {
                proceed(ClientHandshake {
                    state: ClientState::WaitCert,
                    transcript: hs.transcript.push(raw),
                    certificate_request_context: Some(message.certificate_request_context),
                    ..hs
                }, seq![])
            }
        },
    }
}

/// WAIT_CERT_CR or WAIT_CERT, "Recv Certificate". To WAIT_CV.
pub open spec fn receive_certificate(p: Primitives, hs: ClientHandshake, body: Seq<u8>, raw: Seq<u8>) -> HandshakeStep {
    match read_certificate(body) {
        None => HandshakeStep::Abort(ClientError::Malformed),
        Some(message) => {
            let failures = certificate_failures(hs.hello, message);
            if failures.len() > 0 {
                HandshakeStep::Abort(failures[0])
            } else {
                match (p.validate_certificate_chain)(message.certificate_list) {
                    // §4.4.2.2: "it MUST abort the handshake with an appropriate
                    // certificate-related alert".
                    ChainResult::Rejected(alert) => HandshakeStep::Abort(ClientError::ChainRejected(alert)),
                    ChainResult::Accepted(server_public_key) =>
                        proceed(ClientHandshake {
                            state: ClientState::WaitCv,
                            transcript: hs.transcript.push(raw),
                            server_public_key,
                            ..hs
                        }, seq![]),
                }
            }
        },
    }
}

/// WAIT_CV, "Recv CertificateVerify". To WAIT_FINISHED.
pub open spec fn receive_certificate_verify(p: Primitives, hs: ClientHandshake, body: Seq<u8>, raw: Seq<u8>) -> HandshakeStep {
    match read_certificate_verify(body) {
        None => HandshakeStep::Abort(ClientError::Malformed),
        Some(message) => {
            let failures = certificate_verify_failures(p, hs.hello, message, hs.transcript, hs.retry is Some, hs.server_public_key);
            if failures.len() > 0 {
                HandshakeStep::Abort(failures[0])
            } else {
                proceed(ClientHandshake { state: ClientState::WaitFinished, transcript: hs.transcript.push(raw), ..hs }, seq![])
            }
        },
    }
}

/// WAIT_FINISHED, "Recv Finished", to CONNECTED:
/// ```text
///   K_send = handshake
///   [Send Certificate [+ CertificateVerify]]
///   Send Finished
///   K_send = K_recv = application
/// ```
pub open spec fn receive_finished(p: Primitives, hs: ClientHandshake, body: Seq<u8>, raw: Seq<u8>) -> HandshakeStep {
    let retried = hs.retry is Some;
    match read_finished(body) {
        None => HandshakeStep::Abort(ClientError::Malformed),
        Some(message) =>
            // §4.4.4: "Recipients of Finished messages MUST verify that the contents are
            // correct". §4.4's table: the Server row's Base Key.
            if message.verify_data != verify_data(p, hs.server_handshake_traffic_secret, hs.transcript, retried) {
                HandshakeStep::Abort(ClientError::FinishedIncorrect)
            } else {
                // ClientHello...server Finished.
                let through_server_finished = hs.transcript.push(raw);
                let master = master_secret(p, hs.handshake_secret);
                let client_application = client_application_traffic_secret_0(p, master, through_server_finished, retried);
                let server_application = server_application_traffic_secret_0(p, master, through_server_finished, retried);
                // §4.4.2: "The client MUST send a Certificate message if and only if the
                // server has requested client authentication"; "If the server requests
                // client authentication but no suitable certificate is available, the
                // client MUST send a Certificate message containing no certificates".
                // §4.4.2's certificate_request_context: "If this message is in response
                // to a CertificateRequest, the value of certificate_request_context in
                // that message."
                let client_certificate: Seq<Seq<u8>> = match hs.certificate_request_context {
                    None => seq![],
                    Some(certificate_request_context) => seq![write_certificate(
                        Certificate { certificate_request_context, certificate_list: seq![] })],
                };
                let through_client_certificate = through_server_finished + client_certificate;
                // §4.4's table: the Client row's Handshake Context and Base Key.
                let client_finished = write_finished(
                    verify_data(p, hs.client_handshake_traffic_secret, through_client_certificate, retried));
                let through_client_finished = through_client_certificate.push(client_finished);
                HandshakeStep::Proceed {
                    handshake: ClientHandshake {
                        state: ClientState::Connected,
                        transcript: through_client_finished,
                        resumption_master_secret: resumption_master_secret(p, master, through_client_finished, retried),
                        exporter_master_secret: exporter_master_secret(p, master, through_server_finished, retried),
                        ..hs
                    },
                    actions: seq![Action::SetSendSecret(hs.client_handshake_traffic_secret)]
                        + send_each(client_certificate)
                        + seq![
                            Action::SendHandshake(client_finished, other_record_version()),
                            Action::SetSendSecret(client_application),
                            Action::SetReceiveSecret(server_application),
                        ],
                    receive_key_changes: true,
                }
            },
    }
}

/// The action of sending each message of the list.
pub open spec fn send_each(messages: Seq<Seq<u8>>) -> Seq<Action>
    decreases messages.len(),
{
    if messages.len() == 0 {
        seq![]
    } else {
        seq![Action::SendHandshake(messages[0], other_record_version())]
            + send_each(messages.subrange(1, messages.len() as int))
    }
}

/// CONNECTED: §4.6's messages.
pub open spec fn receive_post_handshake(hs: ClientHandshake, msg_type: nat, body: Seq<u8>) -> HandshakeStep {
    if msg_type == ht_new_session_ticket() {
        match read_new_session_ticket(body) {
            None => HandshakeStep::Abort(ClientError::Malformed),
            Some(message) => {
                let failures = new_session_ticket_failures(message);
                if failures.len() > 0 { HandshakeStep::Abort(failures[0]) } else { proceed(hs, seq![]) }
            },
        }
    } else if msg_type == ht_key_update() {
        match read_key_update(body) {
            None => HandshakeStep::Abort(ClientError::Malformed),
            Some(message) => {
                let failures = key_update_failures(message);
                if failures.len() > 0 {
                    HandshakeStep::Abort(failures[0])
                } else {
                    HandshakeStep::Proceed {
                        handshake: hs,
                        actions: if message.request_update == update_requested() {
                            seq![Action::UpdateReceiveSecret, Action::RespondToKeyUpdate]
                        } else {
                            seq![Action::UpdateReceiveSecret]
                        },
                        receive_key_changes: true,
                    }
                }
            },
        }
    } else if msg_type == ht_certificate_request() {
        // §4.6.2: the profile never sends post_handshake_auth.
        HandshakeStep::Abort(ClientError::PostHandshakeAuthNotOffered)
    } else if msg_type == ht_end_of_early_data() {
        HandshakeStep::Abort(ClientError::EndOfEarlyDataReceived)
    } else {
        HandshakeStep::Abort(ClientError::UnexpectedHandshakeMessage)
    }
}

/// A message of the wrong type for a state before CONNECTED, with the more specific
/// names the RFC gives two of them.
pub open spec fn out_of_order(msg_type: nat) -> HandshakeStep {
    if msg_type == ht_key_update() {
        // §4.6.3.
        HandshakeStep::Abort(ClientError::KeyUpdateBeforeFinished)
    } else if msg_type == ht_end_of_early_data() {
        // §4.5.
        HandshakeStep::Abort(ClientError::EndOfEarlyDataReceived)
    } else {
        // §4.
        HandshakeStep::Abort(ClientError::UnexpectedHandshakeMessage)
    }
}

/// Appendix A.1's transitions, on one complete handshake message `raw`, header
/// included. §4: "Protocol messages MUST be sent in the order defined in Section 4.4.1
/// and shown in the diagrams in Section 2."
pub open spec fn receive_handshake_message(p: Primitives, hs: ClientHandshake, raw: Seq<u8>) -> HandshakeStep {
    let msg_type = raw[0] as nat;
    let body = raw.subrange(4, raw.len() as int);
    match hs.state {
        ClientState::Start => out_of_order(msg_type),
        ClientState::WaitSh =>
            if msg_type == ht_server_hello() { receive_server_hello(p, hs, body, raw) } else { out_of_order(msg_type) },
        ClientState::WaitEe =>
            if msg_type == ht_encrypted_extensions() { receive_encrypted_extensions(hs, body, raw) } else { out_of_order(msg_type) },
        ClientState::WaitCertCr =>
            if msg_type == ht_certificate() {
                receive_certificate(p, hs, body, raw)
            } else if msg_type == ht_certificate_request() {
                receive_certificate_request(hs, body, raw)
            } else {
                out_of_order(msg_type)
            },
        ClientState::WaitCert =>
            if msg_type == ht_certificate() { receive_certificate(p, hs, body, raw) } else { out_of_order(msg_type) },
        ClientState::WaitCv =>
            if msg_type == ht_certificate_verify() { receive_certificate_verify(p, hs, body, raw) } else { out_of_order(msg_type) },
        ClientState::WaitFinished =>
            if msg_type == ht_finished() { receive_finished(p, hs, body, raw) } else { out_of_order(msg_type) },
        ClientState::Connected => receive_post_handshake(hs, msg_type, body),
    }
}

} // verus!
