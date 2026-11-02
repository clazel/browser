//! The socket-free TLS 1.3 client driver (phase-3.md item 3.5f: "the
//! `clazel-tls` public API the shell drives (`connect(host) -> state`,
//! `step`)").
//!
//! [`Client`] owns the three phases of one client connection and the order
//! in which they hand over, with this crate's libcrux providers and the
//! production [`ChainVerifier`]:
//!
//! 1. `clazel_tls::hello::bootstrap::Bootstrap`: the ClientHello, an optional
//!    HelloRetryRequest and ClientHello2, the ServerHello (RFC 8446 §4.1),
//!    all in plaintext records.
//! 2. The key exchange handoff: `clazel_tls::traffic::handshake::start`
//!    (X25519 and the handshake traffic keys, §7.1, §7.3), exactly what
//!    `Established::into_record_auth` calls.
//! 3. `clazel_tls::connection::exec::Connection`: the server's protected
//!    flight (EncryptedExtensions, Certificate, CertificateVerify, Finished)
//!    checked by the [`ChainVerifier`], the client Finished, then
//!    application data, KeyUpdate and close_notify.
//!
//! It is a transducer like the machines it drives: no sockets, no clock and
//! no randomness of its own. The caller supplies the time and a source of
//! random octets, puts every octet of [`Output::send`] on the wire in order,
//! hands every octet received to [`Client::receive`], and reports the end of
//! the stream with [`Client::receive_eof`]. Octets returned in `send` count
//! as sent: if the caller cannot write them, the connection is dead and the
//! client must be dropped.
//!
//! **States** ([`State`]): `Handshaking` from [`Client::connect`] until the
//! server's Finished has been verified and the client Finished is in `send`;
//! `Open` (application data both ways); `Closing` after [`Client::close`]
//! (our close_notify sent, reads still delivered); `Closed` once both
//! close_notify alerts have been seen; `Failed` with the RFC 8446 §6.2 alert
//! and where it came from ([`Origin`]). `Closed` and `Failed` are final:
//! later octets are ignored (§6.1: "Any data received after a closure alert
//! has been received MUST be ignored").
//!
//! **Alerts.** Neither `Bootstrap` nor `Connection` puts an alert on the
//! wire when it fails ("no alert is sent automatically"), so this driver
//! does, once, where it can (§6.2: on a fatal error an implementation
//! "SHOULD send an appropriate fatal alert"; §6: "MUST send alert X if it
//! sends any alert"):
//!
//! - Before the handshake keys (phases 1 and 2) it writes a plaintext fatal
//!   alert record ([`Origin::Sent`]).
//! - During the server's protected flight it seals the alert under the
//!   client handshake traffic key at sequence number 0, the first record of
//!   that epoch. `Connection` holds its own copy of that key and drops it on
//!   failure, so the driver derives a second copy of the epoch (the verified
//!   `clazel_tls::hello::join::derive`, then `Encryptor::new`) when the
//!   ServerHello is accepted. It is dropped, unused, the moment the client
//!   Finished (which takes sequence number 0) is produced, so it never seals
//!   a second record under the same nonce.
//! - After the client Finished, `Connection` drops its application keys
//!   when it fails and offers no way to seal an alert first, so nothing is
//!   sent ([`Origin::NotSent`]). Sending the alert there needs `clazel-tls`
//!   to seal it before dropping its keys (as its post-handshake transducer
//!   already does, `connection::post_handshake_exec`, not yet joined to the
//!   dispatcher). There `Connection` also reports a fatal alert from the
//!   server as `Fail(description)`, so after the handshake `NotSent` covers
//!   both.
//! - A fatal alert from the server is never answered ([`Origin::Peer`]
//!   before the client Finished).
//!   `Connection` reports a received alert and a local failure alike, as
//!   `Fail(description)`, so the driver also decrypts each record of the
//!   server's protected flight with its own copy of the server handshake
//!   key (the same verified `Decryptor`), in step with `Connection`, and
//!   treats a failure as the peer's when the record that caused it is an
//!   alert carrying that description.
//! - The transport ending before close_notify is [`Origin::Truncated`]
//!   (alert 80, `internal_error`, as the machines report it); nothing is
//!   sent.
//! - A close_notify from the server is answered with ours (§6.1: "Each party
//!   MUST send a "close_notify" alert before closing its write side of the
//!   connection, unless it has already sent some error alert").
//!
//! Tier 0, plain safe Rust outside `verus!`: shell glue, tested end to end
//! against rustls (`tests/client.rs`).

use crate::join::exec::ChainVerifier;
use crate::provider::{ChaCha20Poly1305, ChaCha20Poly1305Factory, Sha256Suite, X25519};
use clazel_tls::connection::exec::{Action as ConnAction, Connection, Mode};
use clazel_tls::hello::bootstrap::{Action as BootAction, Bootstrap};
use clazel_tls::hello::client::{Config, Established};
use clazel_tls::hello::key_exchange::KeyExchange;
use clazel_tls::host::exec::Host;
use clazel_tls::spec::{
    CLOSE_NOTIFY, CT_ALERT, CT_APPLICATION_DATA, INTERNAL_ERROR, LEVEL_FATAL, LEVEL_WARNING,
    MAX_PLAINTEXT,
};
use clazel_tls::traffic::exec::{Decryptor, Encryptor, Read};
use std::fmt;

/// Octets of randomness the client draws per connection: the X25519 scalar
/// (RFC 7748 §5), the ClientHello random (RFC 8446 §4.1.2) and the
/// legacy_session_id (Appendix D.4, middlebox compatibility mode).
const RANDOM_LEN: usize = 32;

/// RFC 8446 §5.1: `legacy_record_version` of every record after the first
/// ClientHello.
const RECORD_VERSION: [u8; 2] = [3, 3];

/// The dispatcher this driver runs after the ServerHello.
type Conn<'r> = Connection<Sha256Suite, ChaCha20Poly1305Factory, ChainVerifier<'r>>;

/// Where the connection is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// The handshake is running.
    Handshaking,
    /// The handshake completed: application data flows both ways.
    Open,
    /// Our close_notify has been sent; the server's has not arrived.
    /// Application data from the server is still delivered.
    Closing,
    /// Both close_notify alerts have been seen. Final.
    Closed,
    /// The connection failed. Final.
    Failed(Failure),
}

impl State {
    /// `Closed` or `Failed`: nothing more will be sent or delivered.
    pub fn is_final(self) -> bool {
        matches!(self, State::Closed | State::Failed(_))
    }
}

/// A fatal end of the connection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Failure {
    /// The RFC 8446 §6.2 `AlertDescription`.
    pub alert: u8,
    /// Who raised it, and whether it went on the wire.
    pub origin: Origin,
}

/// Where a [`Failure`] came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Origin {
    /// The client detected it, and the alert record is in [`Output::send`].
    Sent,
    /// No alert was sent. Either the client could not start, or the failure
    /// came after the client Finished, where `Connection` neither seals an
    /// alert nor says whether the server sent this one: it is the server's
    /// alert or a local error.
    NotSent,
    /// The server sent this fatal alert.
    Peer,
    /// The transport closed before a close_notify (RFC 8446 §6.1
    /// truncation); nothing was sent.
    Truncated,
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = alert_name(self.alert).unwrap_or("unknown alert");
        match self.origin {
            Origin::Sent => write!(f, "{name} ({}), sent to the server", self.alert),
            Origin::NotSent => write!(f, "{name} ({}), not sent", self.alert),
            Origin::Peer => write!(f, "{name} ({}), from the server", self.alert),
            Origin::Truncated => write!(f, "connection closed without close_notify"),
        }
    }
}

/// RFC 8446 §6.2: the name of an `AlertDescription`.
pub fn alert_name(description: u8) -> Option<&'static str> {
    Some(match description {
        0 => "close_notify",
        10 => "unexpected_message",
        20 => "bad_record_mac",
        22 => "record_overflow",
        40 => "handshake_failure",
        42 => "bad_certificate",
        43 => "unsupported_certificate",
        44 => "certificate_revoked",
        45 => "certificate_expired",
        46 => "certificate_unknown",
        47 => "illegal_parameter",
        48 => "unknown_ca",
        49 => "access_denied",
        50 => "decode_error",
        51 => "decrypt_error",
        70 => "protocol_version",
        71 => "insufficient_security",
        80 => "internal_error",
        86 => "inappropriate_fallback",
        90 => "user_canceled",
        109 => "missing_extension",
        110 => "unsupported_extension",
        112 => "unrecognized_name",
        113 => "bad_certificate_status_response",
        115 => "unknown_psk_identity",
        116 => "certificate_required",
        120 => "no_application_protocol",
        _ => return None,
    })
}

/// What one call produced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Output {
    /// Octets to write to the transport, in order.
    pub send: Vec<u8>,
    /// Application data from the server, in order.
    pub deliver: Vec<u8>,
    /// The state after the call.
    pub state: State,
}

/// [`Client::send`] was called while the client cannot send application
/// data: the handshake is running, our close_notify was sent, or the
/// connection ended. Nothing changed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NotOpen(pub State);

/// The driver's copy of the handshake epochs (see the module comment,
/// "Alerts"). It lives from the ServerHello until the client Finished.
struct Shadow {
    /// The client handshake epoch, never used: sequence number 0.
    sender: Encryptor<ChaCha20Poly1305>,
    /// The server handshake epoch, in step with `Connection`'s.
    receiver: Decryptor<ChaCha20Poly1305>,
    /// Octets `Connection` consumed that do not yet form a whole record.
    frame: Vec<u8>,
}

impl Shadow {
    /// Follow the octets `Connection` just consumed. Returns the inner type
    /// and content of the last whole record they completed, if it could be
    /// read.
    fn track(&mut self, consumed: &[u8]) -> Option<(u8, Vec<u8>)> {
        self.frame.extend_from_slice(consumed);
        let mut last = None;
        // RFC 8446 §5.1: a 5-octet header whose last two octets are the
        // length of the fragment.
        while let (Some(&outer), Some(&high), Some(&low)) =
            (self.frame.first(), self.frame.get(3), self.frame.get(4))
        {
            let total = 5usize.saturating_add(usize::from(u16::from_be_bytes([high, low])));
            let (Some(record), Some(rest)) = (self.frame.get(..total), self.frame.get(total..))
            else {
                break;
            };
            last = if outer == CT_APPLICATION_DATA {
                match self.receiver.open(record) {
                    Read::Record(inner, content, _) => Some((inner, content)),
                    Read::NeedMore | Read::Fail(_) => None,
                }
            } else {
                Some((outer, record.get(5..).unwrap_or_default().to_vec()))
            };
            self.frame = rest.to_vec();
        }
        last
    }

    /// Seal an alert as the first record of the client handshake epoch.
    fn seal_alert(&mut self, level: u8, description: u8) -> Option<Vec<u8>> {
        self.sender.seal(CT_ALERT, &[level, description], 0).ok()
    }
}

enum Phase<'r> {
    /// Phase 1: through the ServerHello.
    Hello {
        boot: Box<Bootstrap<Sha256Suite>>,
        scalar: Vec<u8>,
        verifier: ChainVerifier<'r>,
    },
    /// Phase 3: the protected flight, then application traffic.
    Live {
        conn: Box<Conn<'r>>,
        shadow: Option<Box<Shadow>>,
    },
    /// `Closed` or `Failed`.
    Ended,
}

/// One TLS 1.3 client connection, without its socket. See the module
/// comment.
pub struct Client<'r> {
    phase: Phase<'r>,
    /// Received octets the current phase has not consumed yet.
    inbox: Vec<u8>,
    state: State,
}

/// A plaintext alert record (RFC 8446 §5.1, §6).
fn plaintext_alert(level: u8, description: u8) -> Vec<u8> {
    let mut out = vec![CT_ALERT];
    out.extend_from_slice(&RECORD_VERSION);
    out.extend_from_slice(&[0, 2, level, description]);
    out
}

impl<'r> Client<'r> {
    /// Start a connection to `host`, validating certificates at `now`
    /// (seconds since the Unix epoch) against `verifier`'s trust anchors.
    /// `random` must fill its argument with fresh, secret, uniformly random
    /// octets; it is called three times. The output's `send` is the
    /// ClientHello record.
    pub fn connect(
        host: Host,
        now: u64,
        verifier: ChainVerifier<'r>,
        random: &mut dyn FnMut(&mut [u8]),
    ) -> (Self, Output) {
        let mut draw = || {
            let mut bytes = vec![0u8; RANDOM_LEN];
            random(&mut bytes);
            bytes
        };
        let scalar = draw();
        let config = Config {
            host,
            now,
            random: draw(),
            session_id: draw(),
            public_key: X25519.public_key(&scalar),
        };
        let mut client = Client {
            phase: Phase::Ended,
            inbox: Vec::new(),
            state: State::Handshaking,
        };
        let mut out = client.output();
        match Bootstrap::start(config, Sha256Suite) {
            Ok((mut boot, BootAction::Send(wire))) => {
                if matches!(boot.acknowledge_send(&wire), BootAction::None) {
                    out.send = wire;
                    client.phase = Phase::Hello {
                        boot: Box::new(boot),
                        scalar,
                        verifier,
                    };
                } else {
                    client.fail(INTERNAL_ERROR, Origin::NotSent);
                }
            }
            Ok(_) => client.fail(INTERNAL_ERROR, Origin::NotSent),
            Err(alert) => client.fail(alert, Origin::NotSent),
        }
        out.state = client.state;
        (client, out)
    }

    /// The current state.
    pub fn state(&self) -> State {
        self.state
    }

    /// Octets received from the server.
    pub fn receive(&mut self, bytes: &[u8]) -> Output {
        let mut out = self.output();
        if self.state.is_final() {
            return out;
        }
        self.inbox.extend_from_slice(bytes);
        while !self.inbox.is_empty() && !self.state.is_final() {
            let consumed = self.step(&mut out);
            self.inbox = self.inbox.get(consumed..).unwrap_or_default().to_vec();
            if consumed == 0 {
                break;
            }
        }
        if self.state.is_final() {
            self.inbox.clear();
        }
        out.state = self.state;
        out
    }

    /// The server closed the transport (end of stream).
    pub fn receive_eof(&mut self) -> Output {
        let mut out = self.output();
        let action = match &mut self.phase {
            Phase::Hello { boot, .. } => match boot.eof() {
                BootAction::Fail(alert) => Some(alert),
                _ => None,
            },
            Phase::Live { conn, .. } => match conn.eof() {
                ConnAction::Fail(alert) => Some(alert),
                _ => None,
            },
            Phase::Ended => None,
        };
        if let Some(alert) = action {
            self.fail(alert, Origin::Truncated);
        } else if !self.state.is_final() {
            // Neither machine ends a connection on end of stream without an
            // alert unless the server's close_notify came first, and this
            // driver answers that at once; nothing else is reachable.
            self.fail(INTERNAL_ERROR, Origin::Truncated);
        }
        out.state = self.state;
        out
    }

    /// Protect application data. Data over 2^14 octets goes out in several
    /// records (RFC 8446 §5.1).
    pub fn send(&mut self, data: &[u8]) -> Result<Output, NotOpen> {
        if self.state != State::Open {
            return Err(NotOpen(self.state));
        }
        let mut out = self.output();
        if let Phase::Live { conn, .. } = &mut self.phase {
            for chunk in data.chunks(MAX_PLAINTEXT) {
                match conn.send_application(chunk, 0) {
                    ConnAction::Send(wire) => out.send.extend_from_slice(&wire),
                    ConnAction::Fail(alert) => {
                        self.fail(alert, Origin::NotSent);
                        break;
                    }
                    // `None` only while a KeyUpdate awaits its send
                    // acknowledgement, and this driver acknowledges every
                    // send at once.
                    _ => {
                        self.fail(INTERNAL_ERROR, Origin::NotSent);
                        break;
                    }
                }
            }
        }
        out.state = self.state;
        Ok(out)
    }

    /// Close the connection from our side: close_notify once the handshake
    /// has completed (RFC 8446 §6.1), after which the server's remaining
    /// data is still delivered until its close_notify (`Closing`). During
    /// the handshake the client sends close_notify and stops (`Closed`).
    pub fn close(&mut self) -> Output {
        let mut out = self.output();
        match std::mem::replace(&mut self.phase, Phase::Ended) {
            Phase::Hello { .. } => {
                out.send = plaintext_alert(LEVEL_WARNING, CLOSE_NOTIFY);
                self.state = State::Closed;
            }
            Phase::Live {
                mut conn,
                mut shadow,
            } => {
                if conn.mode() == Mode::Ready {
                    if self.state == State::Open {
                        self.close_write(&mut conn, &mut out);
                    }
                    if !self.state.is_final() {
                        self.phase = Phase::Live { conn, shadow };
                    }
                } else {
                    if let Some(wire) = shadow
                        .as_mut()
                        .and_then(|s| s.seal_alert(LEVEL_WARNING, CLOSE_NOTIFY))
                    {
                        out.send = wire;
                    }
                    self.state = State::Closed;
                }
            }
            Phase::Ended => {}
        }
        out.state = self.state;
        out
    }

    fn output(&self) -> Output {
        Output {
            send: Vec::new(),
            deliver: Vec::new(),
            state: self.state,
        }
    }

    fn fail(&mut self, alert: u8, origin: Origin) {
        self.phase = Phase::Ended;
        self.state = State::Failed(Failure { alert, origin });
    }

    /// Feed the inbox to the current phase once; returns octets consumed.
    fn step(&mut self, out: &mut Output) -> usize {
        match std::mem::replace(&mut self.phase, Phase::Ended) {
            Phase::Hello {
                mut boot,
                scalar,
                verifier,
            } => {
                let (consumed, action) = boot.feed(&self.inbox);
                match action {
                    BootAction::None => {
                        self.phase = Phase::Hello {
                            boot,
                            scalar,
                            verifier,
                        }
                    }
                    // A HelloRetryRequest: ClientHello2, with the dummy
                    // change_cipher_spec before it when required (D.4).
                    BootAction::Send(wire) => {
                        if matches!(boot.acknowledge_send(&wire), BootAction::None) {
                            out.send.extend_from_slice(&wire);
                            self.phase = Phase::Hello {
                                boot,
                                scalar,
                                verifier,
                            };
                        } else {
                            self.fail_plaintext(INTERNAL_ERROR, out);
                        }
                    }
                    BootAction::Established(established) => {
                        self.establish(established, &scalar, verifier, out);
                    }
                    BootAction::Alert(alert) => self.fail(alert, Origin::Peer),
                    BootAction::Fail(alert) => self.fail_plaintext(alert, out),
                    // §6.1: answer close_notify with ours.
                    BootAction::Close => {
                        out.send
                            .extend_from_slice(&plaintext_alert(LEVEL_WARNING, CLOSE_NOTIFY));
                        self.state = State::Closed;
                    }
                }
                consumed
            }
            Phase::Live {
                mut conn,
                mut shadow,
            } => {
                let handshake = conn.mode() == Mode::Handshake;
                let (consumed, action) = conn.feed(&self.inbox);
                let last = match (&mut shadow, handshake) {
                    (Some(s), true) => s.track(self.inbox.get(..consumed).unwrap_or_default()),
                    _ => None,
                };
                self.live(conn, shadow, action, last.as_ref(), out);
                consumed
            }
            Phase::Ended => 0,
        }
    }

    /// A local failure before the handshake keys: a plaintext fatal alert.
    fn fail_plaintext(&mut self, alert: u8, out: &mut Output) {
        out.send
            .extend_from_slice(&plaintext_alert(LEVEL_FATAL, alert));
        self.fail(alert, Origin::Sent);
    }

    /// Phase 2: the key exchange and the handshake epochs, then `Connection`.
    fn establish(
        &mut self,
        established: Established,
        scalar: &[u8],
        verifier: ChainVerifier<'r>,
        out: &mut Output,
    ) {
        let (config, transcript, peer) = established.into_parts();
        let copy = Config {
            host: config.host.clone(),
            now: config.now,
            random: config.random.clone(),
            session_id: config.session_id.clone(),
            public_key: config.public_key.clone(),
        };
        // The driver's own copy of the handshake epochs, from the same
        // inputs and the same verified derivation as the dispatcher's.
        let shadow = clazel_tls::hello::join::derive(
            copy,
            &transcript,
            peer.clone(),
            &Sha256Suite,
            &X25519,
            scalar,
        )
        .ok()
        .and_then(|(secrets, _master)| {
            let sender = Encryptor::new(
                &Sha256Suite,
                &ChaCha20Poly1305Factory,
                &secrets.client_secret,
            )
            .ok()?;
            let receiver = Decryptor::new(
                &Sha256Suite,
                &ChaCha20Poly1305Factory,
                &secrets.server_secret,
            )
            .ok()?;
            Some(Box::new(Shadow {
                sender,
                receiver,
                frame: Vec::new(),
            }))
        });
        // Exactly `Established::into_record_auth`.
        match clazel_tls::traffic::handshake::start(
            config,
            transcript,
            peer,
            &Sha256Suite,
            &X25519,
            &ChaCha20Poly1305Factory,
            scalar,
        ) {
            Ok(keys) => {
                let conn = Connection::new(keys, Sha256Suite, ChaCha20Poly1305Factory, verifier);
                self.phase = Phase::Live {
                    conn: Box::new(conn),
                    shadow,
                };
            }
            Err(alert) => self.fail_plaintext(alert, out),
        }
    }

    /// Carry out one `Connection` action. `last` is the inner type and
    /// content of the record that produced it, during the server's flight.
    fn live(
        &mut self,
        mut conn: Box<Conn<'r>>,
        mut shadow: Option<Box<Shadow>>,
        action: ConnAction,
        last: Option<&(u8, Vec<u8>)>,
        out: &mut Output,
    ) {
        match action {
            ConnAction::None | ConnAction::Ignored | ConnAction::Cancelled => {}
            ConnAction::Send(wire) => {
                // Whatever `Connection` sends first is the client Finished,
                // which takes sequence number 0 of the client handshake
                // epoch: from here the copy must never seal.
                shadow = None;
                let ack = if conn.mode() == Mode::AwaitClientFlight {
                    conn.acknowledge_client_flight(&wire)
                } else {
                    conn.acknowledge_key_update(&wire)
                };
                out.send.extend_from_slice(&wire);
                return self.live(conn, shadow, ack, None, out);
            }
            ConnAction::Ready => self.state = State::Open,
            ConnAction::Deliver(data) => out.deliver.extend_from_slice(&data),
            // §6.1: the server's close_notify; ours follows at once.
            ConnAction::PeerClosed => {
                if self.state == State::Open {
                    self.close_write(&mut conn, out);
                } else {
                    self.state = State::Closed;
                }
            }
            ConnAction::WriteClosed => self.state = State::Closing,
            ConnAction::Close => {
                if let Some(wire) = shadow
                    .as_mut()
                    .and_then(|s| s.seal_alert(LEVEL_WARNING, CLOSE_NOTIFY))
                {
                    out.send.extend_from_slice(&wire);
                }
                self.state = State::Closed;
            }
            ConnAction::Fail(alert) => {
                let from_peer = matches!(last, Some((CT_ALERT, content))
                    if content.get(1) == Some(&alert) && content.len() == 2);
                let origin = if from_peer {
                    Origin::Peer
                } else if let Some(wire) = shadow
                    .as_mut()
                    .and_then(|s| s.seal_alert(LEVEL_FATAL, alert))
                {
                    out.send.extend_from_slice(&wire);
                    Origin::Sent
                } else {
                    Origin::NotSent
                };
                self.fail(alert, origin);
                return;
            }
        }
        if !self.state.is_final() {
            self.phase = Phase::Live { conn, shadow };
        } else {
            self.phase = Phase::Ended;
        }
    }

    /// Our close_notify under the application keys.
    fn close_write(&mut self, conn: &mut Conn<'r>, out: &mut Output) {
        match conn.close_write() {
            ConnAction::Send(wire) => {
                let ack = conn.acknowledge_close_notify(&wire);
                out.send.extend_from_slice(&wire);
                match ack {
                    ConnAction::WriteClosed => self.state = State::Closing,
                    ConnAction::Close => self.state = State::Closed,
                    ConnAction::Fail(alert) => self.fail(alert, Origin::NotSent),
                    _ => self.fail(INTERNAL_ERROR, Origin::NotSent),
                }
            }
            ConnAction::Fail(alert) => self.fail(alert, Origin::NotSent),
            _ => self.fail(INTERNAL_ERROR, Origin::NotSent),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::join::exec::Root;

    fn counter() -> impl FnMut(&mut [u8]) {
        let mut next = 0u8;
        move |out: &mut [u8]| {
            for byte in out.iter_mut() {
                *byte = next;
                next = next.wrapping_add(1);
            }
        }
    }

    fn client() -> (Client<'static>, Output) {
        let verifier = ChainVerifier::new(&[] as &[Root<'static>]);
        Client::connect(
            Host::Dns(b"test.example".to_vec()),
            1_793_448_000,
            verifier,
            &mut counter(),
        )
    }

    #[test]
    fn connect_sends_a_client_hello_and_handshakes() {
        let (client, out) = client();
        assert_eq!(out.state, State::Handshaking);
        assert_eq!(client.state(), State::Handshaking);
        // A handshake record (22) holding a ClientHello (1).
        assert_eq!(out.send.first(), Some(&22));
        assert_eq!(out.send.get(5), Some(&1));
        assert!(out.deliver.is_empty());
    }

    #[test]
    fn bytes_that_are_not_tls_get_a_plaintext_alert() {
        let (mut client, _) = client();
        let out = client.receive(b"HTTP/1.1 400 Bad Request\r\n\r\n");
        assert!(matches!(out.state, State::Failed(_)), "{:?}", out.state);
        let State::Failed(failure) = out.state else {
            return;
        };
        assert_eq!(failure.origin, Origin::Sent);
        assert_eq!(out.send, plaintext_alert(LEVEL_FATAL, failure.alert));
        // Final: nothing more is read or sent.
        let again = client.receive(b"more");
        assert!(again.send.is_empty() && again.deliver.is_empty());
        assert_eq!(again.state, out.state);
    }

    #[test]
    fn a_plaintext_fatal_alert_is_not_answered() {
        let (mut client, _) = client();
        let out = client.receive(&[21, 3, 3, 0, 2, 2, 40]);
        assert_eq!(
            out.state,
            State::Failed(Failure {
                alert: 40,
                origin: Origin::Peer
            })
        );
        assert!(out.send.is_empty());
    }

    #[test]
    fn close_notify_before_the_server_hello_is_answered() {
        let (mut client, _) = client();
        let out = client.receive(&[21, 3, 3, 0, 2, 1, 0]);
        assert_eq!(out.state, State::Closed);
        assert_eq!(out.send, plaintext_alert(LEVEL_WARNING, CLOSE_NOTIFY));
    }

    #[test]
    fn end_of_stream_during_the_handshake_is_truncation() {
        let (mut client, _) = client();
        let out = client.receive_eof();
        assert_eq!(
            out.state,
            State::Failed(Failure {
                alert: INTERNAL_ERROR,
                origin: Origin::Truncated
            })
        );
        assert!(out.send.is_empty());
    }

    #[test]
    fn send_before_the_handshake_is_refused() {
        let (mut client, _) = client();
        assert_eq!(client.send(b"x"), Err(NotOpen(State::Handshaking)));
    }

    #[test]
    fn alert_names() {
        assert_eq!(alert_name(42), Some("bad_certificate"));
        assert_eq!(alert_name(1), None);
        let failure = Failure {
            alert: 42,
            origin: Origin::Peer,
        };
        assert_eq!(failure.to_string(), "bad_certificate (42), from the server");
    }
}
