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
//!    checked by the [`ChainVerifier`], then the client Finished.
//! 4. `clazel_tls::connection::post_handshake_exec::PostHandshake`, the
//!    transducer that `Connection::into_post_handshake` hands over to:
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
//! **Alerts.** On a fatal error the client sends the fatal alert once,
//! where it can (§6.2: an implementation "SHOULD send an appropriate fatal
//! alert"; §6: "MUST send alert X if it sends any alert"), and never answers
//! the server's:
//!
//! - Before the handshake keys (phases 1 and 2) `Bootstrap` puts no alert
//!   on the wire, so this driver writes a plaintext fatal alert record
//!   ([`Origin::Sent`]).
//! - During the server's flight `Connection` seals the alert itself, under
//!   the client handshake epoch at its next sequence number, before it drops
//!   its keys, and returns it in `Fail(description, Some(record))`. The driver
//!   puts that record on the wire as is ([`Origin::Sent`]). It holds no key
//!   of its own. `Fail(description, None)` means `Connection` held no
//!   settled write epoch: nothing is sent ([`Origin::NotSent`]).
//! - After the handshake the transducer does the same: a `Send` of the sealed
//!   alert, then `Fail`. A `Fail` with no `Send` before it sent nothing, as
//!   after our close_notify ([`Origin::NotSent`]).
//! - A fatal alert from the server is never answered ([`Origin::Peer`]):
//!   `Bootstrap` reports it as `Alert`, `Connection` and the transducer as
//!   `PeerAlert`.
//! - The transport ending before close_notify is [`Origin::Truncated`]
//!   (alert 80, `internal_error`, as the machines report it); nothing is
//!   sent.
//! - A close_notify from the server is answered with ours once the
//!   handshake has completed (§6.1: "Each party MUST send a "close_notify"
//!   alert before closing its write side of the connection, unless it has
//!   already sent some error alert"). During the server's protected flight
//!   `Connection` seals it under the client handshake epoch, whether the
//!   server closed or [`Client::close`] was called, and the client stops.
//!
//! The joining itself is `clazel_tls::connection::driver_exec::Driver`, generic
//! over its providers and proven in `driver_contract`. This file fixes the
//! providers and keeps the input buffer: tier 0, plain safe Rust outside
//! `verus!`, tested end to end
//! against rustls (`tests/client.rs`).

use crate::join::exec::ChainVerifier;
use crate::provider::{ChaCha20Poly1305Factory, Sha256Suite, X25519};
use clazel_tls::connection::driver_exec::Driver;
pub use clazel_tls::connection::driver_exec::{Failure, Origin, Output, State, alert_name};
use clazel_tls::hello::client::Config;
use clazel_tls::hello::key_exchange::KeyExchange;
use clazel_tls::host::exec::Host;
use clazel_tls::spec::MAX_PLAINTEXT;

/// The scalar, the ClientHello random and the session id: each 32 octets (the
/// session id for middlebox compatibility, RFC 8446 Appendix D.4).
const RANDOM_LEN: usize = 32;

/// [`Client::send`] was called while the client cannot send application
/// data: the handshake is running, our close_notify was sent, or the
/// connection ended. Nothing changed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NotOpen(pub State);

/// One TLS 1.3 client connection, without its socket. See the module
/// comment.
pub struct Client<'r> {
    driver: Driver<Sha256Suite, X25519, ChaCha20Poly1305Factory, ChainVerifier<'r>>,
    /// Received octets the current machine has not consumed yet.
    inbox: Vec<u8>,
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
        let (driver, out) = Driver::connect(
            config,
            scalar,
            Sha256Suite,
            Sha256Suite,
            X25519,
            ChaCha20Poly1305Factory,
            verifier,
        );
        let inbox = Vec::new();
        (Client { driver, inbox }, out)
    }

    /// Where the connection is.
    pub fn state(&self) -> State {
        self.driver.state()
    }

    /// Octets received from the server.
    pub fn receive(&mut self, bytes: &[u8]) -> Output {
        let mut out = Output {
            send: Vec::new(),
            deliver: Vec::new(),
            state: self.state(),
        };
        if out.state.is_final() {
            return out;
        }
        self.inbox.extend_from_slice(bytes);
        while !self.inbox.is_empty() && !out.state.is_final() {
            let (consumed, step) = self.driver.step(&self.inbox);
            out.send.extend_from_slice(&step.send);
            out.deliver.extend_from_slice(&step.deliver);
            out.state = step.state;
            self.inbox = self.inbox.get(consumed..).unwrap_or_default().to_vec();
            if consumed == 0 {
                break;
            }
        }
        if out.state.is_final() {
            self.inbox.clear();
        }
        out
    }

    /// The server closed the transport (end of stream).
    pub fn receive_eof(&mut self) -> Output {
        self.driver.eof()
    }

    /// Protect application data. Data over 2^14 octets goes out in several
    /// records (RFC 8446 §5.1).
    pub fn send(&mut self, data: &[u8]) -> Result<Output, NotOpen> {
        let state = self.state();
        if state != State::Open {
            return Err(NotOpen(state));
        }
        let mut out = Output {
            send: Vec::new(),
            deliver: Vec::new(),
            state,
        };
        for chunk in data.chunks(MAX_PLAINTEXT) {
            let step = self.driver.send(chunk);
            out.send.extend_from_slice(&step.send);
            out.state = step.state;
            if out.state.is_final() {
                break;
            }
        }
        Ok(out)
    }

    /// Close the connection from our side: close_notify once the handshake
    /// has completed (RFC 8446 §6.1), after which the server's remaining
    /// data is still delivered until its close_notify (`Closing`). Before
    /// the ServerHello the client sends a plaintext close_notify and stops
    /// (`Closed`); during the server's protected flight it seals one under
    /// the client handshake epoch and stops (`Closed`).
    pub fn close(&mut self) -> Output {
        self.driver.close()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::join::exec::Root;
    use clazel_tls::connection::driver_exec::plaintext_alert;
    use clazel_tls::spec::{CLOSE_NOTIFY, INTERNAL_ERROR, LEVEL_FATAL, LEVEL_WARNING};

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
