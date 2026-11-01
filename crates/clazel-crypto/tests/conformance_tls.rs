//! TLS 1.3 end to end (phase-3.md item 3.5g, first part): our client, as
//! production would assemble it, against a real TLS 1.3 server, over an
//! in-memory byte pipe (no sockets).
//!
//! **The client** is `clazel_tls::hello::bootstrap::Bootstrap` (ClientHello,
//! ServerHello), then `Established::into_record_auth` (key exchange and
//! handshake record keys), then `clazel_tls::connection::exec::Connection`
//! (the authentication flight, the client Finished, application data,
//! close_notify), over `clazel_crypto`'s libcrux providers (`Sha256Suite`,
//! `X25519`, `ChaCha20Poly1305Factory`) and the production
//! `join::exec::ChainVerifier`, whose trust anchors are the test root in
//! `tests/fixtures/tls` (production uses `roots::ROOTS` through
//! `join::exec::mozilla`; `ChainVerifier::new` already takes the anchors as a
//! parameter).
//!
//! **The server** is rustls 0.23.46 with its ring provider, restricted to
//! TLS 1.3, `TLS_CHACHA20_POLY1305_SHA256` and X25519 (docs/DEPENDENCIES.md:
//! no new package). Only its X25519 group is replaced, by one with a fixed
//! test scalar, so that the scripted server below can derive the handshake
//! traffic keys.
//!
//! **Randomness is test-only.** The client's X25519 scalar, ClientHello
//! random and legacy_session_id come from [`SEED`] through SHA-256, and so do
//! the server's X25519 scalar. Production has no randomness source yet
//! (clazel-sys); nothing here is a model for one.
//!
//! **The scripted server** (hostile cases) takes the flight a real rustls
//! server produced for the client's real ClientHello, decrypts it with the
//! handshake keys (derived from the transcript and the shared secret by
//! `clazel_tls::schedule`, which the success cases check against rustls),
//! changes one thing, and re-encrypts it. An unchanged flight (the control
//! case) completes the handshake.

// rustls's ring provider is C and assembly, which Miri cannot run.
#![cfg(not(miri))]

use std::io::Cursor;
use std::sync::Arc;

use clazel_crypto::join::exec::{ChainVerifier, Root};
use clazel_crypto::provider::{ChaCha20Poly1305Factory, Sha256Suite, X25519};
use clazel_tls::connection::exec::{Action, Connection, Mode};
use clazel_tls::hello::bootstrap::{Action as BootAction, Bootstrap};
use clazel_tls::hello::client::Config;
use clazel_tls::hello::key_exchange::KeyExchange;
use clazel_tls::host::exec::Host;
use clazel_tls::record::encrypt_record;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::schedule::exec::{
    derive_secret, early_secret, handshake_secret, write_iv, write_key,
};
use clazel_tls::schedule::spec::Label;
use clazel_tls::traffic::exec::{Decryptor, Read};
use clazel_tls::traffic::provider::Factory;
use rustls::crypto::ring::{cipher_suite::TLS13_CHACHA20_POLY1305_SHA256, default_provider};
use rustls::crypto::{ActiveKeyExchange, CryptoProvider, SharedSecret, SupportedKxGroup};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{NamedGroup, ServerConfig, ServerConnection};

type TestResult = Result<(), String>;

// ---------------------------------------------------------------------------
// Fixtures (tests/fixtures/tls/SOURCE.md)
// ---------------------------------------------------------------------------

static ROOT: &[u8] = include_bytes!("fixtures/tls/root.der");
static INTERMEDIATE: &[u8] = include_bytes!("fixtures/tls/intermediate.der");
static LEAF_ECDSA: &[u8] = include_bytes!("fixtures/tls/leaf-ecdsa.der");
static KEY_ECDSA: &[u8] = include_bytes!("fixtures/tls/leaf-ecdsa.key.der");
static LEAF_RSA: &[u8] = include_bytes!("fixtures/tls/leaf-rsa.der");
static KEY_RSA: &[u8] = include_bytes!("fixtures/tls/leaf-rsa.key.der");
static LEAF_OTHER: &[u8] = include_bytes!("fixtures/tls/leaf-other-name.der");
static KEY_OTHER: &[u8] = include_bytes!("fixtures/tls/leaf-other-name.key.der");
static LEAF_EXPIRED: &[u8] = include_bytes!("fixtures/tls/leaf-expired.der");
static KEY_EXPIRED: &[u8] = include_bytes!("fixtures/tls/leaf-expired.key.der");
static INTERMEDIATE_EXPIRED: &[u8] = include_bytes!("fixtures/tls/intermediate-expired.der");
static LEAF_UNDER_EXPIRED: &[u8] =
    include_bytes!("fixtures/tls/leaf-under-expired-intermediate.der");
static SELF_SIGNED: &[u8] = include_bytes!("fixtures/tls/self-signed.der");
static KEY_SELF_SIGNED: &[u8] = include_bytes!("fixtures/tls/self-signed.key.der");

/// 2026-10-31T12:00:00Z, inside every valid fixture's validity.
const NOW: u64 = 1_793_448_000;
const HOST: &[u8] = b"test.example";

// RFC 8446 §6.2 alert descriptions.
const UNEXPECTED_MESSAGE: u8 = 10;
const BAD_RECORD_MAC: u8 = 20;
const RECORD_OVERFLOW: u8 = 22;
const BAD_CERTIFICATE: u8 = 42;
const CERTIFICATE_EXPIRED: u8 = 45;
const UNKNOWN_CA: u8 = 48;
const DECRYPT_ERROR: u8 = 51;
const PROTOCOL_VERSION: u8 = 70;

// ---------------------------------------------------------------------------
// Test-only randomness
// ---------------------------------------------------------------------------

/// TEST-ONLY seed. Every "random" input of both ends derives from it.
const SEED: &[u8] = b"clazel conformance_tls test seed v1: not random, never for production";

fn seeded(label: &str) -> Vec<u8> {
    let mut input = SEED.to_vec();
    input.extend_from_slice(label.as_bytes());
    Sha256Suite.hash(&input)
}

// ---------------------------------------------------------------------------
// Small checked helpers (the workspace forbids indexing and bare arithmetic)
// ---------------------------------------------------------------------------

fn need<T>(value: Option<T>, what: &str) -> Result<T, String> {
    value.ok_or_else(|| what.to_owned())
}

fn byte(bytes: &[u8], at: usize) -> Result<u8, String> {
    need(bytes.get(at).copied(), "byte out of range")
}

fn be16(bytes: &[u8], at: usize) -> Result<usize, String> {
    let next = need(at.checked_add(1), "offset overflow")?;
    Ok(usize::from(byte(bytes, at)?) << 8 | usize::from(byte(bytes, next)?))
}

fn tail(bytes: &[u8], from: usize) -> Result<&[u8], String> {
    need(bytes.get(from..), "tail out of range")
}

fn head(bytes: &[u8], to: usize) -> Result<&[u8], String> {
    need(bytes.get(..to), "head out of range")
}

fn add(a: usize, b: usize) -> Result<usize, String> {
    need(a.checked_add(b), "overflow")
}

/// Split concatenated TLS records into whole records (5-octet header each).
fn split_records(mut bytes: &[u8]) -> Result<Vec<Vec<u8>>, String> {
    let mut out = Vec::new();
    while !bytes.is_empty() {
        let total = add(5, be16(bytes, 3)?)?;
        out.push(head(bytes, total)?.to_vec());
        bytes = tail(bytes, total)?;
    }
    Ok(out)
}

/// Split a handshake byte string into whole messages (4-octet header each).
fn split_messages(mut bytes: &[u8]) -> Result<Vec<Vec<u8>>, String> {
    let mut out = Vec::new();
    while !bytes.is_empty() {
        let len = usize::from(byte(bytes, 1)?) << 16 | be16(bytes, 2)?;
        let total = add(4, len)?;
        out.push(head(bytes, total)?.to_vec());
        bytes = tail(bytes, total)?;
    }
    Ok(out)
}

fn plain_record(ctype: u8, fragment: &[u8]) -> Result<Vec<u8>, String> {
    let len = u16::try_from(fragment.len()).map_err(|e| e.to_string())?;
    let mut out = vec![ctype, 3, 3];
    out.extend_from_slice(&len.to_be_bytes());
    out.extend_from_slice(fragment);
    Ok(out)
}

// ---------------------------------------------------------------------------
// The server: rustls, TLS 1.3, ChaCha20-Poly1305, X25519 with a fixed scalar
// ---------------------------------------------------------------------------

fn server_scalar() -> Vec<u8> {
    seeded("server x25519 scalar")
}

#[derive(Debug)]
struct FixedX25519;

struct FixedActive {
    public: Vec<u8>,
}

static FIXED_X25519: FixedX25519 = FixedX25519;

impl SupportedKxGroup for FixedX25519 {
    fn start(&self) -> Result<Box<dyn ActiveKeyExchange>, rustls::Error> {
        Ok(Box::new(FixedActive {
            public: X25519.public_key(&server_scalar()),
        }))
    }

    fn name(&self) -> NamedGroup {
        NamedGroup::X25519
    }
}

impl ActiveKeyExchange for FixedActive {
    fn complete(self: Box<Self>, peer_pub_key: &[u8]) -> Result<SharedSecret, rustls::Error> {
        match X25519.shared_secret(&server_scalar(), peer_pub_key) {
            Some(shared) => Ok(SharedSecret::from(shared.as_slice())),
            None => Err(rustls::Error::General("x25519 refused".to_owned())),
        }
    }

    fn pub_key(&self) -> &[u8] {
        &self.public
    }

    fn group(&self) -> NamedGroup {
        NamedGroup::X25519
    }
}

/// A server chain: the certificates it sends (leaf first) and the leaf key.
struct ServerCert {
    chain: Vec<&'static [u8]>,
    key: &'static [u8],
}

fn ecdsa_chain() -> ServerCert {
    ServerCert {
        chain: vec![LEAF_ECDSA, INTERMEDIATE],
        key: KEY_ECDSA,
    }
}

fn rsa_chain() -> ServerCert {
    ServerCert {
        chain: vec![LEAF_RSA, INTERMEDIATE],
        key: KEY_RSA,
    }
}

fn server_config(cert: &ServerCert) -> Result<Arc<ServerConfig>, String> {
    let provider = CryptoProvider {
        cipher_suites: vec![TLS13_CHACHA20_POLY1305_SHA256],
        kx_groups: vec![&FIXED_X25519],
        ..default_provider()
    };
    let chain = cert
        .chain
        .iter()
        .map(|der| CertificateDer::from(der.to_vec()))
        .collect();
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(cert.key.to_vec()));
    let config = ServerConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .map_err(|e| e.to_string())?
        .with_no_client_auth()
        .with_single_cert(chain, key)
        .map_err(|e| e.to_string())?;
    Ok(Arc::new(config))
}

struct Server {
    conn: ServerConnection,
}

impl Server {
    fn new(cert: &ServerCert) -> Result<Self, String> {
        let conn = ServerConnection::new(server_config(cert)?).map_err(|e| e.to_string())?;
        Ok(Server { conn })
    }

    /// Give the server octets from the client; every rustls error is returned.
    fn feed(&mut self, bytes: &[u8]) -> TestResult {
        let mut cursor = Cursor::new(bytes);
        // Stop at the end of `bytes`: a read of 0 octets tells rustls that
        // the transport closed.
        while usize::try_from(cursor.position()).map_err(|e| e.to_string())? < bytes.len() {
            let n = self.conn.read_tls(&mut cursor).map_err(|e| e.to_string())?;
            if n == 0 {
                return Ok(());
            }
            self.conn
                .process_new_packets()
                .map_err(|e| format!("rustls server: {e}"))?;
        }
        Ok(())
    }

    /// Everything the server wants to send.
    fn take(&mut self) -> Result<Vec<u8>, String> {
        let mut out = Vec::new();
        while self.conn.wants_write() {
            self.conn.write_tls(&mut out).map_err(|e| e.to_string())?;
        }
        Ok(out)
    }

    /// Plaintext application data the server has received.
    fn read_plaintext(&mut self) -> Result<Vec<u8>, String> {
        use std::io::Read as _;
        let mut out = Vec::new();
        let mut buf = [0u8; 4096];
        loop {
            match self.conn.reader().read(&mut buf) {
                Ok(0) => return Ok(out),
                Ok(n) => out.extend_from_slice(head(&buf, n)?),
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => return Ok(out),
                Err(e) => return Err(format!("server read: {e}")),
            }
        }
    }

    fn write_plaintext(&mut self, data: &[u8]) -> TestResult {
        use std::io::Write as _;
        self.conn
            .writer()
            .write_all(data)
            .map_err(|e| e.to_string())
    }
}

// ---------------------------------------------------------------------------
// The client, assembled as production would
// ---------------------------------------------------------------------------

type Conn = Connection<Sha256Suite, ChaCha20Poly1305Factory, ChainVerifier<'static>>;

#[derive(Debug, PartialEq, Eq)]
enum Event {
    /// Octets the client sends to the server (already acknowledged).
    Send(Vec<u8>),
    /// The application epochs are installed.
    Ready,
    /// Application plaintext released.
    Deliver(Vec<u8>),
    /// The peer's close_notify.
    PeerClosed,
    /// Both directions closed: the peer's close_notify after ours.
    Closed,
    /// Fatal: the dispatcher's alert description.
    Fail(u8),
    /// An alert the peer sent before the handshake keys.
    PeerAlert(u8),
    /// Anything else of interest.
    Other(String),
}

enum Phase {
    Boot(Box<Bootstrap<Sha256Suite>>),
    Live(Box<Conn>),
    Done,
}

struct Client {
    phase: Phase,
    inbox: Vec<u8>,
    scalar: Vec<u8>,
    verifier: Option<ChainVerifier<'static>>,
    public: Vec<u8>,
}

fn anchors() -> ChainVerifier<'static> {
    ChainVerifier::new(&[Root {
        der: ROOT,
        server_distrust_after: None,
    }])
}

impl Client {
    /// Returns the client and its ClientHello record. `anchors` is the trust
    /// store.
    fn start(verifier: ChainVerifier<'static>) -> Result<(Self, Vec<u8>), String> {
        let scalar = seeded("client x25519 scalar");
        let public = X25519.public_key(&scalar);
        let config = Config {
            host: Host::Dns(HOST.to_vec()),
            now: NOW,
            random: seeded("client hello random"),
            session_id: seeded("client legacy_session_id"),
            public_key: public.clone(),
        };
        let (boot, action) = Bootstrap::start(config, Sha256Suite)
            .map_err(|alert| format!("Bootstrap::start alert {alert}"))?;
        let wire = match action {
            BootAction::Send(wire) => wire,
            _ => return Err("Bootstrap::start did not send".to_owned()),
        };
        let mut client = Client {
            phase: Phase::Boot(Box::new(boot)),
            inbox: Vec::new(),
            scalar,
            verifier: Some(verifier),
            public,
        };
        if let Phase::Boot(boot) = &mut client.phase {
            match boot.acknowledge_send(&wire) {
                BootAction::None => {}
                _ => return Err("ClientHello acknowledgement refused".to_owned()),
            }
        }
        Ok((client, wire))
    }

    /// Feed octets from the server; run the dispatcher until it needs more.
    fn receive(&mut self, bytes: &[u8]) -> Result<Vec<Event>, String> {
        self.inbox.extend_from_slice(bytes);
        let mut events = Vec::new();
        while !self.inbox.is_empty() {
            let input = std::mem::take(&mut self.inbox);
            let phase = std::mem::replace(&mut self.phase, Phase::Done);
            let (consumed, stop) = match phase {
                Phase::Boot(mut boot) => {
                    let (consumed, action) = boot.feed(&input);
                    let mut stop = false;
                    self.phase = Phase::Boot(boot);
                    match action {
                        BootAction::None => {}
                        BootAction::Send(wire) => {
                            events.push(Event::Send(wire.clone()));
                            if let Phase::Boot(boot) = &mut self.phase {
                                boot.acknowledge_send(&wire);
                            }
                        }
                        BootAction::Established(established) => {
                            let keys = established.into_record_auth(
                                &Sha256Suite,
                                &X25519,
                                &ChaCha20Poly1305Factory,
                                &self.scalar,
                            );
                            match keys {
                                Ok(keys) => {
                                    let verifier = need(self.verifier.take(), "verifier used")?;
                                    self.phase = Phase::Live(Box::new(Connection::new(
                                        keys,
                                        Sha256Suite,
                                        ChaCha20Poly1305Factory,
                                        verifier,
                                    )));
                                }
                                Err(alert) => {
                                    events.push(Event::Fail(alert));
                                    stop = true;
                                }
                            }
                        }
                        BootAction::Alert(alert) => {
                            events.push(Event::PeerAlert(alert));
                            stop = true;
                        }
                        BootAction::Fail(alert) => {
                            events.push(Event::Fail(alert));
                            stop = true;
                        }
                        BootAction::Close => {
                            events.push(Event::PeerClosed);
                            stop = true;
                        }
                    }
                    (consumed, stop)
                }
                Phase::Live(mut conn) => {
                    let (consumed, action) = conn.feed(&input);
                    let stop = Self::live_action(conn.as_mut(), action, &mut events);
                    self.phase = Phase::Live(conn);
                    (consumed, stop)
                }
                Phase::Done => return Err("input after the client ended".to_owned()),
            };
            if stop {
                self.inbox.clear();
                return Ok(events);
            }
            let rest = tail(&input, consumed)?;
            self.inbox = rest.to_vec();
            if consumed == 0 {
                break;
            }
        }
        Ok(events)
    }

    /// Record one dispatcher action. Every `Send` is acknowledged at once, as
    /// the network shell does after the write completes. True when fatal.
    fn live_action(conn: &mut Conn, action: Action, events: &mut Vec<Event>) -> bool {
        match action {
            Action::None | Action::Ignored => false,
            Action::Send(wire) => {
                events.push(Event::Send(wire.clone()));
                let ack = if conn.mode() == Mode::AwaitClientFlight {
                    conn.acknowledge_client_flight(&wire)
                } else {
                    conn.acknowledge_key_update(&wire)
                };
                Self::live_action(conn, ack, events)
            }
            Action::Ready => {
                events.push(Event::Ready);
                false
            }
            Action::Deliver(data) => {
                events.push(Event::Deliver(data));
                false
            }
            Action::PeerClosed => {
                events.push(Event::PeerClosed);
                false
            }
            Action::Fail(alert) => {
                events.push(Event::Fail(alert));
                true
            }
            Action::Close => {
                events.push(Event::Closed);
                false
            }
            other => {
                events.push(Event::Other(format!("{other:?}")));
                false
            }
        }
    }

    fn conn(&mut self) -> Result<&mut Conn, String> {
        match &mut self.phase {
            Phase::Live(conn) => Ok(conn.as_mut()),
            _ => Err("client is not past the Hello exchange".to_owned()),
        }
    }

    fn send_application(&mut self, data: &[u8]) -> Result<Vec<u8>, String> {
        match self.conn()?.send_application(data, 0) {
            Action::Send(wire) => Ok(wire),
            other => Err(format!("send_application gave {other:?}")),
        }
    }

    fn close_write(&mut self) -> Result<Vec<u8>, String> {
        let conn = self.conn()?;
        match conn.close_write() {
            Action::Send(wire) => match conn.acknowledge_close_notify(&wire) {
                Action::WriteClosed => Ok(wire),
                other => Err(format!("acknowledge_close_notify gave {other:?}")),
            },
            other => Err(format!("close_write gave {other:?}")),
        }
    }

    fn mode(&mut self) -> Result<Mode, String> {
        Ok(self.conn()?.mode())
    }
}

fn sends(events: &[Event]) -> Vec<u8> {
    events
        .iter()
        .filter_map(|event| match event {
            Event::Send(bytes) => Some(bytes.as_slice()),
            _ => None,
        })
        .flatten()
        .copied()
        .collect()
}

/// Run the pipe until neither side has anything to say.
fn pump(client: &mut Client, server: &mut Server, first: Vec<u8>) -> Result<Vec<Event>, String> {
    let mut all = Vec::new();
    let mut to_server = first;
    for _ in 0..32 {
        server.feed(&to_server)?;
        let from_server = server.take()?;
        if from_server.is_empty() {
            return Ok(all);
        }
        let events = client.receive(&from_server)?;
        to_server = sends(&events);
        let fatal = events
            .iter()
            .any(|event| matches!(event, Event::Fail(_) | Event::PeerAlert(_)));
        all.extend(events);
        if fatal {
            return Ok(all);
        }
    }
    Err("the pipe did not quiesce".to_owned())
}

/// A full handshake against rustls with `cert`; the client is `Ready`.
fn connect(cert: &ServerCert) -> Result<(Client, Server), String> {
    let mut server = Server::new(cert)?;
    let (mut client, hello) = Client::start(anchors())?;
    let events = pump(&mut client, &mut server, hello)?;
    if !events.contains(&Event::Ready) {
        return Err(format!("no Ready; events: {events:?}"));
    }
    if server.conn.is_handshaking() {
        return Err("rustls still handshaking after the client's Finished".to_owned());
    }
    if client.mode()? != Mode::Ready {
        return Err("client is not Ready".to_owned());
    }
    // The profile (phase-3.md 3.0): TLS 1.3 and ChaCha20-Poly1305 only.
    if server.conn.protocol_version() != Some(rustls::ProtocolVersion::TLSv1_3)
        || server.conn.negotiated_cipher_suite().map(|s| s.suite())
            != Some(rustls::CipherSuite::TLS13_CHACHA20_POLY1305_SHA256)
    {
        return Err("rustls negotiated something else".to_owned());
    }
    Ok((client, server))
}

// ---------------------------------------------------------------------------
// Success cases
// ---------------------------------------------------------------------------

fn application_round_trip(cert: &ServerCert) -> TestResult {
    let (mut client, mut server) = connect(cert)?;
    // The server's first application data. (rustls sends no NewSessionTicket
    // to this client: it offers no psk_key_exchange_modes, RFC 8446 §4.2.9.)
    server.write_plaintext(b"HTTP/1.1 200 OK\r\ncontent-length: 2\r\n\r\nok")?;
    let from_server = server.take()?;
    let events = client.receive(&from_server)?;
    let delivered: Vec<u8> = events
        .iter()
        .filter_map(|event| match event {
            Event::Deliver(bytes) => Some(bytes.as_slice()),
            _ => None,
        })
        .flatten()
        .copied()
        .collect();
    assert_eq!(delivered, b"HTTP/1.1 200 OK\r\ncontent-length: 2\r\n\r\nok");
    // The client's request.
    let wire = client.send_application(b"GET / HTTP/1.1\r\nhost: test.example\r\n\r\n")?;
    server.feed(&wire)?;
    assert_eq!(
        server.read_plaintext()?,
        b"GET / HTTP/1.1\r\nhost: test.example\r\n\r\n"
    );
    // Several records both ways, so the sequence numbers advance.
    for round in 0u8..5 {
        let message = vec![round; 3000];
        server.write_plaintext(&message)?;
        let events = client.receive(&server.take()?)?;
        assert_eq!(events, vec![Event::Deliver(message.clone())]);
        let wire = client.send_application(&message)?;
        server.feed(&wire)?;
        assert_eq!(server.read_plaintext()?, message);
    }
    // close_notify both ways (RFC 8446 §6.1).
    let close = client.close_write()?;
    server.feed(&close)?;
    assert!(server.read_plaintext()?.is_empty());
    server.conn.send_close_notify();
    let events = client.receive(&server.take()?)?;
    assert!(
        events.contains(&Event::Closed),
        "server close_notify not seen: {events:?}"
    );
    Ok(())
}

fn ecdsa_chain_full_handshake_and_application_data() -> TestResult {
    application_round_trip(&ecdsa_chain())
}

fn rsa_chain_full_handshake_and_application_data() -> TestResult {
    application_round_trip(&rsa_chain())
}

fn client_can_request_a_key_update() -> TestResult {
    let (mut client, mut server) = connect(&ecdsa_chain())?;
    let wire = match client.conn()?.request_key_update(true) {
        Action::Send(wire) => wire,
        other => return Err(format!("request_key_update gave {other:?}")),
    };
    server.feed(&wire)?;
    assert_eq!(client.conn()?.acknowledge_key_update(&wire), Action::None);
    // The server answers with its own KeyUpdate (update_requested), then data.
    server.write_plaintext(b"after key update")?;
    let events = client.receive(&server.take()?)?;
    assert!(
        events.contains(&Event::Deliver(b"after key update".to_vec())),
        "{events:?}"
    );
    let reply = client.send_application(b"client after update")?;
    server.feed(&reply)?;
    assert_eq!(server.read_plaintext()?, b"client after update");
    Ok(())
}

// ---------------------------------------------------------------------------
// The scripted server
// ---------------------------------------------------------------------------

/// One element of the server's first flight.
#[derive(Clone, Debug)]
enum Item {
    /// Octets sent as they are (a plaintext record).
    Plain(Vec<u8>),
    /// A record to protect under the server handshake traffic key: the inner
    /// content type and the content (a whole handshake message for type 22).
    Sealed(u8, Vec<u8>),
}

/// The real rustls flight for the client's real ClientHello, decrypted.
struct Flight {
    items: Vec<Item>,
    server_secret: Vec<u8>,
}

fn script(
    cert: &ServerCert,
    client: &Client,
    hello_record: &[u8],
) -> Result<(Flight, Server), String> {
    let mut server = Server::new(cert)?;
    server.feed(hello_record)?;
    let wire = server.take()?;
    let records = split_records(&wire)?;
    let server_hello = need(records.first(), "no ServerHello record")?;
    // RFC 8446 §7.1 / Appendix A: the transcript is ClientHello || ServerHello.
    let mut transcript = tail(hello_record, 5)?.to_vec();
    transcript.extend_from_slice(tail(server_hello, 5)?);
    let shared = need(
        X25519.shared_secret(&server_scalar(), &client.public),
        "server DH refused",
    )?;
    let early = early_secret(&Sha256Suite);
    let handshake = handshake_secret(&Sha256Suite, &early, &shared);
    let server_secret = derive_secret(
        &Sha256Suite,
        &handshake,
        Label::ServerHandshake,
        &transcript,
    );
    let mut reader = Decryptor::new(&Sha256Suite, &ChaCha20Poly1305Factory, &server_secret)
        .map_err(|alert| format!("decryptor alert {alert}"))?;
    let mut items = vec![Item::Plain(server_hello.clone())];
    for record in records.iter().skip(1) {
        match byte(record, 0)? {
            20 => items.push(Item::Plain(record.clone())),
            23 => match reader.open(record) {
                Read::Record(22, content, _) => {
                    for message in split_messages(&content)? {
                        items.push(Item::Sealed(22, message));
                    }
                }
                other => {
                    return Err(format!(
                        "flight record did not open as handshake: {other:?}"
                    ));
                }
            },
            other => return Err(format!("unexpected server record type {other}")),
        }
    }
    Ok((
        Flight {
            items,
            server_secret,
        },
        server,
    ))
}

impl Flight {
    fn wire(&self) -> Result<Vec<u8>, String> {
        // RFC 8446 §7.3 keys, §5.3 nonces. `Encryptor::seal` refuses inner
        // types the client would never send (change_cipher_spec), so the
        // records are protected with `record::encrypt_record` directly.
        let key = write_key(&Sha256Suite, &self.server_secret);
        let iv = write_iv(&Sha256Suite, &self.server_secret);
        let aead = ChaCha20Poly1305Factory.make(&key);
        let mut sequence: u64 = 0;
        let mut out = Vec::new();
        for item in &self.items {
            match item {
                Item::Plain(bytes) => out.extend_from_slice(bytes),
                Item::Sealed(ctype, content) => {
                    out.extend_from_slice(&encrypt_record(
                        &aead, &iv, sequence, *ctype, content, 0,
                    ));
                    sequence = need(sequence.checked_add(1), "sequence overflow")?;
                }
            }
        }
        Ok(out)
    }

    /// The index of the first sealed handshake message of this type.
    fn find(&self, handshake_type: u8) -> Result<usize, String> {
        for (at, item) in self.items.iter().enumerate() {
            if let Item::Sealed(22, message) = item
                && byte(message, 0)? == handshake_type
            {
                return Ok(at);
            }
        }
        Err(format!("no handshake message of type {handshake_type}"))
    }

    fn flip_last_byte(&mut self, handshake_type: u8) -> TestResult {
        let at = self.find(handshake_type)?;
        match self.items.get_mut(at) {
            Some(Item::Sealed(_, message)) => match message.last_mut() {
                Some(last) => {
                    *last ^= 0x01;
                    Ok(())
                }
                None => Err("empty message".to_owned()),
            },
            _ => Err("not a sealed item".to_owned()),
        }
    }

    fn insert(&mut self, at: usize, item: Item) -> TestResult {
        if at > self.items.len() {
            return Err("insert out of range".to_owned());
        }
        self.items.insert(at, item);
        Ok(())
    }
}

/// Run the scripted server: the changed flight goes to a fresh client.
fn run_scripted(
    cert: &ServerCert,
    change: impl FnOnce(&mut Flight) -> TestResult,
) -> Result<(Vec<Event>, Client, Server), String> {
    let (mut client, hello) = Client::start(anchors())?;
    // `server` is the rustls instance whose flight is changed, so that it can
    // read the client's answer when the changed flight is still accepted.
    let (mut flight, server) = script(cert, &client, &hello)?;
    change(&mut flight)?;
    let wire = flight.wire()?;
    let events = client.receive(&wire)?;
    Ok((events, client, server))
}

fn last_event(events: &[Event]) -> Option<&Event> {
    events.last()
}

fn scripted_server_control_completes_the_handshake() -> TestResult {
    for cert in [ecdsa_chain(), rsa_chain()] {
        let (events, _client, mut server) = run_scripted(&cert, |_| Ok(()))?;
        assert!(events.contains(&Event::Ready), "{events:?}");
        // The re-encrypted flight is byte-identical in content, so the real
        // rustls server accepts the client's answer.
        server.feed(&sends(&events))?;
        assert!(!server.conn.is_handshaking());
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Hostile servers
// ---------------------------------------------------------------------------

fn wrong_finished_is_decrypt_error() -> TestResult {
    let (events, mut client, _) = run_scripted(&ecdsa_chain(), |f| f.flip_last_byte(20))?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(DECRYPT_ERROR)),
        "{events:?}"
    );
    assert!(!events.contains(&Event::Ready));
    // Nothing is sent afterwards.
    assert_eq!(client.mode()?, Mode::Failed);
    Ok(())
}

fn wrong_certificate_verify_is_decrypt_error() -> TestResult {
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| f.flip_last_byte(15))?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(DECRYPT_ERROR)),
        "{events:?}"
    );
    let (events, _, _) = run_scripted(&rsa_chain(), |f| f.flip_last_byte(15))?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(DECRYPT_ERROR)),
        "{events:?}"
    );
    Ok(())
}

/// A real handshake against a rustls server whose certificate is the problem.
fn refused_with(cert: &ServerCert, alert: u8) -> TestResult {
    let mut server = Server::new(cert)?;
    let (mut client, hello) = Client::start(anchors())?;
    let events = pump(&mut client, &mut server, hello)?;
    assert_eq!(last_event(&events), Some(&Event::Fail(alert)), "{events:?}");
    assert!(!events.contains(&Event::Ready));
    assert_eq!(client.mode()?, Mode::Failed);
    Ok(())
}

fn certificate_for_another_name_is_bad_certificate() -> TestResult {
    refused_with(
        &ServerCert {
            chain: vec![LEAF_OTHER, INTERMEDIATE],
            key: KEY_OTHER,
        },
        BAD_CERTIFICATE,
    )
}

fn expired_leaf_is_bad_certificate() -> TestResult {
    // The search's first candidate fails the leaf profile, which covers the
    // leaf's validity, so an expired leaf is bad_certificate (42), not
    // certificate_expired (45): tests/join.rs `an_expired_leaf_is_refused`
    // and clazel-x509's path/search/spec.rs say the same. RFC 8446 §6.2 words
    // certificate_expired as "expired or is not currently valid", so 45 would
    // also be right; both are fatal.
    refused_with(
        &ServerCert {
            chain: vec![LEAF_EXPIRED, INTERMEDIATE],
            key: KEY_EXPIRED,
        },
        BAD_CERTIFICATE,
    )
}

fn expired_intermediate_is_certificate_expired() -> TestResult {
    refused_with(
        &ServerCert {
            chain: vec![LEAF_UNDER_EXPIRED, INTERMEDIATE_EXPIRED],
            key: KEY_ECDSA,
        },
        CERTIFICATE_EXPIRED,
    )
}

fn self_signed_leaf_is_unknown_ca() -> TestResult {
    refused_with(
        &ServerCert {
            chain: vec![SELF_SIGNED],
            key: KEY_SELF_SIGNED,
        },
        UNKNOWN_CA,
    )
}

fn missing_intermediate_is_unknown_ca() -> TestResult {
    refused_with(
        &ServerCert {
            chain: vec![LEAF_ECDSA],
            key: KEY_ECDSA,
        },
        UNKNOWN_CA,
    )
}

fn empty_trust_store_refuses_a_valid_chain() -> TestResult {
    let mut server = Server::new(&ecdsa_chain())?;
    let (mut client, hello) = Client::start(ChainVerifier::new(&[]))?;
    let events = pump(&mut client, &mut server, hello)?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(UNKNOWN_CA)),
        "{events:?}"
    );
    Ok(())
}

/// Plaintext handshake record of the length given (not a real message).
fn handshake_record_of(len: usize) -> Result<Vec<u8>, String> {
    let n = u16::try_from(len).map_err(|e| e.to_string())?;
    let mut out = vec![22, 3, 3];
    out.extend_from_slice(&n.to_be_bytes());
    out.extend(std::iter::repeat_n(0u8, len));
    Ok(out)
}

fn application_record_of(len: usize) -> Result<Vec<u8>, String> {
    let n = u16::try_from(len).map_err(|e| e.to_string())?;
    let mut out = vec![23, 3, 3];
    out.extend_from_slice(&n.to_be_bytes());
    out.extend(std::iter::repeat_n(0u8, len));
    Ok(out)
}

fn oversized_records_are_record_overflow() -> TestResult {
    // RFC 8446 §5.1: a plaintext record over 2^14 octets.
    let (mut client, _) = Client::start(anchors())?;
    let events = client.receive(&handshake_record_of(16_385)?)?;
    assert_eq!(events, vec![Event::Fail(RECORD_OVERFLOW)]);
    // §5.2: a protected record over 2^14 + 256 octets, after a real ServerHello.
    for len in [16_641usize, 65_535] {
        let (events, _, _) = run_scripted(&ecdsa_chain(), |f| {
            f.insert(2, Item::Plain(application_record_of(len)?))
        })?;
        assert_eq!(
            last_event(&events),
            Some(&Event::Fail(RECORD_OVERFLOW)),
            "{len}: {events:?}"
        );
    }
    // The limit itself is a well-formed record; the AEAD then refuses its
    // contents (§5.2: bad_record_mac), not the framing.
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| {
        f.insert(2, Item::Plain(application_record_of(16_640)?))
    })?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(BAD_RECORD_MAC)),
        "{events:?}"
    );
    Ok(())
}

/// The ServerHello message of the flight with its extension `extension_type`
/// removed (RFC 8446 §4.1.3 structure), as a plaintext record.
fn server_hello_without(flight: &Flight, extension_type: u16) -> Result<Vec<u8>, String> {
    let record = match flight.items.first() {
        Some(Item::Plain(record)) => record,
        _ => return Err("no ServerHello".to_owned()),
    };
    let message = tail(record, 5)?;
    let body = tail(message, 4)?;
    let session_len = usize::from(byte(body, 34)?);
    let ext_at = add(add(35, session_len)?, 3)?;
    let ext_len = be16(body, ext_at)?;
    let fixed = head(body, add(ext_at, 2)?)?;
    let mut extensions = Vec::new();
    let mut rest = head(tail(body, add(ext_at, 2)?)?, ext_len)?;
    while !rest.is_empty() {
        let kind = be16(rest, 0)?;
        let total = add(4, be16(rest, 2)?)?;
        if kind != usize::from(extension_type) {
            extensions.extend_from_slice(head(rest, total)?);
        }
        rest = tail(rest, total)?;
    }
    let mut new_body = head(fixed, ext_at)?.to_vec();
    new_body.extend_from_slice(
        &u16::try_from(extensions.len())
            .map_err(|e| e.to_string())?
            .to_be_bytes(),
    );
    new_body.extend_from_slice(&extensions);
    let mut new_message = vec![2];
    let len = u32::try_from(new_body.len()).map_err(|e| e.to_string())?;
    new_message.extend_from_slice(tail(&len.to_be_bytes(), 1)?);
    new_message.extend_from_slice(&new_body);
    plain_record(22, &new_message)
}

fn tls12_server_hello_is_refused() -> TestResult {
    // A ServerHello without supported_versions is a TLS 1.2 (or lower)
    // selection (RFC 8446 §4.2.1); the client offered only 1.3.
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| {
        let record = server_hello_without(f, 43)?;
        match f.items.first_mut() {
            Some(first) => *first = Item::Plain(record),
            None => return Err("empty flight".to_owned()),
        }
        Ok(())
    })?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(PROTOCOL_VERSION)),
        "{events:?}"
    );
    Ok(())
}

fn downgrade_sentinel_is_protocol_version() -> TestResult {
    // RFC 8446 §4.1.3: ServerHello.random ends in "DOWNGRD\x01" (a TLS 1.2
    // selection by a server that supports 1.3), which a client that supports
    // TLS 1.2 must refuse with illegal_parameter. This client offers only
    // 1.3 and clazel-tls's hello/spec.rs classifies every ServerHello without
    // supported_versions as protocol_version before it reads the random, so
    // the sentinel is not looked at: the alert differs from §4.1.3's literal
    // text (both are fatal). Reported in phase-3.md 3.5g, not changed here.
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| {
        let mut record = server_hello_without(f, 43)?;
        // header(5) + handshake header(4) + version(2) + random(32): the
        // random's last eight octets end at offset 43.
        let sentinel = b"DOWNGRD\x01";
        let slot = record.get_mut(35..43).ok_or("short ServerHello")?;
        slot.copy_from_slice(sentinel);
        match f.items.first_mut() {
            Some(first) => *first = Item::Plain(record),
            None => return Err("empty flight".to_owned()),
        }
        Ok(())
    })?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(PROTOCOL_VERSION)),
        "{events:?}"
    );
    Ok(())
}

const CCS: [u8; 6] = [20, 3, 3, 0, 1, 1];

fn change_cipher_spec_in_the_wrong_place_is_unexpected_message() -> TestResult {
    // RFC 8446 §5: a CCS must be the single octet 0x01; anything else is
    // unexpected_message.
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| {
        f.insert(1, Item::Plain(vec![20, 3, 3, 0, 1, 2]))
    })?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(UNEXPECTED_MESSAGE)),
        "{events:?}"
    );

    // A CCS of two octets.
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| {
        f.insert(1, Item::Plain(vec![20, 3, 3, 0, 2, 1, 1]))
    })?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(UNEXPECTED_MESSAGE)),
        "{events:?}"
    );

    // A CCS between the fragments of one handshake message (§5.1; the
    // erratum in docs/ERRATA.md): the ServerHello split in two.
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| {
        let record = match f.items.first() {
            Some(Item::Plain(record)) => record.clone(),
            _ => return Err("no ServerHello".to_owned()),
        };
        let message = tail(&record, 5)?;
        let first = plain_record(22, head(message, 10)?)?;
        let second = plain_record(22, tail(message, 10)?)?;
        match f.items.first_mut() {
            Some(slot) => *slot = Item::Plain(first),
            None => return Err("empty flight".to_owned()),
        }
        f.insert(1, Item::Plain(CCS.to_vec()))?;
        f.insert(2, Item::Plain(second))
    })?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(UNEXPECTED_MESSAGE)),
        "{events:?}"
    );

    // A protected record whose inner type is change_cipher_spec (§5.2:
    // handshake epochs carry handshake, alert and application_data only).
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| f.insert(2, Item::Sealed(20, vec![1])))?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(UNEXPECTED_MESSAGE)),
        "{events:?}"
    );

    // A plaintext CCS after the server's Finished has been received: §5 allows
    // the drop only before the peer's Finished.
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| {
        let end = f.items.len();
        f.insert(end, Item::Plain(CCS.to_vec()))
    })?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(UNEXPECTED_MESSAGE)),
        "{events:?}"
    );
    Ok(())
}

fn compatibility_change_cipher_spec_where_rfc_8446_allows_it_is_dropped() -> TestResult {
    // The control for the CCS cases above: rustls's own CCS after the
    // ServerHello is dropped (§5), and so is one before the ServerHello.
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| f.insert(0, Item::Plain(CCS.to_vec())))?;
    assert!(events.contains(&Event::Ready), "{events:?}");
    let (events, _, _) = run_scripted(&ecdsa_chain(), |f| f.insert(3, Item::Plain(CCS.to_vec())))?;
    assert!(events.contains(&Event::Ready), "{events:?}");
    Ok(())
}

// ---------------------------------------------------------------------------
// The runner (xtask/src/conformance.rs: one summary line per suite)
// ---------------------------------------------------------------------------

type Case = (&'static str, fn() -> TestResult);

const SUCCESS: &[Case] = &[
    (
        "ecdsa_chain_full_handshake_and_application_data",
        ecdsa_chain_full_handshake_and_application_data,
    ),
    (
        "rsa_chain_full_handshake_and_application_data",
        rsa_chain_full_handshake_and_application_data,
    ),
    (
        "client_can_request_a_key_update",
        client_can_request_a_key_update,
    ),
    (
        "scripted_server_control_completes_the_handshake",
        scripted_server_control_completes_the_handshake,
    ),
    (
        "compatibility_change_cipher_spec_where_rfc_8446_allows_it_is_dropped",
        compatibility_change_cipher_spec_where_rfc_8446_allows_it_is_dropped,
    ),
];

const HOSTILE: &[Case] = &[
    (
        "wrong_finished_is_decrypt_error",
        wrong_finished_is_decrypt_error,
    ),
    (
        "wrong_certificate_verify_is_decrypt_error",
        wrong_certificate_verify_is_decrypt_error,
    ),
    (
        "certificate_for_another_name_is_bad_certificate",
        certificate_for_another_name_is_bad_certificate,
    ),
    (
        "expired_leaf_is_bad_certificate",
        expired_leaf_is_bad_certificate,
    ),
    (
        "expired_intermediate_is_certificate_expired",
        expired_intermediate_is_certificate_expired,
    ),
    (
        "self_signed_leaf_is_unknown_ca",
        self_signed_leaf_is_unknown_ca,
    ),
    (
        "missing_intermediate_is_unknown_ca",
        missing_intermediate_is_unknown_ca,
    ),
    (
        "empty_trust_store_refuses_a_valid_chain",
        empty_trust_store_refuses_a_valid_chain,
    ),
    (
        "oversized_records_are_record_overflow",
        oversized_records_are_record_overflow,
    ),
    (
        "tls12_server_hello_is_refused",
        tls12_server_hello_is_refused,
    ),
    (
        "downgrade_sentinel_is_protocol_version",
        downgrade_sentinel_is_protocol_version,
    ),
    (
        "change_cipher_spec_in_the_wrong_place_is_unexpected_message",
        change_cipher_spec_in_the_wrong_place_is_unexpected_message,
    ),
];

/// Run a suite; a panic or an `Err` is a failure, reported by name.
fn run_suite(name: &str, cases: &[Case]) -> Vec<String> {
    let mut failed = Vec::new();
    for (case, run) in cases {
        match std::panic::catch_unwind(run) {
            Ok(Ok(())) => {}
            Ok(Err(message)) => failed.push(format!("{case}: {message}")),
            Err(_) => failed.push(format!("{case}: panicked")),
        }
    }
    println!(
        "clazel-conformance: suite=\"{name}\" pass={} xfail=0 fail={} total={}",
        cases.len().saturating_sub(failed.len()),
        failed.len(),
        cases.len()
    );
    failed
}

#[test]
fn tls_1_3_end_to_end() {
    let mut failed = run_suite(
        "TLS 1.3 client against rustls (ring), ECDSA and RSA chains, scripted control",
        SUCCESS,
    );
    failed.extend(run_suite(
        "TLS 1.3 hostile servers, RFC 8446 section 6.2 alerts",
        HOSTILE,
    ));
    assert!(failed.is_empty(), "failed: {failed:#?}");
}
