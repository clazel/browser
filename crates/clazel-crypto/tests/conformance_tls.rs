//! TLS 1.3 end to end (phase-3.md item 3.5g, first part): our client, as
//! production would assemble it, against a real TLS 1.3 server, over an
//! in-memory byte pipe (no sockets).
//!
//! **The client** is production's: `clazel_crypto::client::Client`, the
//! driver `clazel_net::TlsConnection` runs, over `clazel_crypto`'s libcrux
//! providers and `join::exec::ChainVerifier`, whose trust anchors are the test
//! roots in `tests/fixtures/tls` (production uses `roots::ROOTS` through
//! `join::exec::mozilla`; `ChainVerifier::new` already takes the anchors as a
//! parameter). [`Client`] here only turns its outputs into [`Event`]s.
//!
//! **The server** is rustls 0.23.46 with its ring provider, restricted to
//! TLS 1.3, `TLS_CHACHA20_POLY1305_SHA256` and X25519 (docs/DEPENDENCIES.md:
//! no new package). Only its X25519 group is replaced, by one with a fixed
//! test scalar, so that the scripted server below can derive the handshake
//! traffic keys.
//!
//! **Randomness is test-only.** The client's X25519 scalar, ClientHello
//! random and legacy_session_id come from [`SEED`] through SHA-256, and so does
//! the server's X25519 scalar. Production draws them from
//! `clazel_sys::fill_random`; nothing here is a model for that.
//!
//! **The scripted server** (hostile cases) takes the flight a real rustls
//! server produced for the client's real ClientHello, decrypts it with the
//! handshake keys (derived from the transcript and the shared secret by
//! `clazel_tls::schedule`, which the success cases check against rustls),
//! changes one thing, and re-encrypts it. An unchanged flight (the control
//! case) completes the handshake.
//!
//! **What rustls cannot be made to do** (phase-3.md 3.5g, each case says so):
//!
//! - *HelloRetryRequest.* This client offers X25519 and a key share for it, so
//!   a server that speaks X25519 has no reason to retry, and rustls sends no
//!   cookie, the only retry this client accepts. So no real server completes a
//!   retry with this client. `hello_retry_request_completes` is a script: it
//!   writes the HelloRetryRequest itself; rustls (given ClientHello2 as if it
//!   were a first hello) contributes the ServerHello, EncryptedExtensions and
//!   Certificate; and the script redoes the CertificateVerify and the Finished
//!   over the transcript with the retry in it. Its key share, key schedule,
//!   signature and AEAD are ring's, through rustls's public provider API, not
//!   ours, so the keys are derived twice from one transcript by unrelated code.
//!   `real_rustls_retry_is_refused` is the real thing: a ClientHello with its
//!   key shares emptied out in the pipe makes rustls send a real
//!   HelloRetryRequest, which this client must refuse.
//! - *NewSessionTicket.* rustls sends none to this client (no
//!   psk_key_exchange_modes, RFC 8446 §4.2.9), so after a real rustls handshake
//!   the script seals tickets under the application keys rustls itself exports,
//!   with a ticket body from rustls's own ticketer.

// rustls's ring provider is C and assembly, which Miri cannot run.
#![cfg(not(miri))]

use std::io::Cursor;
use std::sync::Arc;

use clazel_crypto::client::{Client as Driver, Failure, Origin, Output, State};
use clazel_crypto::join::exec::{ChainVerifier, Root};
use clazel_crypto::provider::{ChaCha20Poly1305Factory, Sha256Suite, X25519};
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
use rustls::crypto::cipher::{
    AeadKey, InboundOpaqueMessage, Iv, MessageDecrypter, MessageEncrypter, OutboundChunks,
    OutboundPlainMessage,
};
use rustls::crypto::ring::{cipher_suite::TLS13_CHACHA20_POLY1305_SHA256, default_provider};
use rustls::crypto::tls13::{HkdfExpander, OkmBlock};
use rustls::crypto::{ActiveKeyExchange, CryptoProvider, SharedSecret, SupportedKxGroup};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{
    ConnectionTrafficSecrets, ContentType, NamedGroup, ProtocolVersion, ServerConfig,
    ServerConnection, SignatureScheme,
};

type TestResult = Result<(), String>;

// ---------------------------------------------------------------------------
// Fixtures (tests/fixtures/tls/SOURCE.md)
// ---------------------------------------------------------------------------

static ROOT: &[u8] = include_bytes!("fixtures/tls/root.der");
static ROOT_P384: &[u8] = include_bytes!("fixtures/tls/root-p384.der");
static INTERMEDIATE: &[u8] = include_bytes!("fixtures/tls/intermediate.der");
static LEAF_ECDSA: &[u8] = include_bytes!("fixtures/tls/leaf-ecdsa.der");
static KEY_ECDSA: &[u8] = include_bytes!("fixtures/tls/leaf-ecdsa.key.der");
static LEAF_P384: &[u8] = include_bytes!("fixtures/tls/leaf-p384.der");
static KEY_P384: &[u8] = include_bytes!("fixtures/tls/leaf-p384.key.der");
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
const ILLEGAL_PARAMETER: u8 = 47;
const UNKNOWN_CA: u8 = 48;
const DECODE_ERROR: u8 = 50;
const DECRYPT_ERROR: u8 = 51;
const PROTOCOL_VERSION: u8 = 70;
const INTERNAL_ERROR: u8 = 80;

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

/// A P-384 leaf: rustls can sign CertificateVerify only with
/// ecdsa_secp384r1_sha384 (RFC 8446 §4.2.3), so this needs our offer.
fn p384_chain() -> ServerCert {
    ServerCert {
        chain: vec![LEAF_P384],
        key: KEY_P384,
    }
}

fn server_config(
    cert: &ServerCert,
    tweak: impl FnOnce(&mut ServerConfig),
) -> Result<Arc<ServerConfig>, String> {
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
    let mut config = ServerConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .map_err(|e| e.to_string())?
        .with_no_client_auth()
        .with_single_cert(chain, key)
        .map_err(|e| e.to_string())?;
    tweak(&mut config);
    Ok(Arc::new(config))
}

struct Server {
    conn: ServerConnection,
}

impl Server {
    fn new(cert: &ServerCert) -> Result<Self, String> {
        Self::configured(cert, |_| {})
    }

    fn configured(
        cert: &ServerCert,
        tweak: impl FnOnce(&mut ServerConfig),
    ) -> Result<Self, String> {
        let conn = ServerConnection::new(server_config(cert, tweak)?).map_err(|e| e.to_string())?;
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
// The client: production's driver, its outputs as events
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq)]
enum Event {
    /// Octets the client sends to the server.
    Send(Vec<u8>),
    /// The handshake completed: the driver is `Open`.
    Ready,
    /// Application plaintext released.
    Deliver(Vec<u8>),
    /// Both directions closed.
    Closed,
    /// Fatal: the client's own failure, with its alert description.
    Fail(u8),
    /// A fatal alert the peer sent, before or after the handshake keys.
    PeerAlert(u8),
}

struct Client {
    driver: Driver<'static>,
    /// The state of the last output.
    state: State,
    /// The X25519 public key the ClientHello carries.
    public: Vec<u8>,
}

fn anchors() -> ChainVerifier<'static> {
    ChainVerifier::new(&[
        Root {
            der: ROOT,
            server_distrust_after: None,
        },
        Root {
            der: ROOT_P384,
            server_distrust_after: None,
        },
    ])
}

impl Client {
    /// Returns the client and its ClientHello record. `verifier` holds the
    /// trust store.
    fn start(verifier: ChainVerifier<'static>) -> Result<(Self, Vec<u8>), String> {
        // The order in which the driver draws its octets.
        let mut draws = [
            "client x25519 scalar",
            "client hello random",
            "client legacy_session_id",
        ]
        .into_iter();
        let (driver, out) = Driver::connect(
            Host::Dns(HOST.to_vec()),
            NOW,
            verifier,
            &mut |buf: &mut [u8]| {
                if let Some(label) = draws.next() {
                    for (octet, seed) in buf.iter_mut().zip(seeded(label)) {
                        *octet = seed;
                    }
                }
            },
        );
        let public = X25519.public_key(&seeded("client x25519 scalar"));
        let state = out.state;
        Ok((
            Client {
                driver,
                state,
                public,
            },
            out.send,
        ))
    }

    /// One output as events, in the order the driver produced them.
    fn events(&mut self, out: Output) -> Vec<Event> {
        let mut events = Vec::new();
        if !out.send.is_empty() {
            events.push(Event::Send(out.send));
        }
        if self.state == State::Handshaking && out.state == State::Open {
            events.push(Event::Ready);
        }
        if !out.deliver.is_empty() {
            events.push(Event::Deliver(out.deliver));
        }
        match out.state {
            State::Closed => events.push(Event::Closed),
            State::Failed(failure) if failure.origin == Origin::Peer => {
                events.push(Event::PeerAlert(failure.alert));
            }
            State::Failed(failure) => events.push(Event::Fail(failure.alert)),
            _ => {}
        }
        self.state = out.state;
        events
    }

    /// Feed octets from the server.
    fn receive(&mut self, bytes: &[u8]) -> Result<Vec<Event>, String> {
        let out = self.driver.receive(bytes);
        Ok(self.events(out))
    }

    fn send_application(&mut self, data: &[u8]) -> Result<Vec<u8>, String> {
        let out = self.driver.send(data).map_err(|e| format!("{e:?}"))?;
        Ok(out.send)
    }

    fn close_write(&mut self) -> Result<Vec<u8>, String> {
        Ok(self.driver.close().send)
    }

    fn failed(&self) -> bool {
        matches!(self.driver.state(), State::Failed(_))
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
    connect_to(Server::new(cert)?)
}

/// A full handshake against this server; the client is `Ready`.
fn connect_to(mut server: Server) -> Result<(Client, Server), String> {
    let (mut client, hello) = Client::start(anchors())?;
    let events = pump(&mut client, &mut server, hello)?;
    if !events.contains(&Event::Ready) {
        return Err(format!("no Ready; events: {events:?}"));
    }
    if server.conn.is_handshaking() {
        return Err("rustls still handshaking after the client's Finished".to_owned());
    }
    if client.driver.state() != State::Open {
        return Err("client is not Open".to_owned());
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

fn p384_chain_full_handshake_and_application_data() -> TestResult {
    application_round_trip(&p384_chain())
}

fn server_key_update_is_followed() -> TestResult {
    let (mut client, mut server) = connect(&ecdsa_chain())?;
    server
        .conn
        .refresh_traffic_keys()
        .map_err(|e| e.to_string())?;
    server.write_plaintext(b"after key update")?;
    let events = client.receive(&server.take()?)?;
    assert!(
        events.contains(&Event::Deliver(b"after key update".to_vec())),
        "{events:?}"
    );
    // Any KeyUpdate the driver answered with goes first, as on the wire.
    server.feed(&sends(&events))?;
    let reply = client.send_application(b"client after update")?;
    server.feed(&reply)?;
    assert_eq!(server.read_plaintext()?, b"client after update");
    Ok(())
}

// ---------------------------------------------------------------------------
// Fragmented and truncated flights from the real server
// ---------------------------------------------------------------------------

/// The plaintext in `events`, in order.
fn delivered(events: &[Event]) -> Vec<u8> {
    events
        .iter()
        .filter_map(|event| match event {
            Event::Deliver(bytes) => Some(bytes.as_slice()),
            _ => None,
        })
        .flatten()
        .copied()
        .collect()
}

/// A real rustls server that fragments everything it sends: 64 octets is its
/// record limit here, so every message of the flight spans records (RFC 8446
/// §5.1), and it does this itself.
fn fragmenting_server() -> Result<Server, String> {
    Server::configured(&ecdsa_chain(), |config| {
        config.max_fragment_size = Some(64);
    })
}

/// The client's answer to a whole flight is accepted by rustls, and data goes
/// both ways afterwards.
fn finish_and_exchange(client: &mut Client, server: &mut Server, answer: &[u8]) -> TestResult {
    server.feed(answer)?;
    if server.conn.is_handshaking() {
        return Err("rustls did not accept the client's Finished".to_owned());
    }
    server.write_plaintext(b"after a fragmented flight")?;
    let events = client.receive(&server.take()?)?;
    assert_eq!(delivered(&events), b"after a fragmented flight");
    let wire = client.send_application(b"client reply")?;
    server.feed(&wire)?;
    assert_eq!(server.read_plaintext()?, b"client reply");
    Ok(())
}

fn server_flight_fragmented_across_records_by_rustls() -> TestResult {
    let mut server = fragmenting_server()?;
    let (mut client, hello) = Client::start(anchors())?;
    server.feed(&hello)?;
    let flight = server.take()?;
    // More protected records than the flight has messages: rustls did split them.
    let protected = split_records(&flight)?
        .iter()
        .filter(|record| record.first() == Some(&23))
        .count();
    assert!(protected > 8, "rustls sent {protected} protected records");
    let events = client.receive(&flight)?;
    assert!(events.contains(&Event::Ready), "{events:?}");
    let answer = sends(&events);
    finish_and_exchange(&mut client, &mut server, &answer)
}

fn server_flight_delivered_one_octet_at_a_time() -> TestResult {
    for mut server in [Server::new(&ecdsa_chain())?, fragmenting_server()?] {
        let (mut client, hello) = Client::start(anchors())?;
        server.feed(&hello)?;
        let flight = server.take()?;
        let mut events = Vec::new();
        for octet in &flight {
            events.extend(client.receive(core::slice::from_ref(octet))?);
        }
        assert!(events.contains(&Event::Ready), "{events:?}");
        // Nothing but the client flight, which goes out once.
        assert_eq!(events.len(), 2, "{events:?}");
        let answer = sends(&events);
        finish_and_exchange(&mut client, &mut server, &answer)?;
    }
    Ok(())
}

/// RFC 8446 §6.1: a transport that ends before close_notify is a truncation.
/// It ends the connection, so our close_notify goes out first: one record,
/// in plaintext before the handshake keys (warning, close_notify), and
/// protected afterwards (an application_data record of 2 octets of alert,
/// 1 of content type and the 16-octet tag). No alert is sent.
fn truncated_is_refused(client: &mut Client) -> TestResult {
    let out = client.driver.receive_eof();
    let plaintext = [21u8, 3, 3, 0, 2, 1, 0];
    let protected = out.send.len() == 24 && out.send.get(..5) == Some(&[23u8, 3, 3, 0, 19][..]);
    assert!(out.send == plaintext || protected, "sent {:?}", out.send);
    assert_eq!(
        out.state,
        State::Failed(Failure {
            alert: INTERNAL_ERROR,
            origin: Origin::Truncated,
        })
    );
    Ok(())
}

/// Every place worth cutting a flight of these records: inside the first
/// header, after each record, and one octet either side of each record's end.
fn cut_points(flight: &[u8]) -> Result<Vec<usize>, String> {
    let mut cuts = vec![0, 3];
    let mut end = 0usize;
    for record in split_records(flight)? {
        end = add(end, record.len())?;
        cuts.push(need(end.checked_sub(1), "empty record")?);
        cuts.push(end);
    }
    // The last end is the whole flight, which is not a truncation of it.
    cuts.pop();
    Ok(cuts)
}

fn server_flight_truncated_at_every_record_boundary() -> TestResult {
    for fresh in [
        Server::new as fn(&ServerCert) -> Result<Server, String>,
        |_: &ServerCert| fragmenting_server(),
    ] {
        // Each connection's own cuts: an ECDSA signature's length varies, so
        // the flights differ in length.
        let mut index = 0usize;
        loop {
            let mut server = fresh(&ecdsa_chain())?;
            let (mut client, hello) = Client::start(anchors())?;
            server.feed(&hello)?;
            let flight = server.take()?;
            let cuts = cut_points(&flight)?;
            let Some(&cut) = cuts.get(index) else {
                assert!(index > 6, "only {index} cuts");
                break;
            };
            let events = client.receive(head(&flight, cut)?)?;
            assert!(
                events.is_empty(),
                "a cut at {cut} of {} gave {events:?}",
                flight.len()
            );
            truncated_is_refused(&mut client)?;
            index = add(index, 1)?;
        }
    }
    Ok(())
}

fn server_gone_after_its_flight_is_truncated() -> TestResult {
    // The flight is whole and the client Finished sent, then no close_notify.
    let (mut client, _server) = connect(&ecdsa_chain())?;
    truncated_is_refused(&mut client)
}

// ---------------------------------------------------------------------------
// The independent server side: ring, through rustls's public provider API.
// Nothing here calls libcrux or `clazel_tls::schedule`.
// ---------------------------------------------------------------------------

fn suite() -> Result<&'static rustls::Tls13CipherSuite, String> {
    need(
        TLS13_CHACHA20_POLY1305_SHA256.tls13(),
        "not a TLS 1.3 suite",
    )
}

fn ring_hash(data: &[u8]) -> Result<Vec<u8>, String> {
    Ok(suite()?.common.hash_provider.hash(data).as_ref().to_vec())
}

/// RFC 8446 §7.1 HKDF-Expand-Label, written from the RFC for this test.
fn expand_label(
    expander: &dyn HkdfExpander,
    label: &[u8],
    context: &[u8],
    length: u16,
) -> Result<Vec<u8>, String> {
    let mut out = vec![0u8; usize::from(length)];
    let full = u8::try_from(add(6, label.len())?).map_err(|e| e.to_string())?;
    let context_len = u8::try_from(context.len()).map_err(|e| e.to_string())?;
    expander
        .expand_slice(
            &[
                &length.to_be_bytes(),
                &[full],
                b"tls13 ",
                label,
                &[context_len],
                context,
            ],
            &mut out,
        )
        .map_err(|_| "HKDF output too long".to_owned())?;
    Ok(out)
}

fn expander_for(secret: &[u8]) -> Result<Box<dyn HkdfExpander>, String> {
    Ok(suite()?
        .hkdf_provider
        .expander_for_okm(&OkmBlock::new(secret)))
}

/// RFC 8446 §7.3: the key and IV of a traffic secret.
fn traffic_key(secret: &[u8]) -> Result<(AeadKey, Iv), String> {
    let expander = expander_for(secret)?;
    let key: [u8; 32] = expand_label(expander.as_ref(), b"key", &[], 32)?
        .try_into()
        .map_err(|_| "key length".to_owned())?;
    let iv: [u8; 12] = expand_label(expander.as_ref(), b"iv", &[], 12)?
        .try_into()
        .map_err(|_| "IV length".to_owned())?;
    Ok((AeadKey::from(key), Iv::from(iv)))
}

/// One direction under ring's ChaCha20-Poly1305, and its §5.3 sequence number.
struct RingSender {
    sealer: Box<dyn MessageEncrypter>,
    sequence: u64,
}

impl RingSender {
    fn new(key: AeadKey, iv: Iv, sequence: u64) -> Result<Self, String> {
        Ok(RingSender {
            sealer: suite()?.aead_alg.encrypter(key, iv),
            sequence,
        })
    }

    fn seal(&mut self, typ: ContentType, content: &[u8]) -> Result<Vec<u8>, String> {
        let message = OutboundPlainMessage {
            typ,
            version: ProtocolVersion::TLSv1_2,
            payload: OutboundChunks::Single(content),
        };
        let sealed = self
            .sealer
            .encrypt(message, self.sequence)
            .map_err(|e| e.to_string())?;
        self.sequence = need(self.sequence.checked_add(1), "sequence overflow")?;
        Ok(sealed.encode())
    }
}

/// The other direction.
struct RingReceiver {
    opener: Box<dyn MessageDecrypter>,
    sequence: u64,
}

impl RingReceiver {
    fn new(key: AeadKey, iv: Iv, sequence: u64) -> Result<Self, String> {
        Ok(RingReceiver {
            opener: suite()?.aead_alg.decrypter(key, iv),
            sequence,
        })
    }

    /// Open one whole record; its inner type and content.
    fn open(&mut self, record: &[u8]) -> Result<(ContentType, Vec<u8>), String> {
        let mut body = tail(record, 5)?.to_vec();
        let message = InboundOpaqueMessage::new(
            ContentType::ApplicationData,
            ProtocolVersion::TLSv1_2,
            &mut body,
        );
        let opened = self
            .opener
            .decrypt(message, self.sequence)
            .map_err(|e| format!("ring did not open the client's record: {e}"))?;
        let out = (opened.typ, opened.payload.to_vec());
        self.sequence = need(self.sequence.checked_add(1), "sequence overflow")?;
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// HelloRetryRequest
// ---------------------------------------------------------------------------

/// RFC 8446 §4.1.3: SHA-256 of "HelloRetryRequest", the retry's random.
const HRR_RANDOM: [u8; 32] = [
    0xCF, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11, 0xBE, 0x1D, 0x8C, 0x02, 0x1E, 0x65, 0xB8, 0x91,
    0xC2, 0xA2, 0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E, 0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C,
];

/// A handshake message's header on this body.
fn handshake_message(typ: u8, body: &[u8]) -> Result<Vec<u8>, String> {
    let len = u32::try_from(body.len()).map_err(|e| e.to_string())?;
    let mut out = vec![typ];
    out.extend_from_slice(need(len.to_be_bytes().get(1..), "length")?);
    out.extend_from_slice(body);
    Ok(out)
}

/// §4.1.2: the offset of `legacy_session_id`'s length in a ClientHello body.
const SESSION_ID_AT: usize = 34;

/// A ClientHello message's session id, and the offset of its extensions'
/// total length.
fn client_hello_layout(message: &[u8]) -> Result<(Vec<u8>, usize), String> {
    let body = tail(message, 4)?;
    let session_len = usize::from(byte(body, SESSION_ID_AT)?);
    let session_at = add(SESSION_ID_AT, 1)?;
    let session = head(tail(body, session_at)?, session_len)?.to_vec();
    let suites_at = add(session_at, session_len)?;
    let suites_len = be16(body, suites_at)?;
    let compression_at = add(add(suites_at, 2)?, suites_len)?;
    let compression_len = usize::from(byte(body, compression_at)?);
    let extensions_at = add(add(compression_at, 1)?, compression_len)?;
    Ok((session, extensions_at))
}

/// A ClientHello message with one extension cut out, and its lengths fixed.
fn client_hello_without(message: &[u8], extension: u16) -> Result<Vec<u8>, String> {
    client_hello_replacing(message, extension, None)
}

/// A ClientHello message with one extension cut out or its data replaced, and
/// its lengths fixed.
fn client_hello_replacing(
    message: &[u8],
    extension: u16,
    data: Option<&[u8]>,
) -> Result<Vec<u8>, String> {
    let (_, extensions_at) = client_hello_layout(message)?;
    let body = tail(message, 4)?;
    let mut rest = tail(body, add(extensions_at, 2)?)?;
    let mut kept = Vec::new();
    while !rest.is_empty() {
        let total = add(4, be16(rest, 2)?)?;
        if be16(rest, 0)? != usize::from(extension) {
            kept.extend_from_slice(head(rest, total)?);
        } else if let Some(data) = data {
            let data_len = u16::try_from(data.len()).map_err(|e| e.to_string())?;
            kept.extend_from_slice(&extension.to_be_bytes());
            kept.extend_from_slice(&data_len.to_be_bytes());
            kept.extend_from_slice(data);
        }
        rest = tail(rest, total)?;
    }
    let kept_len = u16::try_from(kept.len()).map_err(|e| e.to_string())?;
    let mut out = head(body, extensions_at)?.to_vec();
    out.extend_from_slice(&kept_len.to_be_bytes());
    out.extend_from_slice(&kept);
    handshake_message(1, &out)
}

/// §4.1.4: a HelloRetryRequest with a cookie, the one retry this client
/// accepts: its X25519 share is the only group it offers, so no other change
/// to the ClientHello could be asked for.
fn hello_retry_request(session: &[u8], cookie: &[u8]) -> Result<Vec<u8>, String> {
    let cookie_len = u16::try_from(cookie.len()).map_err(|e| e.to_string())?;
    let data_len = u16::try_from(add(cookie.len(), 2)?).map_err(|e| e.to_string())?;
    let mut extensions = vec![0, 43, 0, 2, 3, 4, 0, 44];
    extensions.extend_from_slice(&data_len.to_be_bytes());
    extensions.extend_from_slice(&cookie_len.to_be_bytes());
    extensions.extend_from_slice(cookie);
    let extensions_len = u16::try_from(extensions.len()).map_err(|e| e.to_string())?;
    let mut body = vec![3, 3];
    body.extend_from_slice(&HRR_RANDOM);
    body.push(u8::try_from(session.len()).map_err(|e| e.to_string())?);
    body.extend_from_slice(session);
    body.extend_from_slice(&[0x13, 0x03, 0]);
    body.extend_from_slice(&extensions_len.to_be_bytes());
    body.extend_from_slice(&extensions);
    handshake_message(2, &body)
}

const COOKIE: &[u8] = b"a cookie the client must echo";

/// A client that has answered a HelloRetryRequest: the client, ClientHello1,
/// the retry, and ClientHello2's record.
struct Retried {
    client: Client,
    hello1: Vec<u8>,
    retry: Vec<u8>,
    hello2_record: Vec<u8>,
}

fn retried_client() -> Result<Retried, String> {
    let (mut client, hello_record) = Client::start(anchors())?;
    let hello1 = tail(&hello_record, 5)?.to_vec();
    let (session, _) = client_hello_layout(&hello1)?;
    let retry = hello_retry_request(&session, COOKIE)?;
    let events = client.receive(&plain_record(22, &retry)?)?;
    let wire = sends(&events);
    let records = split_records(&wire)?;
    // Appendix D.4: the session id asks for compatibility mode, so the dummy
    // change_cipher_spec comes first, once.
    assert_eq!(records.len(), 2, "{wire:?}");
    assert_eq!(
        records.first().map(Vec::as_slice),
        Some(&[20u8, 3, 3, 0, 1, 1][..])
    );
    let hello2_record = need(records.get(1), "no ClientHello2")?.clone();
    // §4.1.2: ClientHello2 is ClientHello1 and the cookie, nothing else.
    assert_eq!(
        client_hello_without(tail(&hello2_record, 5)?, 44)?,
        hello1,
        "ClientHello2 changed more than the cookie"
    );
    let mut cookie = u16::try_from(COOKIE.len())
        .map_err(|e| e.to_string())?
        .to_be_bytes()
        .to_vec();
    cookie.extend_from_slice(COOKIE);
    assert!(
        tail(&hello2_record, 5)?
            .windows(cookie.len())
            .any(|window| window == cookie.as_slice()),
        "ClientHello2 does not echo the cookie"
    );
    Ok(Retried {
        client,
        hello1,
        retry,
        hello2_record,
    })
}

/// The handshake and application secrets of the script's transcript.
struct RingSecrets {
    client_handshake: Vec<u8>,
    server_handshake: Vec<u8>,
    client_application: Vec<u8>,
    server_application: Vec<u8>,
}

/// RFC 8446 §7.1's schedule, from ring's HKDF. `to_server_hello` and
/// `to_server_finished` are the transcripts of the two derivations.
fn ring_schedule(
    shared: &[u8],
    to_server_hello: &[u8],
    to_server_finished: &[u8],
) -> Result<RingSecrets, String> {
    let hkdf = suite()?.hkdf_provider;
    let empty = ring_hash(&[])?;
    let early = hkdf.extract_from_zero_ikm(None);
    let salt = expand_label(early.as_ref(), b"derived", &empty, 32)?;
    let handshake = hkdf.extract_from_secret(Some(&salt), shared);
    let hello_hash = ring_hash(to_server_hello)?;
    let client_handshake = expand_label(handshake.as_ref(), b"c hs traffic", &hello_hash, 32)?;
    let server_handshake = expand_label(handshake.as_ref(), b"s hs traffic", &hello_hash, 32)?;
    let salt = expand_label(handshake.as_ref(), b"derived", &empty, 32)?;
    let master = hkdf.extract_from_zero_ikm(Some(&salt));
    let finished_hash = ring_hash(to_server_finished)?;
    Ok(RingSecrets {
        client_handshake,
        server_handshake,
        client_application: expand_label(master.as_ref(), b"c ap traffic", &finished_hash, 32)?,
        server_application: expand_label(master.as_ref(), b"s ap traffic", &finished_hash, 32)?,
    })
}

/// §4.4.4: Finished for this transcript, with ring's HMAC.
fn ring_finished(base_key: &[u8], transcript: &[u8]) -> Result<Vec<u8>, String> {
    let expander = expander_for(base_key)?;
    let key = expand_label(expander.as_ref(), b"finished", &[], 32)?;
    let tag = suite()?
        .hkdf_provider
        .hmac_sign(&OkmBlock::new(&key), &ring_hash(transcript)?);
    handshake_message(20, tag.as_ref())
}

/// §4.4.3: the server's CertificateVerify for this transcript: ring's ECDSA
/// P-256 with the leaf's key, not anything rustls signed.
fn ring_certificate_verify(cert: &ServerCert, transcript: &[u8]) -> Result<Vec<u8>, String> {
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(cert.key.to_vec()));
    let signing =
        rustls::crypto::ring::sign::any_supported_type(&key).map_err(|e| e.to_string())?;
    let signer = need(
        signing.choose_scheme(&[SignatureScheme::ECDSA_NISTP256_SHA256]),
        "the leaf cannot sign ecdsa_secp256r1_sha256",
    )?;
    let mut content = vec![0x20u8; 64];
    content.extend_from_slice(b"TLS 1.3, server CertificateVerify\0");
    content.extend_from_slice(&ring_hash(transcript)?);
    let signature = signer.sign(&content).map_err(|e| e.to_string())?;
    let signature_len = u16::try_from(signature.len()).map_err(|e| e.to_string())?;
    let mut body = vec![0x04u8, 0x03];
    body.extend_from_slice(&signature_len.to_be_bytes());
    body.extend_from_slice(&signature);
    handshake_message(15, &body)
}

/// The server's half of a retried handshake, as far as the client's answer.
struct RetriedServer {
    secrets: RingSecrets,
    /// The whole transcript through the server Finished.
    transcript: Vec<u8>,
    events: Vec<Event>,
    client: Client,
}

/// Run the scripted server after a HelloRetryRequest. `prefix` is what the
/// transcript has before ClientHello2: §4.4.1 says the message_hash of
/// ClientHello1, then the retry.
fn scripted_retry(
    prefix: impl FnOnce(&Retried) -> Result<Vec<u8>, String>,
) -> Result<RetriedServer, String> {
    let cert = ecdsa_chain();
    let retried = retried_client()?;
    let mut transcript = prefix(&retried)?;
    let Retried {
        mut client,
        hello2_record,
        ..
    } = retried;
    // rustls takes ClientHello2 as a first hello: only its messages are used.
    let (flight, _) = script(&cert, &client, &hello2_record)?;
    let mut items = flight.items.iter();
    let server_hello_record = match items.next() {
        Some(Item::Plain(record)) => record.clone(),
        _ => return Err("the flight does not start with a ServerHello".to_owned()),
    };
    // ring's own X25519, in place of the fixed share rustls was given.
    let ring_x25519 = rustls::crypto::ring::kx_group::X25519
        .start()
        .map_err(|e| e.to_string())?;
    let ring_public = ring_x25519.pub_key().to_vec();
    let fixed_public = X25519.public_key(&server_scalar());
    let mut server_hello = tail(&server_hello_record, 5)?.to_vec();
    let at = need(
        server_hello
            .windows(fixed_public.len())
            .position(|window| window == fixed_public.as_slice()),
        "no key share in the ServerHello",
    )?;
    need(server_hello.get_mut(at..add(at, 32)?), "short key share")?.copy_from_slice(&ring_public);
    let shared = ring_x25519
        .complete(&client.public)
        .map_err(|e| e.to_string())?;
    transcript.extend_from_slice(tail(&hello2_record, 5)?);
    transcript.extend_from_slice(&server_hello);
    let to_server_hello = transcript.clone();

    // EncryptedExtensions and Certificate are rustls's, unchanged.
    let mut messages = Vec::new();
    for item in items {
        if let Item::Sealed(22, message) = item
            && matches!(message.first(), Some(8 | 11))
        {
            transcript.extend_from_slice(message);
            messages.push(message.clone());
        }
    }
    let certificate_verify = ring_certificate_verify(&cert, &transcript)?;
    transcript.extend_from_slice(&certificate_verify);
    messages.push(certificate_verify);
    let handshake_only = ring_schedule(shared.secret_bytes(), &to_server_hello, &transcript)?;
    let finished = ring_finished(&handshake_only.server_handshake, &transcript)?;
    transcript.extend_from_slice(&finished);
    messages.push(finished);
    let secrets = ring_schedule(shared.secret_bytes(), &to_server_hello, &transcript)?;

    let (key, iv) = traffic_key(&secrets.server_handshake)?;
    let mut sender = RingSender::new(key, iv, 0)?;
    let mut wire = plain_record(22, &server_hello)?;
    for message in &messages {
        wire.extend_from_slice(&sender.seal(ContentType::Handshake, message)?);
    }
    let events = client.receive(&wire)?;
    Ok(RetriedServer {
        secrets,
        transcript,
        events,
        client,
    })
}

/// §4.4.1: `message_hash` of ClientHello1, then the retry.
fn retry_transcript(retried: &Retried) -> Result<Vec<u8>, String> {
    let mut transcript = vec![254u8, 0, 0, 32];
    transcript.extend_from_slice(&ring_hash(&retried.hello1)?);
    transcript.extend_from_slice(&retried.retry);
    Ok(transcript)
}

fn hello_retry_request_completes() -> TestResult {
    let RetriedServer {
        secrets,
        mut transcript,
        events,
        mut client,
    } = scripted_retry(retry_transcript)?;
    assert!(events.contains(&Event::Ready), "{events:?}");
    let answer = sends(&events);
    // Appendix D.4: the change_cipher_spec went before ClientHello2, and no
    // second one comes now.
    let records = split_records(&answer)?;
    assert_eq!(records.len(), 1, "{answer:?}");
    let (key, iv) = traffic_key(&secrets.client_handshake)?;
    let (typ, finished) =
        RingReceiver::new(key, iv, 0)?.open(need(records.first(), "no record")?)?;
    assert_eq!(typ, ContentType::Handshake);
    assert_eq!(
        finished,
        ring_finished(&secrets.client_handshake, &transcript)?,
        "the client's Finished disagrees with ring's over the retried transcript"
    );
    transcript.extend_from_slice(&finished);

    // Application traffic under ring's secrets, both ways.
    let (key, iv) = traffic_key(&secrets.server_application)?;
    let mut to_client = RingSender::new(key, iv, 0)?;
    let events =
        client.receive(&to_client.seal(ContentType::ApplicationData, b"after a retry")?)?;
    assert_eq!(delivered(&events), b"after a retry");
    let (key, iv) = traffic_key(&secrets.client_application)?;
    let wire = client.send_application(b"client after a retry")?;
    let (typ, plain) = RingReceiver::new(key, iv, 0)?.open(&wire)?;
    assert_eq!(typ, ContentType::ApplicationData);
    assert_eq!(plain, b"client after a retry");
    Ok(())
}

fn retry_left_out_of_the_transcript_is_refused() -> TestResult {
    // The same script over ClientHello2 alone (§4.4.1 ignored): its keys differ
    // from the client's, so the first protected record does not open.
    let run = scripted_retry(|_| Ok(Vec::new()))?;
    assert_eq!(last_event(&run.events), Some(&Event::Fail(BAD_RECORD_MAC)));
    assert!(run.client.failed());
    Ok(())
}

fn second_hello_retry_request_is_refused() -> TestResult {
    // §4.1.4: "If a client receives a second HelloRetryRequest in the same
    // connection [...], it MUST abort the handshake with an
    // "unexpected_message" alert."
    let mut retried = retried_client()?;
    let events = retried.client.receive(&plain_record(22, &retried.retry)?)?;
    assert_eq!(last_event(&events), Some(&Event::Fail(UNEXPECTED_MESSAGE)));
    Ok(())
}

fn real_rustls_retry_is_refused() -> TestResult {
    // The real thing: with the shares emptied out of the ClientHello's key_share
    // (a test's tampering, in the pipe), rustls has to ask for one. It asks for
    // X25519, for which the client did offer a share, and §4.2.8 is plain: "the
    // client MUST abort the handshake with an "illegal_parameter" alert".
    let (mut client, hello_record) = Client::start(anchors())?;
    let tampered = client_hello_replacing(tail(&hello_record, 5)?, 51, Some(&[0, 0]))?;
    let mut server = Server::new(&ecdsa_chain())?;
    server.feed(&plain_record(22, &tampered)?)?;
    let retry = server.take()?;
    assert_eq!(
        retry.get(11..43),
        Some(&HRR_RANDOM[..]),
        "rustls did not send a HelloRetryRequest"
    );
    let events = client.receive(&retry)?;
    assert_eq!(last_event(&events), Some(&Event::Fail(ILLEGAL_PARAMETER)));
    Ok(())
}

// ---------------------------------------------------------------------------
// NewSessionTicket
// ---------------------------------------------------------------------------

/// §4.6.1: a NewSessionTicket around a ticket body from rustls's own ticketer,
/// with these extensions.
fn new_session_ticket(extensions: &[u8]) -> Result<Vec<u8>, String> {
    let ticketer = rustls::crypto::ring::Ticketer::new().map_err(|e| e.to_string())?;
    let ticket = need(
        ticketer.encrypt(b"a resumption state"),
        "the ticketer refused",
    )?;
    let ticket_len = u16::try_from(ticket.len()).map_err(|e| e.to_string())?;
    let extensions_len = u16::try_from(extensions.len()).map_err(|e| e.to_string())?;
    let mut body = Vec::new();
    body.extend_from_slice(&7200u32.to_be_bytes());
    body.extend_from_slice(&0x0102_0304u32.to_be_bytes());
    body.extend_from_slice(&[4, 1, 2, 3, 4]);
    body.extend_from_slice(&ticket_len.to_be_bytes());
    body.extend_from_slice(&ticket);
    body.extend_from_slice(&extensions_len.to_be_bytes());
    body.extend_from_slice(extensions);
    handshake_message(4, &body)
}

/// A real rustls handshake, then both directions under the application keys
/// and sequence numbers rustls exports.
fn after_real_handshake() -> Result<(Client, RingSender, RingReceiver), String> {
    let server = Server::configured(&ecdsa_chain(), |config| {
        config.enable_secret_extraction = true;
    })?;
    let (client, server) = connect_to(server)?;
    let secrets = server
        .conn
        .dangerous_extract_secrets()
        .map_err(|e| e.to_string())?;
    let (ConnectionTrafficSecrets::Chacha20Poly1305 { key, iv }, tx_sequence) =
        (secrets.tx.1, secrets.tx.0)
    else {
        return Err("rustls negotiated something else".to_owned());
    };
    let to_client = RingSender::new(key, iv, tx_sequence)?;
    let (ConnectionTrafficSecrets::Chacha20Poly1305 { key, iv }, rx_sequence) =
        (secrets.rx.1, secrets.rx.0)
    else {
        return Err("rustls negotiated something else".to_owned());
    };
    let from_client = RingReceiver::new(key, iv, rx_sequence)?;
    Ok((client, to_client, from_client))
}

fn new_session_ticket_is_read_and_ignored() -> TestResult {
    let (mut client, mut to_client, mut from_client) = after_real_handshake()?;
    // One ticket in a record.
    let ticket = new_session_ticket(&[])?;
    let events = client.receive(&to_client.seal(ContentType::Handshake, &ticket)?)?;
    assert_eq!(events, vec![]);
    // Two in one record, one with an early_data extension (§4.6.1), which this
    // client did not ask for and does nothing with.
    let mut two = new_session_ticket(&[0, 42, 0, 4, 0, 0, 4, 0])?;
    two.extend_from_slice(&ticket);
    let events = client.receive(&to_client.seal(ContentType::Handshake, &two)?)?;
    assert_eq!(events, vec![]);
    // One split across two records (§5.1).
    let (first, second) = ticket.split_at(10);
    let mut wire = to_client.seal(ContentType::Handshake, first)?;
    wire.extend_from_slice(&to_client.seal(ContentType::Handshake, second)?);
    let events = client.receive(&wire)?;
    assert_eq!(events, vec![]);
    // Nothing was delivered or sent, the sequence numbers still agree, and data
    // goes both ways.
    let events =
        client.receive(&to_client.seal(ContentType::ApplicationData, b"after tickets")?)?;
    assert_eq!(events, vec![Event::Deliver(b"after tickets".to_vec())]);
    let wire = client.send_application(b"client after tickets")?;
    let (typ, plain) = from_client.open(&wire)?;
    assert_eq!(typ, ContentType::ApplicationData);
    assert_eq!(plain, b"client after tickets");
    Ok(())
}

fn malformed_new_session_ticket_is_decode_error() -> TestResult {
    let (mut client, mut to_client, mut from_client) = after_real_handshake()?;
    // The body stops inside the ticket's length.
    let truncated = handshake_message(4, &[0, 0, 0, 1, 0, 0, 0, 1, 0, 0])?;
    let events = client.receive(&to_client.seal(ContentType::Handshake, &truncated)?)?;
    assert_eq!(last_event(&events), Some(&Event::Fail(DECODE_ERROR)));
    // The alert is sealed under the client application key, as ring can read.
    let wire = sends(&events);
    let (typ, alert) = from_client.open(&wire)?;
    assert_eq!(typ, ContentType::Alert);
    assert_eq!(alert, vec![2, DECODE_ERROR]);
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

    /// Set CertificateVerify's algorithm, the two octets after the
    /// handshake header (RFC 8446 §4.4.3).
    fn set_certificate_verify_scheme(&mut self, scheme: u16) -> TestResult {
        let at = self.find(15)?;
        match self.items.get_mut(at) {
            Some(Item::Sealed(_, message)) => match message.get_mut(4..6) {
                Some(octets) => {
                    octets.copy_from_slice(&scheme.to_be_bytes());
                    Ok(())
                }
                None => Err("short CertificateVerify".to_owned()),
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
    for cert in [ecdsa_chain(), rsa_chain(), p384_chain()] {
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
    let (events, client, _) = run_scripted(&ecdsa_chain(), |f| f.flip_last_byte(20))?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(DECRYPT_ERROR)),
        "{events:?}"
    );
    assert!(!events.contains(&Event::Ready));
    // Nothing is sent afterwards.
    assert!(client.failed());
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

/// RFC 8446 §4.4.3, "If the verification fails, the receiver MUST terminate
/// the handshake with a "decrypt_error" alert."
fn wrong_p384_certificate_verify_is_decrypt_error() -> TestResult {
    let (events, client, _) = run_scripted(&p384_chain(), |f| f.flip_last_byte(15))?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(DECRYPT_ERROR)),
        "{events:?}"
    );
    assert!(!events.contains(&Event::Ready));
    assert!(client.failed());
    Ok(())
}

/// RFC 8446 §4.2.3: a P-384 key's signature relabelled with the P-256
/// scheme, which is offered, does not verify.
fn p384_leaf_under_the_p256_scheme_is_decrypt_error() -> TestResult {
    let (events, _, _) = run_scripted(&p384_chain(), |f| f.set_certificate_verify_scheme(0x0403))?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(DECRYPT_ERROR)),
        "{events:?}"
    );
    Ok(())
}

/// RFC 8446 §4.4.3: the algorithm "MUST be one offered in the client's
/// "signature_algorithms" extension". ecdsa_secp521r1_sha512 is not.
fn unoffered_p521_scheme_is_illegal_parameter() -> TestResult {
    let (events, _, _) = run_scripted(&p384_chain(), |f| f.set_certificate_verify_scheme(0x0603))?;
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(ILLEGAL_PARAMETER)),
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
    assert!(client.failed());
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
    assert_eq!(
        last_event(&events),
        Some(&Event::Fail(RECORD_OVERFLOW)),
        "{events:?}"
    );
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

fn downgrade_sentinel_is_illegal_parameter() -> TestResult {
    // RFC 8446 §4.1.3: a ServerHello without supported_versions indicates
    // TLS 1.2 or below, and "TLS 1.3 clients receiving a ServerHello
    // indicating TLS 1.2 or below MUST check that the last 8 bytes are not
    // equal to either of these values" (DOWNGRD\x01 for TLS 1.2, DOWNGRD\x00
    // for TLS 1.1 or below); on a match the client MUST abort with
    // illegal_parameter. clazel-tls's hello/spec.rs (below_tls13) checks the
    // sentinel before reporting the missing version, so the same ServerHello
    // without it stays protocol_version (tls12_server_hello_is_refused).
    for sentinel in [b"DOWNGRD\x01", b"DOWNGRD\x00"] {
        let (events, _, _) = run_scripted(&ecdsa_chain(), |f| {
            let mut record = server_hello_without(f, 43)?;
            // header(5) + handshake header(4) + version(2) + random(32): the
            // random's last eight octets end at offset 43.
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
            Some(&Event::Fail(ILLEGAL_PARAMETER)),
            "{sentinel:02x?}: {events:?}"
        );
    }
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
        "p384_chain_full_handshake_and_application_data",
        p384_chain_full_handshake_and_application_data,
    ),
    (
        "server_key_update_is_followed",
        server_key_update_is_followed,
    ),
    (
        "scripted_server_control_completes_the_handshake",
        scripted_server_control_completes_the_handshake,
    ),
    (
        "compatibility_change_cipher_spec_where_rfc_8446_allows_it_is_dropped",
        compatibility_change_cipher_spec_where_rfc_8446_allows_it_is_dropped,
    ),
    (
        "server_flight_fragmented_across_records_by_rustls",
        server_flight_fragmented_across_records_by_rustls,
    ),
    (
        "server_flight_delivered_one_octet_at_a_time",
        server_flight_delivered_one_octet_at_a_time,
    ),
    (
        "hello_retry_request_completes",
        hello_retry_request_completes,
    ),
    (
        "new_session_ticket_is_read_and_ignored",
        new_session_ticket_is_read_and_ignored,
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
        "wrong_p384_certificate_verify_is_decrypt_error",
        wrong_p384_certificate_verify_is_decrypt_error,
    ),
    (
        "p384_leaf_under_the_p256_scheme_is_decrypt_error",
        p384_leaf_under_the_p256_scheme_is_decrypt_error,
    ),
    (
        "unoffered_p521_scheme_is_illegal_parameter",
        unoffered_p521_scheme_is_illegal_parameter,
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
        "downgrade_sentinel_is_illegal_parameter",
        downgrade_sentinel_is_illegal_parameter,
    ),
    (
        "change_cipher_spec_in_the_wrong_place_is_unexpected_message",
        change_cipher_spec_in_the_wrong_place_is_unexpected_message,
    ),
    (
        "server_flight_truncated_at_every_record_boundary",
        server_flight_truncated_at_every_record_boundary,
    ),
    (
        "server_gone_after_its_flight_is_truncated",
        server_gone_after_its_flight_is_truncated,
    ),
    (
        "retry_left_out_of_the_transcript_is_refused",
        retry_left_out_of_the_transcript_is_refused,
    ),
    (
        "second_hello_retry_request_is_refused",
        second_hello_retry_request_is_refused,
    ),
    ("real_rustls_retry_is_refused", real_rustls_retry_is_refused),
    (
        "malformed_new_session_ticket_is_decode_error",
        malformed_new_session_ticket_is_decode_error,
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
