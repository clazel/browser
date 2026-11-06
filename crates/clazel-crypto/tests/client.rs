//! The client driver (`clazel_crypto::client`, phase-3.md item 3.5f) against
//! a real TLS 1.3 server, over an in-memory byte pipe (no sockets).
//!
//! The server is rustls 0.23.46 with its ring provider, restricted to TLS
//! 1.3, `TLS_CHACHA20_POLY1305_SHA256` and X25519, as in
//! `tests/conformance_tls.rs`, with the certificates of `tests/fixtures/tls`
//! (see `SOURCE.md` there). The client's trust store is the test root.
//!
//! **Randomness is test-only**: the client's random octets come from a fixed
//! seed through SHA-256. Nothing here is a model for a production source.

// rustls's ring provider is C and assembly, which Miri cannot run.
#![cfg(not(miri))]

use std::io::Cursor;
use std::sync::Arc;

use clazel_crypto::client::{Client, Failure, NotOpen, Origin, Output, State};
use clazel_crypto::join::exec::{ChainVerifier, Root};
use clazel_crypto::provider::Sha256Suite;
use clazel_tls::host::exec::Host;
use clazel_tls::schedule::crypto::Crypto;
use rustls::crypto::ring::{cipher_suite::TLS13_CHACHA20_POLY1305_SHA256, default_provider};
use rustls::crypto::{CryptoProvider, ring::kx_group::X25519};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{ServerConfig, ServerConnection};

type TestResult = Result<(), String>;

static ROOT: &[u8] = include_bytes!("fixtures/tls/root.der");
static INTERMEDIATE: &[u8] = include_bytes!("fixtures/tls/intermediate.der");
static LEAF_ECDSA: &[u8] = include_bytes!("fixtures/tls/leaf-ecdsa.der");
static KEY_ECDSA: &[u8] = include_bytes!("fixtures/tls/leaf-ecdsa.key.der");
static LEAF_RSA: &[u8] = include_bytes!("fixtures/tls/leaf-rsa.der");
static KEY_RSA: &[u8] = include_bytes!("fixtures/tls/leaf-rsa.key.der");
static LEAF_OTHER: &[u8] = include_bytes!("fixtures/tls/leaf-other-name.der");
static KEY_OTHER: &[u8] = include_bytes!("fixtures/tls/leaf-other-name.key.der");

/// 2026-10-31T12:00:00Z, inside every valid fixture's validity.
const NOW: u64 = 1_793_448_000;

/// TEST-ONLY seed for the client's random octets.
const SEED: &[u8] = b"clazel client driver test seed v1: not random, never for production";

/// A deterministic source: SHA-256 of the seed and a counter, per call.
fn seeded() -> impl FnMut(&mut [u8]) {
    let mut calls = 0u32;
    move |out: &mut [u8]| {
        let mut input = SEED.to_vec();
        input.extend_from_slice(&calls.to_be_bytes());
        calls = calls.wrapping_add(1);
        let digest = Sha256Suite.hash(&input);
        for (byte, value) in out.iter_mut().zip(digest.iter().cycle()) {
            *byte = *value;
        }
    }
}

fn anchors() -> ChainVerifier<'static> {
    ChainVerifier::new(&[Root {
        der: ROOT,
        server_distrust_after: None,
    }])
}

fn connect(verifier: ChainVerifier<'static>) -> (Client<'static>, Output) {
    Client::connect(
        Host::Dns(b"test.example".to_vec()),
        NOW,
        verifier,
        &mut seeded(),
    )
}

fn server(leaf: &'static [u8], key: &'static [u8]) -> Result<ServerConnection, String> {
    let provider = CryptoProvider {
        cipher_suites: vec![TLS13_CHACHA20_POLY1305_SHA256],
        kx_groups: vec![X25519],
        ..default_provider()
    };
    let chain = vec![
        CertificateDer::from(leaf.to_vec()),
        CertificateDer::from(INTERMEDIATE.to_vec()),
    ];
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key.to_vec()));
    let config = ServerConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .map_err(|e| e.to_string())?
        .with_no_client_auth()
        .with_single_cert(chain, key)
        .map_err(|e| e.to_string())?;
    ServerConnection::new(Arc::new(config)).map_err(|e| e.to_string())
}

/// Give the server octets from the client; rustls's error, if any.
fn feed(server: &mut ServerConnection, bytes: &[u8]) -> TestResult {
    let mut cursor = Cursor::new(bytes);
    while usize::try_from(cursor.position()).map_err(|e| e.to_string())? < bytes.len() {
        let n = server.read_tls(&mut cursor).map_err(|e| e.to_string())?;
        if n == 0 {
            return Ok(());
        }
        server
            .process_new_packets()
            .map_err(|e| format!("rustls server: {e}"))?;
    }
    Ok(())
}

fn take(server: &mut ServerConnection) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    while server.wants_write() {
        server.write_tls(&mut out).map_err(|e| e.to_string())?;
    }
    Ok(out)
}

fn read_plaintext(server: &mut ServerConnection) -> Result<Vec<u8>, String> {
    use std::io::Read as _;
    let mut out = Vec::new();
    let mut buf = [0u8; 4096];
    loop {
        match server.reader().read(&mut buf) {
            Ok(0) => return Ok(out),
            Ok(n) => out.extend_from_slice(buf.get(..n).unwrap_or_default()),
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => return Ok(out),
            Err(e) => return Err(format!("server read: {e}")),
        }
    }
}

fn write_plaintext(server: &mut ServerConnection, data: &[u8]) -> TestResult {
    use std::io::Write as _;
    server.writer().write_all(data).map_err(|e| e.to_string())
}

/// Run the pipe until the client is no longer handshaking. Returns the
/// client's last output and the server's error, if it raised one.
fn handshake(
    client: &mut Client<'static>,
    server: &mut ServerConnection,
    hello: Vec<u8>,
) -> Result<(Output, Option<String>), String> {
    let mut to_server = hello;
    for _ in 0..16 {
        if let Err(e) = feed(server, &to_server) {
            return Ok((
                Output {
                    send: Vec::new(),
                    deliver: Vec::new(),
                    state: client.state(),
                },
                Some(e),
            ));
        }
        let out = client.receive(&take(server)?);
        if out.state != State::Handshaking {
            let error = feed(server, &out.send).err();
            return Ok((out, error));
        }
        to_server = out.send;
    }
    Err("the handshake did not finish".to_owned())
}

fn round_trip(leaf: &'static [u8], key: &'static [u8]) -> TestResult {
    let mut server = server(leaf, key)?;
    let (mut client, hello) = connect(anchors());
    assert_eq!(hello.state, State::Handshaking);
    let (out, error) = handshake(&mut client, &mut server, hello.send)?;
    assert_eq!(out.state, State::Open, "{out:?}");
    assert_eq!(error, None);
    assert!(!server.is_handshaking());
    // A request, then a response over one record (three records).
    let request = b"GET / HTTP/1.1\r\nhost: test.example\r\n\r\n";
    let out = client.send(request).map_err(|e| format!("{e:?}"))?;
    feed(&mut server, &out.send)?;
    assert_eq!(read_plaintext(&mut server)?, request);
    let response: Vec<u8> = (0..40_000u32).map(|i| i.to_le_bytes()[0]).collect();
    write_plaintext(&mut server, &response)?;
    let out = client.receive(&take(&mut server)?);
    assert_eq!(out.deliver, response);
    assert_eq!(out.state, State::Open);
    // The client sends more than one record too.
    let upload = vec![7u8; 20_000];
    let out = client.send(&upload).map_err(|e| format!("{e:?}"))?;
    feed(&mut server, &out.send)?;
    assert_eq!(read_plaintext(&mut server)?, upload);
    // Our close_notify, then the server's (RFC 8446 §6.1).
    let out = client.close();
    assert_eq!(out.state, State::Closing);
    feed(&mut server, &out.send)?;
    assert_eq!(client.send(b"x"), Err(NotOpen(State::Closing)));
    write_plaintext(&mut server, b"last words")?;
    server.send_close_notify();
    let out = client.receive(&take(&mut server)?);
    assert_eq!(out.deliver, b"last words");
    assert_eq!(out.state, State::Closed);
    assert!(out.send.is_empty());
    Ok(())
}

#[test]
fn ecdsa_chain_handshake_data_and_close() -> TestResult {
    round_trip(LEAF_ECDSA, KEY_ECDSA)
}

#[test]
fn rsa_chain_handshake_data_and_close() -> TestResult {
    round_trip(LEAF_RSA, KEY_RSA)
}

#[test]
fn the_servers_close_notify_is_answered() -> TestResult {
    let mut server = server(LEAF_ECDSA, KEY_ECDSA)?;
    let (mut client, hello) = connect(anchors());
    let (out, _) = handshake(&mut client, &mut server, hello.send)?;
    assert_eq!(out.state, State::Open);
    server.send_close_notify();
    let out = client.receive(&take(&mut server)?);
    assert_eq!(out.state, State::Closed);
    // Our close_notify went out; rustls reads it as the end of the stream.
    feed(&mut server, &out.send)?;
    assert_eq!(read_plaintext(&mut server)?, b"");
    Ok(())
}

/// RFC 8446 §6.1: closing during the server's flight sends close_notify,
/// sealed under the client handshake epoch. rustls decrypts it.
#[test]
fn closing_during_the_servers_flight_sends_close_notify() -> TestResult {
    let mut server = server(LEAF_ECDSA, KEY_ECDSA)?;
    let (mut client, hello) = connect(anchors());
    feed(&mut server, &hello.send)?;
    // The ServerHello alone: the client now holds the handshake keys.
    let flight = take(&mut server)?;
    let length = flight
        .get(3..5)
        .map(|n| n.iter().fold(0usize, |a, b| a * 256 + usize::from(*b)))
        .ok_or("no record header")?;
    let server_hello = flight.get(..length + 5).ok_or("no ServerHello record")?;
    let out = client.receive(server_hello);
    assert_eq!(out.state, State::Handshaking);
    let out = client.close();
    assert_eq!(out.state, State::Closed);
    assert_eq!(out.send.first(), Some(&23), "not a protected record");
    // rustls decrypts it and, mid-handshake, reports it as an error.
    let read = feed(&mut server, &out.send);
    assert!(
        read.as_ref().is_err_and(|e| e.contains("CloseNotify")),
        "{read:?}"
    );
    Ok(())
}

#[test]
fn a_certificate_for_another_name_sends_bad_certificate() -> TestResult {
    let mut server = server(LEAF_OTHER, KEY_OTHER)?;
    let (mut client, hello) = connect(anchors());
    let (out, error) = handshake(&mut client, &mut server, hello.send)?;
    assert_eq!(
        out.state,
        State::Failed(Failure {
            alert: 42,
            origin: Origin::Sent
        })
    );
    // rustls decrypted the alert under the client handshake key.
    let error = error.unwrap_or_default();
    assert!(error.contains("BadCertificate"), "{error}");
    Ok(())
}

#[test]
fn an_empty_trust_store_sends_unknown_ca() -> TestResult {
    let mut server = server(LEAF_ECDSA, KEY_ECDSA)?;
    let (mut client, hello) = connect(ChainVerifier::new(&[]));
    let (out, error) = handshake(&mut client, &mut server, hello.send)?;
    assert_eq!(
        out.state,
        State::Failed(Failure {
            alert: 48,
            origin: Origin::Sent
        })
    );
    let error = error.unwrap_or_default();
    assert!(error.contains("UnknownCA"), "{error}");
    // Final: later octets are ignored and nothing more is sent.
    let after = client.receive(b"\x17\x03\x03\x00\x01x");
    assert!(after.send.is_empty() && after.deliver.is_empty());
    Ok(())
}

/// RFC 8446 §5.2, §6.2: after the handshake, application data from the
/// server that fails to decrypt is bad_record_mac (20). `Connection` seals
/// that alert under the client application key at its next sequence number
/// (1, after the request) before it drops its keys, and rustls decrypts it.
#[test]
fn undecryptable_application_data_sends_bad_record_mac() -> TestResult {
    let mut server = server(LEAF_ECDSA, KEY_ECDSA)?;
    let (mut client, hello) = connect(anchors());
    let (out, _) = handshake(&mut client, &mut server, hello.send)?;
    assert_eq!(out.state, State::Open);
    let out = client
        .send(b"GET / HTTP/1.1\r\n\r\n")
        .map_err(|e| format!("{e:?}"))?;
    feed(&mut server, &out.send)?;
    write_plaintext(&mut server, b"a response the client cannot read")?;
    let mut record = take(&mut server)?;
    // Flip one octet of the AEAD tag: the record no longer authenticates.
    if let Some(last) = record.last_mut() {
        *last ^= 1;
    }
    let out = client.receive(&record);
    assert_eq!(
        out.state,
        State::Failed(Failure {
            alert: 20,
            origin: Origin::Sent
        })
    );
    assert!(out.deliver.is_empty());
    // One protected record: application_data outer type, 0x0303, and the
    // two alert octets, the inner type and the 16-octet tag.
    assert_eq!(out.send.len(), 5 + 2 + 1 + 16, "{:?}", out.send);
    assert_eq!(out.send.get(..5), Some(&[23u8, 3, 3, 0, 19][..]));
    let error = feed(&mut server, &out.send).err().unwrap_or_default();
    assert!(error.contains("BadRecordMac"), "{error}");
    // Final: nothing more is read or sent.
    let after = client.receive(&take(&mut server)?);
    assert!(after.send.is_empty() && after.deliver.is_empty());
    Ok(())
}

/// RFC 8446 §6, §6.2: a fatal alert from the server after the handshake ends
/// the connection and is not answered.
#[test]
fn a_server_alert_after_the_handshake_is_not_answered() -> TestResult {
    let mut server = server(LEAF_ECDSA, KEY_ECDSA)?;
    let (mut client, hello) = connect(anchors());
    let (out, _) = handshake(&mut client, &mut server, hello.send)?;
    assert_eq!(out.state, State::Open);
    // A tampered client record makes rustls send bad_record_mac.
    let mut record = client.send(b"x").map_err(|e| format!("{e:?}"))?.send;
    if let Some(last) = record.last_mut() {
        *last ^= 1;
    }
    let error = feed(&mut server, &record).err().unwrap_or_default();
    assert!(error.contains("ecrypt"), "{error}");
    let alert = take(&mut server)?;
    assert!(!alert.is_empty());
    let out = client.receive(&alert);
    assert_eq!(
        out.state,
        State::Failed(Failure {
            alert: 20,
            origin: Origin::Peer
        })
    );
    assert!(out.send.is_empty());
    Ok(())
}

#[test]
fn the_end_of_stream_without_close_notify_is_truncation() -> TestResult {
    let mut server = server(LEAF_ECDSA, KEY_ECDSA)?;
    let (mut client, hello) = connect(anchors());
    let (out, _) = handshake(&mut client, &mut server, hello.send)?;
    assert_eq!(out.state, State::Open);
    let out = client.receive_eof();
    assert_eq!(
        out.state,
        State::Failed(Failure {
            alert: 80,
            origin: Origin::Truncated
        })
    );
    assert!(out.send.is_empty());
    Ok(())
}
