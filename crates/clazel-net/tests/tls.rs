//! `TlsConnection` against an in-process rustls 0.23.46 server on a real
//! loopback TCP socket (phase-3.md items 3.5f and 3.8). The server is
//! restricted to TLS 1.3, `TLS_CHACHA20_POLY1305_SHA256` and X25519 over its
//! ring provider and uses the certificates of
//! `clazel-crypto/tests/fixtures/tls` (see `SOURCE.md` there); the client's
//! trust store is the test root. Hostile servers are plain `TcpListener`s.
//!
//! **Randomness**: most tests use a fixed seed through SHA-256
//! (`open_with_random`), so a handshake is reproducible; that seed is never a
//! model for production. The `*_with_os_randomness` tests and
//! `os_randomness_differs_between_connections` use the production path,
//! `TlsConnection::open`, whose octets come from `clazel_sys::fill_random`.

// rustls's ring provider is C and assembly, and these tests open sockets:
// Miri can run neither.
#![cfg(not(miri))]

use std::io::{self, Read, Write};
use std::net::{IpAddr, Ipv4Addr, TcpListener, TcpStream};
use std::sync::Arc;
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use clazel_cookie::storage::exec::CookieRecord;
use clazel_crypto::client::{Failure, Origin};
use clazel_crypto::join::exec::{ChainVerifier, Root};
use clazel_crypto::provider::Sha256Suite;
use clazel_net::{FetchError, NetError, Stage, Timeouts, TlsConnection, fetch_jar_verified};
use clazel_tls::host::exec::Host;
use clazel_tls::schedule::crypto::Crypto;
use rustls::crypto::ring::{cipher_suite::TLS13_CHACHA20_POLY1305_SHA256, default_provider};
use rustls::crypto::{CryptoProvider, ring::kx_group::X25519};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{ServerConfig, ServerConnection, StreamOwned};

type T = Result<(), String>;

static ROOT: &[u8] = include_bytes!("../../clazel-crypto/tests/fixtures/tls/root.der");
static INTERMEDIATE: &[u8] =
    include_bytes!("../../clazel-crypto/tests/fixtures/tls/intermediate.der");
static LEAF_ECDSA: &[u8] = include_bytes!("../../clazel-crypto/tests/fixtures/tls/leaf-ecdsa.der");
static KEY_ECDSA: &[u8] =
    include_bytes!("../../clazel-crypto/tests/fixtures/tls/leaf-ecdsa.key.der");
static LEAF_RSA: &[u8] = include_bytes!("../../clazel-crypto/tests/fixtures/tls/leaf-rsa.der");
static KEY_RSA: &[u8] = include_bytes!("../../clazel-crypto/tests/fixtures/tls/leaf-rsa.key.der");
static LEAF_OTHER: &[u8] =
    include_bytes!("../../clazel-crypto/tests/fixtures/tls/leaf-other-name.der");
static KEY_OTHER: &[u8] =
    include_bytes!("../../clazel-crypto/tests/fixtures/tls/leaf-other-name.key.der");

/// 2026-10-31T12:00:00Z, inside every valid fixture's validity.
const NOW: u64 = 1_793_448_000;
const LOCAL: [IpAddr; 1] = [IpAddr::V4(Ipv4Addr::LOCALHOST)];
const REQUEST: &[u8] = b"GET / HTTP/1.1\r\nhost: test.example\r\n\r\n";

/// TEST-ONLY seed for the client's random octets.
const SEED: &[u8] = b"clazel-net tls test seed v1: not random, never for production";

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

fn timeouts(idle: Duration) -> Timeouts {
    Timeouts {
        connect: Duration::from_secs(2),
        idle,
    }
}

fn verifier() -> ChainVerifier<'static> {
    ChainVerifier::new(&[Root {
        der: ROOT,
        server_distrust_after: None,
    }])
}

fn open(port: u16, idle: Duration) -> Result<TlsConnection<'static>, NetError> {
    TlsConnection::open_with_random(
        &LOCAL,
        port,
        timeouts(idle),
        Host::Dns(b"test.example".to_vec()),
        NOW,
        verifier(),
        &mut seeded(),
    )
}

/// The production path: the client's random octets from the OS
/// (`clazel_sys::fill_random`).
fn open_os(port: u16, idle: Duration) -> Result<TlsConnection<'static>, NetError> {
    TlsConnection::open(
        &LOCAL,
        port,
        timeouts(idle),
        Host::Dns(b"test.example".to_vec()),
        NOW,
        verifier(),
    )
}

type Opener = fn(u16, Duration) -> Result<TlsConnection<'static>, NetError>;

/// A server that accepts one connection and runs `f` on it.
fn server<R: Send + 'static>(
    f: impl FnOnce(TcpStream) -> Result<R, String> + Send + 'static,
) -> Result<(u16, JoinHandle<Result<R, String>>), String> {
    let listener = TcpListener::bind("127.0.0.1:0").map_err(|e| e.to_string())?;
    let port = listener.local_addr().map_err(|e| e.to_string())?.port();
    let handle = thread::spawn(move || {
        let (socket, _) = listener.accept().map_err(|e| e.to_string())?;
        socket
            .set_read_timeout(Some(Duration::from_secs(5)))
            .map_err(|e| e.to_string())?;
        f(socket)
    });
    Ok((port, handle))
}

fn join<R>(handle: JoinHandle<Result<R, String>>) -> Result<R, String> {
    handle
        .join()
        .map_err(|_| "server thread panicked".to_owned())?
}

type Tls = StreamOwned<ServerConnection, TcpStream>;

fn rustls(socket: TcpStream, leaf: &'static [u8], key: &'static [u8]) -> Result<Tls, String> {
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
    let conn = ServerConnection::new(Arc::new(config)).map_err(|e| e.to_string())?;
    Ok(StreamOwned::new(conn, socket))
}

/// Read plaintext until `end` ends what was read, or the stream ends.
fn read_until(tls: &mut Tls, end: &[u8]) -> Result<Vec<u8>, String> {
    let mut got = Vec::new();
    let mut buf = [0u8; 4096];
    while !got.ends_with(end) {
        let n = tls.read(&mut buf).map_err(|e| e.to_string())?;
        if n == 0 {
            break;
        }
        got.extend_from_slice(buf.get(..n).unwrap_or_default());
    }
    Ok(got)
}

/// Everything until `None`.
fn read_to_close(conn: &mut TlsConnection<'_>) -> Result<Vec<u8>, NetError> {
    let mut got = Vec::new();
    let mut buf = vec![0u8; 8192];
    while let Some(n) = conn.read(&mut buf)? {
        got.extend_from_slice(buf.get(..n).unwrap_or_default());
    }
    Ok(got)
}

/// Read one plaintext record (the ClientHello) from a raw socket.
fn read_record(socket: &mut TcpStream) -> Result<Vec<u8>, String> {
    let mut header = [0u8; 5];
    socket.read_exact(&mut header).map_err(|e| e.to_string())?;
    let [_, _, _, high, low] = header;
    let mut body = vec![0u8; usize::from(u16::from_be_bytes([high, low]))];
    socket.read_exact(&mut body).map_err(|e| e.to_string())?;
    let mut record = header.to_vec();
    record.extend_from_slice(&body);
    Ok(record)
}

/// A handshake, a request, a response; the client closes first, then the
/// server answers with its own close_notify. `open` is [`open`] (seeded) or
/// [`open_os`].
fn request_response(leaf: &'static [u8], key: &'static [u8], open: Opener) -> T {
    let (port, handle) = server(move |socket| {
        let mut tls = rustls(socket, leaf, key)?;
        let request = read_until(&mut tls, b"\r\n\r\n")?;
        tls.write_all(b"HTTP/1.1 200 OK\r\ncontent-length: 2\r\n\r\nok")
            .map_err(|e| e.to_string())?;
        tls.flush().map_err(|e| e.to_string())?;
        // Our close_notify reads as the end of the stream.
        let rest = read_until(&mut tls, b"never")?;
        // The client does not wait for this one, and may have closed the
        // socket already, so a failed write is not an error.
        tls.conn.send_close_notify();
        let _ = tls.flush();
        Ok((request, rest))
    })?;
    let mut conn = open(port, Duration::from_secs(5)).map_err(|e| e.to_string())?;
    conn.send(REQUEST).map_err(|e| e.to_string())?;
    let mut response = Vec::new();
    let mut buf = [0u8; 64];
    while !response.ends_with(b"ok") {
        match conn.read(&mut buf).map_err(|e| e.to_string())? {
            Some(n) => response.extend_from_slice(buf.get(..n).unwrap_or_default()),
            None => break,
        }
    }
    assert_eq!(response, b"HTTP/1.1 200 OK\r\ncontent-length: 2\r\n\r\nok");
    conn.close().map_err(|e| e.to_string())?;
    let (request, rest) = join(handle)?;
    assert_eq!(request, REQUEST);
    assert_eq!(rest, b"");
    Ok(())
}

#[test]
fn ecdsa_handshake_request_response_close() -> T {
    request_response(LEAF_ECDSA, KEY_ECDSA, open)
}

#[test]
fn rsa_handshake_request_response_close() -> T {
    request_response(LEAF_RSA, KEY_RSA, open)
}

#[test]
fn a_response_over_many_records_until_the_servers_close_notify() -> T {
    let body: Vec<u8> = (0..100_000u32).map(|i| i.to_le_bytes()[0]).collect();
    let sent = body.clone();
    let (port, handle) = server(move |socket| {
        let mut tls = rustls(socket, LEAF_ECDSA, KEY_ECDSA)?;
        read_until(&mut tls, b"\r\n\r\n")?;
        tls.write_all(&sent).map_err(|e| e.to_string())?;
        tls.conn.send_close_notify();
        tls.flush().map_err(|e| e.to_string())?;
        // The client answers with its close_notify.
        read_until(&mut tls, b"never")
    })?;
    let mut conn = open(port, Duration::from_secs(5)).map_err(|e| e.to_string())?;
    conn.send(REQUEST).map_err(|e| e.to_string())?;
    let got = read_to_close(&mut conn).map_err(|e| e.to_string())?;
    assert_eq!(got.len(), body.len());
    assert!(got == body);
    // Closed: reading again is still the end, sending is refused.
    assert_eq!(conn.read(&mut [0u8; 8]), Ok(None));
    assert_eq!(
        conn.send(b"x"),
        Err(NetError::Io(io::ErrorKind::NotConnected))
    );
    conn.close().map_err(|e| e.to_string())?;
    assert_eq!(join(handle)?, b"");
    Ok(())
}

#[test]
fn a_server_that_closes_during_the_handshake() -> T {
    let (port, handle) = server(|mut socket| {
        read_record(&mut socket)?;
        Ok(())
    })?;
    let result = open(port, Duration::from_secs(5));
    join(handle)?;
    assert_eq!(
        result.err(),
        Some(NetError::Tls(Failure {
            alert: 80,
            origin: Origin::Truncated
        }))
    );
    Ok(())
}

#[test]
fn a_server_that_stalls_hits_the_handshake_timeout() -> T {
    let (port, handle) = server(|mut socket| {
        read_record(&mut socket)?;
        thread::sleep(Duration::from_millis(800));
        Ok(())
    })?;
    let start = Instant::now();
    let result = open(port, Duration::from_millis(200));
    assert!(start.elapsed() < Duration::from_millis(700));
    assert_eq!(result.err(), Some(NetError::Timeout(Stage::Handshake)));
    join(handle)?;
    Ok(())
}

#[test]
fn a_certificate_for_another_name_is_bad_certificate() -> T {
    let (port, handle) = server(|socket| {
        let mut tls = rustls(socket, LEAF_OTHER, KEY_OTHER)?;
        // The handshake fails on the server with the client's alert.
        Ok(read_until(&mut tls, b"\r\n\r\n").err())
    })?;
    let result = open(port, Duration::from_secs(5));
    let failure = Failure {
        alert: 42,
        origin: Origin::Sent,
    };
    assert_eq!(result.err(), Some(NetError::Tls(failure)));
    assert_eq!(
        NetError::Tls(failure).to_string(),
        "tls: bad_certificate (42), sent to the server"
    );
    let server_error = join(handle)?.unwrap_or_default();
    assert!(server_error.contains("BadCertificate"), "{server_error}");
    Ok(())
}

/// RFC 8446 §5.2, §6.2: after the handshake, a response record that fails
/// to decrypt is bad_record_mac (20): the client seals that alert under its
/// application key, and rustls decrypts and reports it.
#[test]
fn an_undecryptable_response_sends_bad_record_mac() -> T {
    let (port, handle) = server(|socket| {
        let mut tls = rustls(socket, LEAF_ECDSA, KEY_ECDSA)?;
        read_until(&mut tls, b"\r\n\r\n")?;
        tls.conn
            .writer()
            .write_all(b"HTTP/1.1 200 OK\r\n\r\n")
            .map_err(|e| e.to_string())?;
        let mut records = Vec::new();
        while tls.conn.wants_write() {
            tls.conn
                .write_tls(&mut records)
                .map_err(|e| e.to_string())?;
        }
        // Flip one octet of the last record's AEAD tag.
        if let Some(last) = records.last_mut() {
            *last ^= 1;
        }
        tls.sock.write_all(&records).map_err(|e| e.to_string())?;
        // What the client sends back is its alert.
        loop {
            match tls.conn.read_tls(&mut tls.sock) {
                Ok(0) => return Ok("closed without an alert".to_owned()),
                Ok(_) => {
                    if let Err(e) = tls.conn.process_new_packets() {
                        return Ok(e.to_string());
                    }
                }
                Err(e) => return Ok(e.to_string()),
            }
        }
    })?;
    let mut conn = open(port, Duration::from_secs(5)).map_err(|e| e.to_string())?;
    conn.send(REQUEST).map_err(|e| e.to_string())?;
    let failure = Failure {
        alert: 20,
        origin: Origin::Sent,
    };
    assert_eq!(conn.read(&mut [0u8; 64]), Err(NetError::Tls(failure)));
    assert_eq!(
        NetError::Tls(failure).to_string(),
        "tls: bad_record_mac (20), sent to the server"
    );
    let server_error = join(handle)?;
    assert!(server_error.contains("BadRecordMac"), "{server_error}");
    Ok(())
}

#[test]
fn bytes_that_are_not_tls() -> T {
    let (port, handle) = server(|mut socket| {
        read_record(&mut socket)?;
        socket
            .write_all(b"HTTP/1.1 400 Bad Request\r\ncontent-length: 0\r\n\r\n")
            .map_err(|e| e.to_string())?;
        // What the client sends back: its alert, then the close.
        let mut back = Vec::new();
        socket.read_to_end(&mut back).map_err(|e| e.to_string())?;
        Ok(back)
    })?;
    let result = open(port, Duration::from_secs(5));
    let back = join(handle)?;
    match result.err() {
        Some(NetError::Tls(Failure {
            alert,
            origin: Origin::Sent,
        })) => assert_eq!(back, [21, 3, 3, 0, 2, 2, alert]),
        other => return Err(format!("{other:?}")),
    }
    Ok(())
}

#[test]
fn ecdsa_handshake_with_os_randomness() -> T {
    request_response(LEAF_ECDSA, KEY_ECDSA, open_os)
}

#[test]
fn rsa_handshake_with_os_randomness() -> T {
    request_response(LEAF_RSA, KEY_RSA, open_os)
}

/// The ClientHello's random (RFC 8446 §4.1.2) and legacy_session_id: after
/// the record header (5), the handshake header (4) and legacy_version (2),
/// 32 octets of random, then the session id's length (32) and its octets.
fn hello_randoms(record: &[u8]) -> Result<(Vec<u8>, Vec<u8>), String> {
    let random = record.get(11..43).ok_or("short ClientHello")?;
    let session_id = record.get(44..76).ok_or("short ClientHello")?;
    assert_eq!(record.get(43), Some(&32));
    Ok((random.to_vec(), session_id.to_vec()))
}

/// Open a connection with `open` and return the ClientHello it sent; the
/// server then closes, so the handshake ends in truncation.
fn client_hello(open: Opener) -> Result<Vec<u8>, String> {
    let (port, handle) = server(|mut socket| read_record(&mut socket))?;
    let result = open(port, Duration::from_secs(5));
    let hello = join(handle)?;
    match result.err() {
        Some(NetError::Tls(Failure {
            origin: Origin::Truncated,
            ..
        })) => Ok(hello),
        other => Err(format!("{other:?}")),
    }
}

/// With the OS source, two connections draw different octets; with the
/// test seed they are the same. The X25519 scalar is drawn the same way
/// but never leaves the client.
#[test]
fn os_randomness_differs_between_connections() -> T {
    let (random_a, session_a) = hello_randoms(&client_hello(open_os)?)?;
    let (random_b, session_b) = hello_randoms(&client_hello(open_os)?)?;
    assert_ne!(random_a, random_b);
    assert_ne!(session_a, session_b);
    assert_ne!(random_a, session_a);
    let seeded_a = client_hello(open)?;
    let seeded_b = client_hello(open)?;
    assert_eq!(seeded_a, seeded_b);
    Ok(())
}

// ---------------------------------------------------------------------
// `fetch` over TLS: an `https:` URL through `clazel-fetch`'s transducer,
// which asks for `Connect { tls: true }`, and this crate's
// `TlsConnection`, with OS randomness (the production path).
// ---------------------------------------------------------------------

/// [`NOW`] in seconds since 1601, as `fetch_jar` takes the time.
const NOW_1601: u64 = NOW + 11_644_473_600;

/// The resolver of the fetch tests: every name is 127.0.0.1.
fn local(_: &[u8]) -> Result<Vec<IpAddr>, NetError> {
    Ok(LOCAL.to_vec())
}

/// The request heads an [`https_server`] read, when it is done.
type Heads = JoinHandle<Result<Vec<Vec<u8>>, String>>;

/// A fetch's status and body, and the jar after it.
type Fetched = (Result<(u16, Vec<u8>), FetchError>, Vec<CookieRecord>);

/// A TLS server that accepts `n` connections in turn, each with the
/// certificate `leaf`, reads one request head, answers with what `reply`
/// gives for it and sends its close_notify. It reports each request head.
fn https_server(
    n: usize,
    leaf: &'static [u8],
    key: &'static [u8],
    reply: fn(&[u8]) -> &'static [u8],
) -> Result<(u16, Heads), String> {
    let listener = TcpListener::bind("127.0.0.1:0").map_err(|e| e.to_string())?;
    let port = listener.local_addr().map_err(|e| e.to_string())?.port();
    let handle = thread::spawn(move || {
        let mut heads = Vec::new();
        for _ in 0..n {
            let (socket, _) = listener.accept().map_err(|e| e.to_string())?;
            socket
                .set_read_timeout(Some(Duration::from_secs(5)))
                .map_err(|e| e.to_string())?;
            let mut tls = rustls(socket, leaf, key)?;
            let head = read_until(&mut tls, b"\r\n\r\n")?;
            tls.write_all(reply(&head)).map_err(|e| e.to_string())?;
            tls.conn.send_close_notify();
            // The client may have closed already once the response was
            // complete.
            let _ = tls.flush();
            heads.push(head);
        }
        Ok(heads)
    });
    Ok((port, handle))
}

fn fetch_https(url: &str) -> Fetched {
    let (r, jar) = fetch_jar_verified(
        url,
        Vec::new(),
        NOW_1601,
        timeouts(Duration::from_secs(5)),
        local,
        verifier,
    );
    (r.map(|r| (r.status_line.status, r.body)), jar)
}

/// RFC 9110 §4.2.2: an `https:` URL is fetched over TLS, with the same
/// request an `http:` URL gets, and the response read through the
/// transducer.
#[test]
fn an_https_fetch_over_tls() -> T {
    let (port, handle) = https_server(1, LEAF_ECDSA, KEY_ECDSA, |_| {
        b"HTTP/1.1 200 OK\r\ncontent-length: 2\r\n\r\nok"
    })?;
    let (r, _) = fetch_https(&format!("https://test.example:{port}/a?b"));
    assert_eq!(r, Ok((200, b"ok".to_vec())));
    let heads = join(handle)?;
    let expected = format!(
        "GET /a?b HTTP/1.1\r\nHost: test.example:{port}\r\nConnection: close\r\nAccept: */*\r\nUser-Agent: clazel\r\n\r\n"
    );
    assert_eq!(heads, [expected.into_bytes()]);
    Ok(())
}

/// A certificate for another name fails the fetch with the TLS alert, and
/// no request is sent.
#[test]
fn an_https_fetch_to_a_server_with_another_name_fails() -> T {
    let (port, handle) = server(|socket| {
        let mut tls = rustls(socket, LEAF_OTHER, KEY_OTHER)?;
        Ok(read_until(&mut tls, b"\r\n\r\n").err())
    })?;
    let (r, _) = fetch_https(&format!("https://test.example:{port}/"));
    let failure = Failure {
        alert: 42,
        origin: Origin::Sent,
    };
    assert_eq!(r, Err(FetchError::Net(NetError::Tls(failure))));
    assert!(join(handle)?.is_some());
    Ok(())
}

/// A response delimited by the connection closing (RFC 9112 §6.3 step 8)
/// whose TCP stream ends without the server's close_notify is a
/// truncation, so the fetch fails rather than taking what arrived as the
/// whole body.
#[test]
fn an_https_body_cut_off_without_close_notify_fails() -> T {
    let (port, handle) = server(|socket| {
        let mut tls = rustls(socket, LEAF_ECDSA, KEY_ECDSA)?;
        read_until(&mut tls, b"\r\n\r\n")?;
        tls.write_all(b"HTTP/1.1 200 OK\r\n\r\nthe whole body?")
            .map_err(|e| e.to_string())?;
        tls.flush().map_err(|e| e.to_string())?;
        // Close the socket without a close_notify.
        tls.sock
            .shutdown(std::net::Shutdown::Both)
            .map_err(|e| e.to_string())
    })?;
    let (r, _) = fetch_https(&format!("https://test.example:{port}/"));
    assert!(
        matches!(
            r,
            Err(FetchError::Net(NetError::Tls(Failure {
                origin: Origin::Truncated,
                ..
            })))
        ),
        "{r:?}"
    );
    join(handle)?;
    Ok(())
}

/// RFC 6265bis §5.7 and §5.8.3 over TLS: a `Secure` cookie set by an
/// `https:` response is stored and sent on the `https:` redirect.
#[test]
fn a_secure_cookie_is_stored_and_sent_over_https() -> T {
    let (port, handle) = https_server(2, LEAF_ECDSA, KEY_ECDSA, |head| {
        if head.starts_with(b"GET /set ") {
            b"HTTP/1.1 302 Found\r\nSet-Cookie: s=1; Secure\r\nLocation: /echo\r\nContent-Length: 0\r\n\r\n"
        } else {
            b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
        }
    })?;
    let (r, jar) = fetch_https(&format!("https://test.example:{port}/set"));
    assert_eq!(r, Ok((200, Vec::new())));
    assert_eq!(jar.len(), 1);
    let heads = join(handle)?;
    let second = heads
        .get(1)
        .map(|h| String::from_utf8_lossy(h).into_owned());
    assert!(
        second
            .as_deref()
            .is_some_and(|h| h.contains("\r\nCookie: s=1\r\n")),
        "{second:?}"
    );
    Ok(())
}
