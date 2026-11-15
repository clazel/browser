//! An https page with an https style sheet, through the real renderer and GPU
//! process (phase-5.md items 5.19, 5.23 and 5.26's https demo): the page and its
//! linked sheet both come from a rustls server on loopback (TLS 1.3,
//! ChaCha20-Poly1305, X25519, the certificates of
//! `clazel-crypto/tests/fixtures/tls`, which the host trusts through `trust`, as
//! `host.rs` does), the sheet through `FetchStyle` on its own TLS connection
//! (`SubConnect { tls: true }`), and:
//!
//! - the sheet's request carries the cookie the page set, since it is same-origin
//!   (5.19's credentials rule);
//! - the painted frame has the sheet's background colour, so the sheet arrived and
//!   applied.
//!
//! macOS on Apple silicon only (the GPU process's only backend); without a Metal
//! device it skips, except under CI.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

mod support;

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener};
use std::process::Command;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_kernel::exec::records::{EventRecord, OutputRecord};
use clazel_net::{ChainVerifier, Root};

static ROOT: &[u8] = include_bytes!("../../clazel-crypto/tests/fixtures/tls/root.der");
static INTERMEDIATE: &[u8] =
    include_bytes!("../../clazel-crypto/tests/fixtures/tls/intermediate.der");
static LEAF: &[u8] = include_bytes!("../../clazel-crypto/tests/fixtures/tls/leaf-ecdsa.der");
static KEY: &[u8] = include_bytes!("../../clazel-crypto/tests/fixtures/tls/leaf-ecdsa.key.der");

const DEJAVU: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf"
);

fn test_root() -> ChainVerifier<'static> {
    ChainVerifier::new(&[Root {
        der: ROOT,
        server_distrust_after: None,
    }])
}

/// The page: it sets a cookie and links the sheet.
const PAGE: &str = "<!doctype html><title>https</title>\
<link rel=stylesheet href=/s.css><body><p>styled over TLS</p></body>";

/// The sheet: a green body.
const SHEET: &str = "body { margin: 0; background: #00c000 }";

/// A TLS server on loopback for `test.example`: `/` is [`PAGE`] with a
/// `Set-Cookie`, `/s.css` is [`SHEET`]. Every request head is kept.
fn serve() -> (SocketAddr, Arc<Mutex<Vec<String>>>) {
    use rustls::crypto::ring::{cipher_suite::TLS13_CHACHA20_POLY1305_SHA256, default_provider};
    use rustls::crypto::{CryptoProvider, ring::kx_group::X25519};
    use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
    use rustls::{ServerConfig, ServerConnection, StreamOwned};

    let heads: Arc<Mutex<Vec<String>>> = Arc::default();
    let dead = SocketAddr::from(([127, 0, 0, 1], 9));
    let provider = CryptoProvider {
        cipher_suites: vec![TLS13_CHACHA20_POLY1305_SHA256],
        kx_groups: vec![X25519],
        ..default_provider()
    };
    let chain = vec![
        CertificateDer::from(LEAF.to_vec()),
        CertificateDer::from(INTERMEDIATE.to_vec()),
    ];
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(KEY.to_vec()));
    let config = ServerConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .and_then(|b| b.with_no_client_auth().with_single_cert(chain, key));
    let (Ok(config), Ok(listener)) = (config, TcpListener::bind("127.0.0.1:0")) else {
        return (dead, heads);
    };
    let config = Arc::new(config);
    let addr = listener.local_addr().unwrap_or(dead);
    let log = Arc::clone(&heads);
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(stream) = stream else { continue };
            let (config, log) = (Arc::clone(&config), Arc::clone(&log));
            std::thread::spawn(move || {
                let _ = stream.set_read_timeout(Some(Duration::from_secs(10)));
                let Ok(conn) = ServerConnection::new(config) else {
                    return;
                };
                let mut tls = StreamOwned::new(conn, stream);
                let mut request = Vec::new();
                let mut buf = [0u8; 4096];
                while !request.ends_with(b"\r\n\r\n") {
                    match tls.read(&mut buf) {
                        Ok(0) | Err(_) => return,
                        Ok(n) => request.extend_from_slice(buf.get(..n).unwrap_or_default()),
                    }
                }
                let head = String::from_utf8_lossy(&request).into_owned();
                let sheet = head.starts_with("GET /s.css ");
                if let Ok(mut l) = log.lock() {
                    l.push(head);
                }
                let reply = if sheet {
                    format!(
                        "HTTP/1.1 200 OK\r\nContent-Type: text/css\r\nContent-Length: {}\r\n\
                         Connection: close\r\n\r\n{SHEET}",
                        SHEET.len()
                    )
                } else {
                    format!(
                        "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nSet-Cookie: a=1; Path=/\r\n\
                         Content-Length: {}\r\nConnection: close\r\n\r\n{PAGE}",
                        PAGE.len()
                    )
                };
                let _ = tls.write_all(reply.as_bytes());
                let _ = tls.flush();
                let mut rest = Vec::new();
                let _ = tls.read_to_end(&mut rest);
                tls.conn.send_close_notify();
                let _ = tls.flush();
            });
        }
    });
    (addr, heads)
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes")]
fn an_https_page_with_an_https_sheet_paints_with_the_sheet() {
    if let Err(e) = clazel_gpu::metal::MetalBackend::new() {
        eprintln!("https_sheet: skipped: no Metal device ({})", e.what);
        assert!(std::env::var_os("CI").is_none(), "no Metal device under CI");
        return;
    }
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let built = Command::new(cargo)
        .args([
            "build",
            "--quiet",
            "-p",
            "clazel-gpu",
            "-p",
            "clazel-renderer",
        ])
        .status();
    assert!(built.is_ok_and(|s| s.success()));
    let renderer = support::binary("clazel-renderer");
    let gpu = renderer.with_file_name("clazel-gpu");
    let (addr, heads) = serve();
    let mut host = Host::new(move |_| {
        let mut c = Command::new(&renderer);
        c.args(["--font", DEJAVU]);
        c
    })
    .with_gpu(move |_| Command::new(&gpu));
    host.route = Some(addr);
    host.trust(test_root);
    let tab = host.open("https://test.example/");
    host.event(EventRecord::Resize {
        tab,
        width: 120,
        height: 80,
        scale: 1,
    });
    let start = Instant::now();
    let mut paint = None;
    let mut frame = None;
    while frame.is_none() && start.elapsed() < Duration::from_secs(20) {
        host.pump(Duration::from_millis(20));
        if let Some(i) = host
            .shown
            .iter()
            .position(|o| matches!(o, OutputRecord::Paint { tab: t, .. } if *t == tab))
        {
            paint = Some(host.shown.remove(i));
        }
        let id = host
            .state
            .renderers
            .iter()
            .find(|r| r.tab == tab)
            .map(|r| r.id);
        if let (Some(id), Some(OutputRecord::Paint { buffer, .. })) = (id, &paint) {
            frame = host.take_frame(id, u32::try_from(*buffer).unwrap_or(u32::MAX));
        }
    }
    assert!(frame.is_some(), "no paint: {:#?}", host.log);
    let Some(frame) = frame else { return };
    // The sheet's connection was its own, over TLS.
    let tls_connections = host
        .log
        .iter()
        .filter(|l| l.contains("to test.example:443 (TLS)"))
        .count();
    assert_eq!(tls_connections, 2, "{:#?}", host.log);
    // The sheet's request is same-origin, so it carries the page's cookie.
    let heads = heads.lock().map(|h| h.clone()).unwrap_or_default();
    let sheet = heads.iter().find(|h| h.starts_with("GET /s.css "));
    assert!(sheet.is_some(), "the sheet was never asked for: {heads:#?}");
    assert!(
        sheet.is_some_and(|h| h.lines().any(|l| l.eq_ignore_ascii_case("cookie: a=1"))),
        "{heads:#?}"
    );
    // The sheet applied: the canvas is its green.
    let px = |x: usize, y: usize| {
        frame
            .pixels
            .get((y * 120 + x) * 4..(y * 120 + x) * 4 + 4)
            .map(<[u8]>::to_vec)
    };
    assert_eq!(px(110, 70), Some(vec![0, 0xc0, 0, 0xff]));
}
