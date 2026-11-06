//! Which top sites refuse this TLS client (phase-3.md item 3.5g): "a local
//! measurement, documented not asserted, of which of the top sites refuse a
//! ChaCha20-only, X25519-only client (run locally, like the demo)".
//!
//! Reads `rank,domain` lines (a Tranco CSV), runs one TLS handshake per
//! domain on port 443 with the production verifier and writes one tab
//! separated line each: rank, domain, the host tried, milliseconds, outcome.
//! A domain with no answer on 443 is tried once more as `www.<domain>`.
//!
//! ```text
//! cargo run -p clazel-net --example tls_survey -- sites.csv out.tsv 8
//! ```

use clazel_crypto::join::exec::mozilla;
use clazel_net::{NetError, Timeouts, TlsConnection, resolve};
use clazel_tls::host::exec::Host;
use std::fs::File;
use std::io::Write;
use std::panic::catch_unwind;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// Handshakes running at once, unless the command line says otherwise.
const WORKERS: usize = 8;

const TIMEOUTS: Timeouts = Timeouts {
    connect: Duration::from_secs(5),
    idle: Duration::from_secs(10),
};

/// One handshake, closed with a close_notify. Only the handshake's result
/// counts: a failing close says nothing about what the survey measures.
fn handshake(host: &str, now: u64) -> Result<(), NetError> {
    let addrs = resolve(host.as_bytes())?;
    let name = Host::Dns(host.as_bytes().to_vec());
    let tls = TlsConnection::open(&addrs, 443, TIMEOUTS, name, now, mozilla())?;
    tls.close().ok();
    Ok(())
}

/// The handshake's outcome as text; a panic is an outcome too, since a
/// server must never be able to cause one.
fn attempt(host: &str, now: u64) -> (String, bool) {
    match catch_unwind(|| handshake(host, now)) {
        Ok(Ok(())) => ("ok".to_owned(), false),
        Ok(Err(e)) => {
            let unanswered = matches!(
                e,
                NetError::Resolve(_) | NetError::Connect(_) | NetError::Timeout(_)
            );
            (format!("{e:?}"), unanswered)
        }
        Err(_) => ("panic".to_owned(), false),
    }
}

/// One line of the result for one `rank,domain` line.
fn survey(line: &str, now: u64) -> Option<String> {
    let (rank, domain) = line.trim().split_once(',')?;
    let start = Instant::now();
    let (mut outcome, unanswered) = attempt(domain, now);
    let mut host = domain.to_owned();
    if unanswered {
        let www = format!("www.{domain}");
        let (second, _) = attempt(&www, now);
        outcome = format!("{second}\tapex: {outcome}");
        host = www;
    }
    let ms = start.elapsed().as_millis();
    Some(format!("{rank}\t{domain}\t{host}\t{ms}\t{outcome}\n"))
}

fn main() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let usage = "usage: tls_survey <sites.csv> <out.tsv> [workers]";
    let sites = args.next().ok_or(usage)?;
    let out = args.next().ok_or(usage)?;
    let workers = match args.next() {
        Some(n) => n.parse::<usize>().map_err(|e| e.to_string())?,
        None => WORKERS,
    };
    let text = std::fs::read_to_string(&sites).map_err(|e| format!("{sites}: {e}"))?;
    let lines: Vec<&str> = text.lines().collect();
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_secs();
    let file = Mutex::new(File::create(&out).map_err(|e| format!("{out}: {e}"))?);
    let next = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                while let Some(line) = lines.get(next.fetch_add(1, Ordering::Relaxed)) {
                    let Some(row) = survey(line, now) else {
                        continue;
                    };
                    if let Ok(mut f) = file.lock() {
                        f.write_all(row.as_bytes()).ok();
                    }
                }
            });
        }
    });
    Ok(())
}
