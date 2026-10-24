//! `clazel fetch URL`: one `http://` GET through `clazel_net::fetch`,
//! printing the status line, the header fields and the body as received.

use std::io::Write;
use std::process::ExitCode;

/// Fetches `url` and writes the response to standard output.
pub fn run(url: &str) -> ExitCode {
    match clazel_net::fetch(url) {
        Ok(r) => {
            let mut out = Vec::new();
            let sl = &r.status_line;
            out.extend_from_slice(format!("HTTP/{}.{} {:03} ", sl.major, sl.minor, sl.status).as_bytes());
            out.extend_from_slice(&sl.reason);
            out.extend_from_slice(b"\n");
            for f in &r.fields {
                out.extend_from_slice(&f.name);
                out.extend_from_slice(b": ");
                out.extend_from_slice(&f.value);
                out.extend_from_slice(b"\n");
            }
            out.extend_from_slice(b"\n");
            out.extend_from_slice(&r.body);
            let mut stdout = std::io::stdout().lock();
            if stdout.write_all(&out).and_then(|()| stdout.flush()).is_err() {
                return ExitCode::FAILURE;
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("clazel: fetch {url}: {e}");
            ExitCode::FAILURE
        }
    }
}
