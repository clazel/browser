//! The command line of the host shell (not part of the line-counted shell in
//! `src/`: it only calls `Host`'s public functions).
//!
//! - `clazel URL SCRIPT`: open a tab at URL running SCRIPT (operations, one
//!   per line, in `clazel-renderer`'s format) and print what the renderer and
//!   the kernel say to each other.
//! - `clazel demo`: the exit demo of phase-2.md item 2.16 (`demo.rs`).
//! - `clazel fetch URL`: one `http://` GET, printing the response
//!   (`fetch.rs`, Phase 3 item 3.8; no renderer involved).
//!
//! The renderer is `$CLAZEL_RENDERER`, or `clazel-renderer` next to this
//! binary, built with `cargo build -p clazel-renderer` if it is not there
//! (`cargo run -p clazel` builds only this package).

mod demo;
mod fetch;

use std::path::PathBuf;
use std::process::{Command, ExitCode};
use std::time::Duration;

/// Where the renderer binary is; builds it if it is missing.
fn renderer() -> Result<PathBuf, String> {
    if let Some(path) = std::env::var_os("CLAZEL_RENDERER") {
        return Ok(path.into());
    }
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let path = exe.with_file_name("clazel-renderer");
    if !path.exists() {
        eprintln!("clazel: building clazel-renderer ...");
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
        let built = Command::new(cargo)
            .args(["build", "-p", "clazel-renderer"])
            .status();
        if !built.is_ok_and(|s| s.success()) || !path.exists() {
            return Err(format!(
                "{} does not exist and could not be built",
                path.display()
            ));
        }
    }
    Ok(path)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if let (Some("fetch"), Some(url), None) = (args.get(1).map(String::as_str), args.get(2), args.get(3)) {
        return fetch::run(url);
    }
    let renderer = match renderer() {
        Ok(path) => path,
        Err(e) => {
            eprintln!("clazel: {e}");
            return ExitCode::FAILURE;
        }
    };
    let mut host = clazel::Host::new(move |_| Command::new(&renderer));
    match (args.get(1).map(String::as_str), args.get(2)) {
        (Some("demo"), None) => demo::run(host),
        (Some(url), Some(script)) => {
            host.open_tab(url, script);
            if host.live() > 0 && host.run(Duration::from_secs(30)) {
                return ExitCode::SUCCESS;
            }
            eprintln!("clazel: no renderer started for {url}, or one is still running after 30 s");
            ExitCode::FAILURE
        }
        _ => {
            eprintln!("usage: clazel URL SCRIPT | clazel demo | clazel fetch URL");
            ExitCode::from(2)
        }
    }
}
