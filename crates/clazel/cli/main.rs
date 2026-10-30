//! The command line of the host shell (not part of the line-counted shell in
//! `src/`: it only calls `Host`'s public functions).
//!
//! - `clazel URL SCRIPT`: open a tab at URL running SCRIPT (operations, one
//!   per line, in `clazel-renderer`'s format) and print what the renderer and
//!   the kernel say to each other.
//! - `clazel demo`: the exit demo of phase-2.md item 2.16 (`demo.rs`).
//! - `clazel fetch URL`: one `http://` GET, printing the response
//!   (`fetch.rs`, Phase 3 item 3.8; no renderer involved).
//! - `clazel browse URL`: the text-mode browser of phase-4.md item 4.15
//!   (`browse.rs`). The host's log of frames goes to standard error.
//!
//! The renderer is `$CLAZEL_RENDERER`, or `clazel-renderer` next to this
//! binary, built with `cargo build -p clazel-renderer` if it is not there
//! (`cargo run -p clazel` builds only this package).

mod browse;
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
    // Resolve symlinks: an install links `bin/clazel` to the binary next to
    // the renderer, and macOS reports the link's path, not its target.
    let exe = std::env::current_exe()
        .and_then(std::fs::canonicalize)
        .map_err(|e| e.to_string())?;
    let path = exe.with_file_name(format!("clazel-renderer{}", std::env::consts::EXE_SUFFIX));
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

/// The terminal width: `$COLUMNS`, or 80.
fn columns() -> usize {
    std::env::var("COLUMNS")
        .ok()
        .and_then(|c| c.trim().parse::<usize>().ok())
        .filter(|w| *w > 0)
        .unwrap_or(80)
}

/// `clazel browse URL` on standard input and output, `width` columns wide.
fn browse_stdio(mut host: clazel::Host, url: &str, width: usize) -> ExitCode {
    let mut out = std::io::stdout().lock();
    match browse::browse(&mut host, url, std::io::stdin().lock(), &mut out, width) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("clazel: browse: {e}");
            ExitCode::FAILURE
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if let (Some("fetch"), Some(url), None) =
        (args.get(1).map(String::as_str), args.get(2), args.get(3))
    {
        return fetch::run(url);
    }
    let renderer = match renderer() {
        Ok(path) => path,
        Err(e) => {
            eprintln!("clazel: {e}");
            return ExitCode::FAILURE;
        }
    };
    // Renderers lay documents out at the terminal's width (item 4.13).
    let width = columns();
    let mut host = clazel::Host::new(move |_| {
        let mut c = Command::new(&renderer);
        c.args(["--width", &width.to_string()]);
        c
    });
    match (args.get(1).map(String::as_str), args.get(2)) {
        (Some("demo"), None) => demo::run(host),
        (Some("browse"), Some(url)) => browse_stdio(host, url, width),
        (Some(url), Some(script)) => {
            host.open_tab(url, script);
            if host.live() > 0 && host.run(Duration::from_secs(30)) {
                return ExitCode::SUCCESS;
            }
            eprintln!("clazel: no renderer started for {url}, or one is still running after 30 s");
            ExitCode::FAILURE
        }
        _ => {
            eprintln!(
                "usage: clazel URL SCRIPT | clazel demo | clazel fetch URL | clazel browse URL"
            );
            ExitCode::from(2)
        }
    }
}
