//! The command line of the host shell (not part of the line-counted shell in
//! `src/`: it only calls `Host`'s public functions).
//!
//! - `clazel URL SCRIPT`: open a tab at URL running SCRIPT (operations, one
//!   per line, in `clazel-renderer`'s format) and print what the renderer and
//!   the kernel say to each other.
//! - `clazel demo`: the exit demo of phase-2.md item 2.16 (`demo.rs`).
//! - `clazel fetch URL`: one `http://` GET, printing the response
//!   (`fetch.rs`, Phase 3 item 3.8; no renderer involved).
//! - `clazel browse URL`: the browser with a window of phase-5.md item 5.23
//!   (`window.rs`), on macOS on Apple silicon in a window server session;
//!   elsewhere, or with `--text`, the text-mode browser of phase-4.md item 4.15
//!   (`browse.rs`). The host's log of frames goes to standard error.
//! - `clazel browse --headless OUT URL [--size WxH] [--wait S]`: render one page to `OUT`, a
//!   PNG or (`.ppm`) a PPM, without a window (item 5.23).
//! - `--gpu=hardware` with `browse` ignores the driver blocklist (item 5.17c), with
//!   a warning.
//!
//! The renderer is `$CLAZEL_RENDERER`, or `clazel-renderer` next to this
//! binary, built with `cargo build -p clazel-renderer` if it is not there
//! (`cargo run -p clazel` builds only this package). The GPU process is
//! `$CLAZEL_GPU`, or `clazel-gpu` beside it, built the same way.

mod browse;
mod demo;
mod fetch;
mod picture;
mod strip;
#[cfg(test)]
mod strip_tests;
mod window;

use std::path::PathBuf;
use std::process::{Command, ExitCode};
use std::time::Duration;

/// Where the renderer binary is; builds it if it is missing.
fn renderer() -> Result<PathBuf, String> {
    sibling("CLAZEL_RENDERER", "clazel-renderer")
}

/// Where binary `name` is: `$var`, else beside this one, built with `cargo build
/// -p name` if it is missing.
fn sibling(var: &str, name: &str) -> Result<PathBuf, String> {
    if let Some(path) = std::env::var_os(var) {
        return Ok(path.into());
    }
    // Resolve symlinks: an install links `bin/clazel` to the binary next to
    // the renderer, and macOS reports the link's path, not its target.
    let exe = std::env::current_exe()
        .and_then(std::fs::canonicalize)
        .map_err(|e| e.to_string())?;
    let path = exe.with_file_name(format!("{name}{}", std::env::consts::EXE_SUFFIX));
    if !path.exists() {
        eprintln!("clazel: building {name} ...");
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
        // Build into the directory this binary is in: a release `clazel`
        // looks beside itself in `target/release`, where a plain `cargo
        // build` (the dev profile) puts nothing.
        let release = exe
            .parent()
            .and_then(|dir| dir.file_name())
            .is_some_and(|dir| dir == "release");
        let mut build = Command::new(cargo);
        build.args(["build", "-p", name]);
        if release {
            build.arg("--release");
        }
        let built = build.status();
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
    let mut host = text_host(renderer.clone(), width);
    if args.get(1).map(String::as_str) == Some("browse") {
        drop(host);
        return browse_command(renderer, args.get(2..).unwrap_or_default(), width);
    }
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
        _ => usage(),
    }
}

fn usage() -> ExitCode {
    eprintln!(
        "usage: clazel URL SCRIPT | clazel demo | clazel fetch URL | \
         clazel browse [--text | --headless OUT [--size WxH] [--wait S]] [--gpu=hardware] URL"
    );
    ExitCode::from(2)
}

/// `WxH`, each side 1 to 8192.
fn size(s: &str) -> Option<(u32, u32)> {
    let (w, h) = s.split_once(['x', 'X', '×'])?;
    let side = |v: &str| v.parse::<u32>().ok().filter(|v| (1..=8192).contains(v));
    Some((side(w)?, side(h)?))
}

/// A host in text mode: renderers lay documents out `width` columns wide (item
/// 4.13) and send `Display`.
fn text_host(renderer: PathBuf, width: usize) -> clazel::Host {
    clazel::Host::new(move |_| {
        let mut c = Command::new(&renderer);
        c.args(["--width", &width.to_string()]);
        c
    })
}

/// `clazel browse ...`.
fn browse_command(renderer: PathBuf, args: &[String], width: usize) -> ExitCode {
    let flag = |f: &str| args.iter().any(|a| a == f);
    let value = |f: &str| {
        let i = args.iter().position(|a| a == f)?;
        args.get(i.checked_add(1)?).cloned()
    };
    let Some(url) = args.last().filter(|u| !u.starts_with("--")) else {
        return usage();
    };
    let headless = value("--headless");
    if flag("--text") {
        return browse_stdio(text_host(renderer, width), url, width);
    }
    if headless.is_none()
        && let Err(why) = window_available()
    {
        eprintln!("clazel: {why}; browsing in text mode");
        return browse_stdio(text_host(renderer, width), url, width);
    }
    let gpu = match sibling("CLAZEL_GPU", "clazel-gpu") {
        Ok(path) => path,
        Err(e) => {
            eprintln!("clazel: {e}");
            return ExitCode::FAILURE;
        }
    };
    let ignore = flag("--gpu=hardware");
    if ignore {
        eprintln!("clazel: --gpu=hardware: the driver blocklist is ignored");
    }
    // Item 5.23: renderers paired with a GPU process get its list socket
    // (`--list-fd`, added by the host) and the fonts to lay out in.
    let fonts = window::renderer_fonts();
    let mut host = clazel::Host::new(move |_| {
        let mut c = Command::new(&renderer);
        c.args(["--width", &width.to_string()]);
        for f in &fonts {
            c.arg("--font").arg(f);
        }
        c
    })
    .with_gpu(move |_| {
        let mut c = Command::new(&gpu);
        if ignore {
            c.arg("--ignore-blocklist");
        }
        c
    });
    if let Some(out) = headless {
        let Some(dims) = value("--size").map_or(Some((1024, 768)), |s| size(&s)) else {
            return usage();
        };
        let wait = match value("--wait").map(|w| w.parse::<u64>()) {
            None => window::HEADLESS_WAIT,
            Some(Ok(s)) => Duration::from_secs(s),
            Some(Err(_)) => return usage(),
        };
        return match window::headless(&mut host, std::path::Path::new(&out), url, dims, wait) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("clazel: browse --headless: {e}");
                ExitCode::FAILURE
            }
        };
    }
    browse_window(host, url, width)
}

/// Whether `browse` can open a window here, or why not.
fn window_available() -> Result<(), &'static str> {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        return Err("no window on this platform yet (phase-5.md items 5.22, 5.22a)");
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if !clazel_window::has_window_server() {
        return Err("no window server session");
    }
    Ok(())
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn browse_window(mut host: clazel::Host, url: &str, _width: usize) -> ExitCode {
    match window::mac::run(&mut host, url) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("clazel: browse: {e}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
fn browse_window(host: clazel::Host, url: &str, width: usize) -> ExitCode {
    browse_stdio(host, url, width)
}
