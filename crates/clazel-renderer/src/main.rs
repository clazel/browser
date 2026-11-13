//! `clazel-renderer [--width N]`: enter the sandbox, then take committed
//! documents: run a user script, or display a document through the
//! pipeline of phase-4.md item 4.13, laid out N columns wide (default 80;
//! 0: no wrapping). The host passes its terminal width as the argument.
//! `--font PATH` (repeated) names font files, read before the sandbox is
//! entered (phase-5.md item 5.20); the graphical pipeline that uses them
//! waits for the list socket (`page/mod.rs`), so they are read only when
//! given, and the text path runs as before.
//! Exit codes: 71 a sandbox layer failed (nothing was read), 70 the socket or
//! protocol failed, 64 the script is not a script. The messages go to
//! standard error, which the host reports.

use std::io;
use std::process::ExitCode;

/// The `--width N` argument, or the default; any other argument is
/// ignored (the host builds the command line).
fn width() -> usize {
    let args: Vec<String> = std::env::args().collect();
    args.iter()
        .position(|a| a == "--width")
        .and_then(|i| args.get(i.saturating_add(1)))
        .and_then(|w| w.parse::<usize>().ok())
        .unwrap_or(clazel_renderer::DEFAULT_WIDTH)
}

/// The `--font PATH` arguments.
fn font_paths() -> Vec<std::path::PathBuf> {
    let args: Vec<String> = std::env::args().collect();
    args.windows(2)
        .filter(|w| w.first().is_some_and(|a| a == "--font"))
        .filter_map(|w| w.get(1).map(std::path::PathBuf::from))
        .collect()
}

fn main() -> ExitCode {
    let width = width();
    // Fonts are read before the sandbox, which forbids opening any file.
    let paths = font_paths();
    let refs: Vec<&std::path::Path> = paths.iter().map(|p| p.as_path()).collect();
    let _fonts = clazel_renderer::page::fonts::Fonts::read(&refs);
    // First act, before a byte is read: fail closed.
    if let Err(failure) = clazel_renderer::sandbox::enter() {
        eprintln!("clazel-renderer: {failure}");
        return ExitCode::from(71);
    }
    // The host gave this process one socket as both stdin and stdout.
    match clazel_renderer::run_with_width(&mut io::stdin().lock(), &mut io::stdout().lock(), width)
    {
        Ok(_) => ExitCode::SUCCESS,
        Err(e @ clazel_renderer::RunError::Script(_)) => {
            eprintln!("clazel-renderer: {e}");
            ExitCode::from(64)
        }
        Err(e) => {
            eprintln!("clazel-renderer: {e}");
            ExitCode::from(70)
        }
    }
}
