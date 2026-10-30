//! `clazel-renderer`: enter the sandbox, then take committed documents: run a
//! user script, or display a document (a stub until phase-4.md item 4.13).
//! Exit codes: 71 a sandbox layer failed (nothing was read), 70 the socket or
//! protocol failed, 64 the script is not a script. The messages go to
//! standard error, which the host reports.

use std::io;
use std::process::ExitCode;

fn main() -> ExitCode {
    // First act, before a byte is read: fail closed.
    if let Err(failure) = clazel_renderer::sandbox::enter() {
        eprintln!("clazel-renderer: {failure}");
        return ExitCode::from(71);
    }
    // The host gave this process one socket as both stdin and stdout.
    match clazel_renderer::run(&mut io::stdin().lock(), &mut io::stdout().lock()) {
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
