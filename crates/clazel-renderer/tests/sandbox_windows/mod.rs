//! The Windows half of the `sandbox` test (see `sandbox.rs`).

use std::io::Read;
use std::process::{Command, ExitCode};
use std::time::Duration;

use clazel_renderer::{launch, sandbox};

/// Inside the AppContainer: `enter` accepts, the file cannot be opened and no
/// socket works (Winsock cannot start, which `std` reports as a panic).
fn probe(file: &str) {
    if let Err(failure) = sandbox::enter() {
        eprintln!("FAILED-CLOSED {failure}");
        return;
    }
    let file_denied = std::fs::File::open(file).is_err();
    let net_denied =
        std::panic::catch_unwind(|| std::net::TcpStream::connect(("127.0.0.1", 9)).is_err())
            .unwrap_or(true);
    if file_denied && net_denied {
        println!("SANDBOXED");
    } else {
        println!("ESCAPED file_denied={file_denied} net_denied={net_denied}");
    }
}

pub fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if let (Some("probe"), Some(file)) = (args.get(1).map(String::as_str), args.get(2)) {
        probe(file);
        return ExitCode::SUCCESS;
    }
    match check() {
        Ok(()) => {
            println!("sandbox: unconfined enter refuses; the AppContainer probe is SANDBOXED");
            ExitCode::SUCCESS
        }
        Err(why) => {
            eprintln!("sandbox: FAILED: {why}");
            ExitCode::FAILURE
        }
    }
}

fn check() -> Result<(), String> {
    match sandbox::enter() {
        Err(failure) if failure.layer == "appcontainer" => {}
        other => return Err(format!("outside the AppContainer, enter gave {other:?}")),
    }
    let secret = std::env::temp_dir().join(format!("clazel-sandbox-{}.txt", std::process::id()));
    std::fs::write(&secret, b"secret").map_err(|e| e.to_string())?;
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let mut command = Command::new(exe);
    command.arg("probe").arg(&secret);
    let (link, mut reader) = launch::spawn(command).map_err(|e| e.to_string())?;
    let mut stdout = String::new();
    let _ = reader.read_to_string(&mut stdout);
    let (status, stderr) = link.finish(Duration::from_secs(5));
    let _ = std::fs::remove_file(&secret);
    if stdout.contains("SANDBOXED") {
        Ok(())
    } else {
        Err(format!(
            "the probe was not confined: {status}, stdout {stdout:?}, stderr {stderr:?}"
        ))
    }
}
