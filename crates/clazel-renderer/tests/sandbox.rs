//! The sandbox, entered for real in a child process (this test, run again
//! with `CLAZEL_SANDBOX_PROBE` set): the probe enters the sandbox first, then
//! tries to open a file and a TCP connection, which must both fail.
//!
//! Fail closed is allowed to show as "no sandbox here": on Linux a kernel or
//! container may refuse a layer, and then `enter` names it and the probe
//! exits, which is also a pass of this test (the renderer would not run
//! either). A seccomp kill (SIGSYS) on a forbidden call is a pass. On macOS
//! only a working sandbox passes. On Windows the host starts the probe inside
//! the AppContainer (`launch::spawn`) and `enter` only checks that it is there:
//! run by hand, outside it, `enter` must refuse; run through `launch`, the
//! probe must find a file and the network closed to it.

#[cfg(windows)]
#[path = "sandbox_windows/mod.rs"]
mod windows;
#[cfg(windows)]
fn main() -> std::process::ExitCode {
    windows::main()
}

#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;
#[cfg(unix)]
use std::process::{Command, ExitCode};

#[cfg(unix)]
const PROBE: &str = "CLAZEL_SANDBOX_PROBE";

#[cfg(unix)]
fn probe() {
    if let Err(failure) = clazel_renderer::sandbox::enter() {
        eprintln!("FAILED-CLOSED {failure}");
        return;
    }
    let file_denied = std::fs::File::open("/etc/hosts").is_err();
    let net_denied = std::net::TcpStream::connect(("127.0.0.1", 9)).is_err();
    if file_denied && net_denied {
        println!("SANDBOXED");
    } else {
        println!("ESCAPED file_denied={file_denied} net_denied={net_denied}");
    }
}

#[cfg(unix)]
fn main() -> ExitCode {
    if std::env::var_os(PROBE).is_some() {
        probe();
        return ExitCode::SUCCESS;
    }
    if cfg!(miri) {
        println!("sandbox: skipped under Miri (spawns a process and calls the OS)");
        return ExitCode::SUCCESS;
    }
    match check() {
        Ok(summary) => {
            println!("sandbox: {summary}");
            ExitCode::SUCCESS
        }
        Err(why) => {
            eprintln!("sandbox: FAILED: {why}");
            ExitCode::FAILURE
        }
    }
}

/// Run the probe in a child process and judge how it ended.
#[cfg(unix)]
fn check() -> Result<String, String> {
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let out = Command::new(exe)
        .env(PROBE, "1")
        .output()
        .map_err(|e| e.to_string())?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    let killed_by_seccomp = cfg!(target_os = "linux") && out.status.signal() == Some(31);
    let sandboxed = stdout.contains("SANDBOXED");
    let failed_closed = cfg!(target_os = "linux") && stderr.contains("FAILED-CLOSED sandbox layer");
    if sandboxed || killed_by_seccomp || failed_closed {
        Ok(format!(
            "sandboxed={sandboxed} killed_by_seccomp={killed_by_seccomp} failed_closed={failed_closed}"
        ))
    } else {
        Err(format!(
            "the probe was not confined: status {:?}, stdout {stdout:?}, stderr {stderr:?}",
            out.status
        ))
    }
}
