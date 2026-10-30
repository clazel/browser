//! Sandbox escape attempts from a real AppContainer process (Windows half of
//! `escape.rs`): `clazel-adversary` is started by `launch::spawn` (inside the
//! AppContainer, the job and the mitigations), makes one call that would reach
//! something other than its pipes, and the test requires `DENIED`.
//!
//! Each attempt first runs unsandboxed (`control`) against a target of its own
//! and must `ESCAPED`, so a denial is the sandbox's and not a wrong path.
//!
//! Not covered: `unix-connect` and `unix-listen` (`std` has no Unix sockets
//! on Windows, so the attempt is unsupported everywhere there) and `fork`
//! (Windows has none; `execve` is process creation).
#![cfg(windows)]

use std::fs;
use std::io::Read;
use std::net::TcpListener;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Duration;

use clazel_renderer::escape::Attempt;
use clazel_renderer::launch;

const ADVERSARY: &str = env!("CARGO_BIN_EXE_clazel-adversary");

type T = Result<(), Box<dyn std::error::Error>>;

/// The adversary outside any sandbox: what the attempt does when nothing stops it.
fn control(attempt: Attempt, target: &str) -> Result<String, Box<dyn std::error::Error>> {
    let out = Command::new(ADVERSARY)
        .args(["control", attempt.name(), target])
        .stdin(Stdio::null())
        .output()?;
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// The adversary started in the AppContainer: its output and its stderr.
fn sandboxed(
    attempt: Attempt,
    target: &str,
) -> Result<(String, String), Box<dyn std::error::Error>> {
    let mut command = Command::new(ADVERSARY);
    command.args(["escape", attempt.name(), target]);
    let (link, mut reader) = launch::spawn(command)?;
    let mut stdout = String::new();
    reader.read_to_string(&mut stdout)?;
    let (status, stderr) = link.finish(Duration::from_secs(5));
    Ok((stdout, format!("{status}; {stderr}")))
}

fn scratch(name: &str) -> Result<PathBuf, Box<dyn std::error::Error>> {
    let dir = std::env::temp_dir().join(format!("clazel-escape-{}", std::process::id()));
    fs::create_dir_all(&dir)?;
    Ok(dir.join(name))
}

/// The attempt escapes unsandboxed and is denied in the AppContainer.
fn denied(attempt: Attempt, control_target: &str, target: &str) -> T {
    let free = control(attempt, control_target)?;
    assert!(
        free.starts_with("ESCAPED"),
        "{}: the control did not succeed, so a denial would prove nothing: {free:?}",
        attempt.name()
    );
    let (out, err) = sandboxed(attempt, target)?;
    assert!(
        out.starts_with("DENIED"),
        "{}: expected DENIED, got stdout {out:?}, stderr/status {err:?}",
        attempt.name()
    );
    Ok(())
}

#[test]
fn the_cookie_jar_and_other_files_cannot_be_read() -> T {
    let jar = scratch("cookies.db")?;
    fs::write(&jar, b"secret")?;
    let jar = jar.to_string_lossy().into_owned();
    denied(Attempt::OpenCookieJar, &jar, &jar)?;
    denied(Attempt::OpenFile, &jar, &jar)
}

#[test]
fn no_file_can_be_created() -> T {
    let free = scratch("control.txt")?;
    let boxed = scratch("sandboxed.txt")?;
    let _ = fs::remove_file(&free);
    let _ = fs::remove_file(&boxed);
    denied(
        Attempt::CreateFile,
        &free.to_string_lossy(),
        &boxed.to_string_lossy(),
    )?;
    assert!(!boxed.exists(), "the sandboxed process created a file");
    Ok(())
}

#[test]
fn no_tcp_connection_can_be_made_or_accepted() -> T {
    let listener = TcpListener::bind("127.0.0.1:0")?;
    let addr = listener.local_addr()?.to_string();
    denied(Attempt::TcpConnect, &addr, &addr)?;
    denied(Attempt::TcpListen, "127.0.0.1:0", "127.0.0.1:0")
}

#[test]
fn no_udp_socket_can_be_bound() -> T {
    denied(Attempt::UdpBind, "127.0.0.1:0", "127.0.0.1:0")
}

#[test]
fn no_program_can_be_started() -> T {
    let whoami = r"C:\Windows\System32\whoami.exe";
    denied(Attempt::Execve, whoami, whoami)
}

#[test]
fn a_sibling_process_cannot_be_opened() -> T {
    let mut sibling = Command::new(ADVERSARY)
        .arg("idle")
        .stdin(Stdio::piped())
        .spawn()?;
    let pid = sibling.id().to_string();
    let result = denied(Attempt::PtraceAttach, &pid, &pid);
    let _ = sibling.kill();
    let _ = sibling.wait();
    result
}
