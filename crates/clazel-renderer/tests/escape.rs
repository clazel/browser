//! Sandbox escape attempts from a real sandboxed process (phase-2.md item
//! 2.16): `clazel-adversary` enters the sandbox as the renderer does, makes
//! one call that would reach something other than its socket, and the test
//! judges how it ended.
//!
//! - **macOS (Seatbelt):** the call returns an error (`DENIED`, exit 0).
//! - **Linux (seccomp):** the filter kills the process with `SIGSYS` (signal
//!   31) on the forbidden call; *only* that passes. An error return is a
//!   failure there (it would mean the call got past seccomp), and so is a
//!   renderer that fails closed before the call (`FAILED-CLOSED`): the test
//!   cannot show anything then, which is what happens on a runner that
//!   restricts unprivileged user namespaces (see the 2.16 section of
//!   docs/phases/phase-2.md). The Linux half has not been run (written on a
//!   Mac; CI is its first run).
//!
//! Each attempt first runs unsandboxed (`control`) against a target of its own
//! and must succeed, so a denial is the sandbox's and not a wrong path. The
//! `fork` and `ptrace-attach` attempts use `clazel-sys`'s `attempt_fork` and
//! `attempt_ptrace_attach` (awaiting their audit, see docs/SYS-AUDITS.md).
//! `ptrace-attach` targets a sibling: an unsandboxed `clazel-adversary idle`
//! the test started, which is not a descendant of the adversary. On Linux
//! with Yama's `ptrace_scope` above 0 (Ubuntu's default) even the unsandboxed
//! control is refused (`EPERM`) for that reason, so there the control may
//! end in that error instead of succeeding; the sandboxed run must still be
//! killed by `SIGSYS`.

use std::fs;
use std::net::TcpListener;
use std::os::unix::net::UnixListener;
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::{Child, Command, Output, Stdio};

use clazel_renderer::escape::Attempt;

const ADVERSARY: &str = env!("CARGO_BIN_EXE_clazel-adversary");
/// `SIGSYS`, which seccomp's `SECCOMP_RET_KILL_PROCESS` raises.
const SIGSYS: i32 = 31;

/// A scratch directory with a short path (a Unix socket's path is limited to
/// about 100 bytes, which `CARGO_TARGET_TMPDIR` can exceed).
fn scratch(attempt: Attempt) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "clazel-escape-{}-{}",
        std::process::id(),
        attempt.name()
    ));
    let _ = fs::remove_dir_all(&dir);
    let _ = fs::create_dir_all(&dir);
    dir
}

fn adversary(mode: &str, attempt: Attempt, target: &str) -> Output {
    let out = Command::new(ADVERSARY)
        .args([mode, attempt.name(), target])
        .output();
    assert!(out.is_ok(), "cannot run {ADVERSARY}: {out:?}");
    out.unwrap_or(Output {
        status: ExitStatusExt::from_raw(0),
        stdout: Vec::new(),
        stderr: Vec::new(),
    })
}

fn text(out: &Output) -> String {
    format!(
        "status {:?}, stdout {:?}, stderr {:?}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

/// A sibling process to attach to: `clazel-adversary idle`, killed on drop.
struct Sibling(Option<Child>);

impl Sibling {
    fn start(program: &str) -> Sibling {
        let child = Command::new(program)
            .arg("idle")
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn();
        assert!(child.is_ok(), "cannot start a sibling: {child:?}");
        Sibling(child.ok())
    }

    fn pid(&self) -> String {
        self.0.as_ref().map_or(0, Child::id).to_string()
    }
}

impl Drop for Sibling {
    fn drop(&mut self) {
        if let Some(child) = self.0.as_mut() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

/// The program the sibling runs. On Linux that is the adversary itself. On
/// macOS an unsandboxed process cannot `ptrace` another one unless the target
/// carries the `com.apple.security.get-task-allow` entitlement (what a debug
/// build from Xcode has, and a Cargo build does not): even an unsandboxed
/// attach to a plain child gets `EPERM`. So the sibling is a copy of the
/// adversary, ad-hoc signed with that entitlement, which is the one thing
/// that makes the control attach succeed and a denial the sandbox's.
fn sibling_program(dir: &std::path::Path) -> String {
    if cfg!(not(target_os = "macos")) {
        return ADVERSARY.to_owned();
    }
    let copy = dir.join("debuggable-sibling");
    let plist = dir.join("get-task-allow.plist");
    let entitlements = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
        <!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \
        \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n\
        <plist version=\"1.0\"><dict><key>com.apple.security.get-task-allow</key>\
        <true/></dict></plist>\n";
    assert!(
        fs::copy(ADVERSARY, &copy).is_ok() && fs::write(&plist, entitlements).is_ok(),
        "cannot prepare the debuggable sibling in {dir:?}"
    );
    let signed = Command::new("codesign")
        .args(["--force", "--sign", "-", "--entitlements"])
        .arg(&plist)
        .arg(&copy)
        .output();
    assert!(
        signed.as_ref().is_ok_and(|o| o.status.success()),
        "codesign of the sibling failed: {signed:?}"
    );
    copy.to_string_lossy().into_owned()
}

/// On Linux, Yama's `ptrace_scope` above 0 lets a process attach only to its
/// descendants, so an unsandboxed attach to a sibling gets `EPERM`.
fn yama_restricts_ptrace() -> bool {
    cfg!(target_os = "linux")
        && fs::read_to_string("/proc/sys/kernel/yama/ptrace_scope").is_ok_and(|v| v.trim() != "0")
}

/// What a listener the test keeps alive and the target for `attempt` are.
/// Returns the target the control run and the sandboxed run use.
fn targets(
    attempt: Attempt,
    dir: &std::path::Path,
) -> (String, String, Vec<Box<dyn std::any::Any>>) {
    let p = |name: &str| dir.join(name).to_string_lossy().into_owned();
    let mut keep: Vec<Box<dyn std::any::Any>> = Vec::new();
    let (control, sandboxed) = match attempt {
        Attempt::OpenCookieJar => {
            let jar = p("cookie-jar");
            let _ = fs::write(&jar, "session=secret");
            (jar.clone(), jar)
        }
        Attempt::OpenFile => ("/etc/hosts".to_owned(), "/etc/hosts".to_owned()),
        Attempt::CreateFile => (p("control-new-file"), p("new-file")),
        Attempt::TcpConnect => {
            let listener = TcpListener::bind("127.0.0.1:0");
            let addr = listener
                .as_ref()
                .ok()
                .and_then(|l| l.local_addr().ok())
                .map_or_else(String::new, |a| a.to_string());
            keep.push(Box::new(listener));
            (addr.clone(), addr)
        }
        Attempt::TcpListen => ("127.0.0.1:0".to_owned(), "127.0.0.1:0".to_owned()),
        Attempt::UdpBind => ("127.0.0.1:0".to_owned(), "127.0.0.1:0".to_owned()),
        Attempt::UnixConnect => {
            let listener = UnixListener::bind(p("sock"));
            keep.push(Box::new(listener));
            (p("sock"), p("sock"))
        }
        Attempt::UnixListen => (p("control-listen"), p("listen")),
        Attempt::Execve => ("/bin/echo".to_owned(), "/bin/echo".to_owned()),
        Attempt::Fork => ("-".to_owned(), "-".to_owned()),
        Attempt::PtraceAttach => {
            // One sibling each, so the control's attach cannot leave the
            // sandboxed run's target traced.
            let program = sibling_program(dir);
            let (for_control, for_escape) = (Sibling::start(&program), Sibling::start(&program));
            let pids = (for_control.pid(), for_escape.pid());
            keep.push(Box::new(for_control));
            keep.push(Box::new(for_escape));
            pids
        }
    };
    (control, sandboxed, keep)
}

fn escape_attempt_is_stopped(attempt: Attempt) {
    let dir = scratch(attempt);
    let (control_target, target, _keep) = targets(attempt, &dir);

    let control = adversary("control", attempt, &control_target);
    let control_stdout = String::from_utf8_lossy(&control.stdout).into_owned();
    // Yama is the one documented way an unsandboxed attach to a sibling fails.
    let yama_refused = attempt == Attempt::PtraceAttach
        && yama_restricts_ptrace()
        && control.status.code() == Some(0)
        && control_stdout.starts_with("DENIED")
        && control_stdout.contains("Operation not permitted");
    if yama_refused {
        println!("escape: ptrace-attach control refused by Yama ptrace_scope, as documented");
    }
    assert!(
        yama_refused || (control.status.code() == Some(3) && control_stdout.starts_with("ESCAPED")),
        "{}: the attempt does not even work outside the sandbox, so a denial would prove nothing: {}",
        attempt.name(),
        text(&control)
    );

    let sandboxed = adversary("escape", attempt, &target);
    let stdout = String::from_utf8_lossy(&sandboxed.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&sandboxed.stderr);
    assert!(
        !stderr.contains("FAILED-CLOSED"),
        "{}: the renderer failed closed before the attempt, so nothing was tried: {}",
        attempt.name(),
        text(&sandboxed)
    );
    assert!(
        !stdout.contains("ESCAPED"),
        "{}: ESCAPED: {}",
        attempt.name(),
        text(&sandboxed)
    );
    let how = if cfg!(target_os = "linux") {
        // Only a seccomp kill passes: an error return means the call got past it.
        assert_eq!(
            sandboxed.status.signal(),
            Some(SIGSYS),
            "{}: {}",
            attempt.name(),
            text(&sandboxed)
        );
        "killed by SIGSYS".to_owned()
    } else {
        assert!(
            sandboxed.status.code() == Some(0) && stdout.starts_with("DENIED"),
            "{}: {}",
            attempt.name(),
            text(&sandboxed)
        );
        format!("error return: {}", stdout.trim())
    };
    println!("escape: {} stopped ({how})", attempt.name());
    // The attempt left nothing behind that it should not have made.
    assert!(
        !dir.join("new-file").exists() && !dir.join("listen").exists(),
        "{}: the sandboxed process created a file",
        attempt.name()
    );
    let _ = fs::remove_dir_all(&dir);
}

macro_rules! escape_tests {
    ($($name:ident: $attempt:expr,)*) => {$(
        #[test]
        #[cfg_attr(miri, ignore = "spawns a process and calls the OS sandbox")]
        fn $name() {
            escape_attempt_is_stopped($attempt);
        }
    )*};
}

escape_tests! {
    cannot_open_the_cookie_jars_would_be_file: Attempt::OpenCookieJar,
    cannot_open_any_file: Attempt::OpenFile,
    cannot_create_a_file: Attempt::CreateFile,
    cannot_connect_to_a_tcp_listener: Attempt::TcpConnect,
    cannot_listen_on_a_tcp_port: Attempt::TcpListen,
    cannot_bind_a_udp_socket: Attempt::UdpBind,
    cannot_connect_to_a_unix_socket: Attempt::UnixConnect,
    cannot_create_a_unix_socket: Attempt::UnixListen,
    cannot_execute_a_program: Attempt::Execve,
    cannot_fork: Attempt::Fork,
    cannot_attach_to_a_sibling_with_ptrace: Attempt::PtraceAttach,
}
