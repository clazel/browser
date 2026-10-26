//! The host shell with stub renderers (`/bin/sh` scripts that speak raw
//! frames) and with the real `clazel-renderer`. Every test spawns processes,
//! so none runs under Miri.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_ipc::frame::codec::payload_length;
use clazel_ipc::message::codec::{Msg, decode_framed};

const LONG: Duration = Duration::from_secs(20);

/// A host whose renderers run `script` with `$ID` set to their id.
fn stub(script: String) -> Host {
    Host::new(move |id| {
        let mut c = Command::new("/bin/sh");
        c.arg("-c")
            .arg(&script)
            .env("ID", id.to_string())
            .env("OUT", env!("CARGO_TARGET_TMPDIR"));
        c
    })
}

/// A frame of `payload`, as the octal escapes `printf` reads.
fn frame_octal(payload: &[u8]) -> String {
    let len = u32::try_from(payload.len()).unwrap_or(u32::MAX);
    len.to_be_bytes()
        .iter()
        .chain(payload)
        .map(|b| format!("\\{b:03o}"))
        .collect()
}

fn decode_all(mut bytes: &[u8]) -> Vec<Msg> {
    let mut out = Vec::new();
    while let Some((header, _)) = bytes.split_at_checked(4) {
        let Some(len) = payload_length(header) else {
            break;
        };
        let Some((frame, rest)) = bytes.split_at_checked(len.saturating_add(4)) else {
            break;
        };
        out.extend(decode_framed(frame));
        bytes = rest;
    }
    out
}

/// Pump the host until `f` has a value.
fn wait_for<T>(mut f: impl FnMut() -> Option<T>, host: &mut Host) -> T {
    let end = Instant::now()
        .checked_add(LONG)
        .unwrap_or_else(Instant::now);
    loop {
        if let Some(v) = f() {
            return v;
        }
        assert!(Instant::now() < end, "timed out; host log: {:#?}", host.log);
        host.pump(Duration::from_millis(20));
    }
}

fn has(host: &Host, needle: &str) -> bool {
    host.log.iter().any(|l| l.contains(needle))
}

/// After the renderer of tab 0 is gone from the kernel, a navigation of that
/// tab does nothing; if the kernel still had it, it would spawn a renderer.
fn kernel_forgot_tab_zero(host: &mut Host) {
    host.navigate_tab(0, "https://other.example/", "");
    assert_eq!(
        host.live(),
        0,
        "the kernel still has renderer 0: {:#?}",
        host.log
    );
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes")]
fn an_oversized_frame_is_refused_and_becomes_renderer_exited() {
    // The header announces 2^32 - 1 bytes, over MAX_FRAME (1 MiB).
    let mut host = stub(r"printf '\377\377\377\377'; exec sleep 30".to_owned());
    host.open_tab("https://a.example/", "");
    assert_eq!(host.live(), 1);
    assert!(host.run(LONG), "{:#?}", host.log);
    assert!(
        has(
            &host,
            "renderer 0 exited: sent a frame over MAX_FRAME (announced 4294967295 bytes)"
        ),
        "{:#?}",
        host.log
    );
    kernel_forgot_tab_zero(&mut host);
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes")]
fn a_closed_socket_becomes_renderer_exited() {
    let mut host = stub("exit 0".to_owned());
    host.open_tab("https://a.example/", "");
    assert!(host.run(LONG), "{:#?}", host.log);
    // Which the host notices first is a race: if the stub has exited before
    // the host sends its commit, the write fails ("cannot write", as on
    // Linux CI); otherwise the read sees the socket close. Either is a
    // correct report that the renderer has gone.
    assert!(
        has(
            &host,
            "renderer 0 exited: closed its socket; exit status: 0"
        ) || has(&host, "renderer 0 exited: cannot write; exit status: 0"),
        "{:#?}",
        host.log
    );
    kernel_forgot_tab_zero(&mut host);
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes")]
fn a_kernel_only_message_gets_the_renderer_killed() {
    // CookieValue (tag 102) is a message only the kernel may send.
    let mut host = stub(format!(
        "printf '{}'; exec sleep 30",
        frame_octal(&[0x82, 0x18, 0x66, 0x60])
    ));
    host.open_tab("https://a.example/", "");
    assert!(host.run(LONG), "{:#?}", host.log);
    assert!(
        has(&host, "renderer 0 exited: killed by the kernel"),
        "{:#?}",
        host.log
    );
    kernel_forgot_tab_zero(&mut host);
}

fn received(id: u64) -> PathBuf {
    Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("received-{id}"))
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes")]
fn the_renderer_id_comes_from_the_socket_and_replies_go_to_the_sender() {
    // Renderer 0 sends CookieGet (a frame of [1], with no id in it); both
    // stubs write everything they receive to a file named after $ID.
    let cookie_get = frame_octal(&[0x81, 0x01]);
    let _ = fs::remove_file(received(0));
    let _ = fs::remove_file(received(1));
    let mut host = stub(format!(
        "if [ \"$ID\" = 0 ]; then printf '{cookie_get}'; fi; exec cat > \"$OUT/received-$ID\""
    ));
    host.open_tab("https://a.example/", "");
    host.open_tab("https://b.example/", "");
    assert_eq!(host.live(), 2);
    let got = wait_for(
        || Some(decode_all(&fs::read(received(0)).ok()?)).filter(|m| m.len() >= 2),
        &mut host,
    );
    assert!(
        matches!(got.as_slice(), [Msg::Commit { .. }, Msg::CookieValue { cookie_string }] if cookie_string.is_empty()),
        "{got:?}"
    );
    // Renderer 1 sent nothing and got only its own Commit.
    wait_for(|| received(1).exists().then_some(()), &mut host);
    host.pump(Duration::from_millis(200));
    let other = decode_all(&fs::read(received(1)).unwrap_or_default());
    assert!(
        matches!(other.as_slice(), [Msg::Commit { .. }]),
        "{other:?}"
    );
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes")]
fn a_cross_origin_navigation_is_kill_spawn_commit_and_a_same_origin_one_is_a_commit() {
    let mut host = stub("exec cat > /dev/null".to_owned());
    host.open_tab("https://a.example/", "");
    host.navigate_tab(0, "https://a.example/other", "");
    assert_eq!(host.live(), 1);
    assert!(!has(&host, "killed"), "{:#?}", host.log);
    host.log.clear();
    host.navigate_tab(0, "https://b.example/", "cookie-get");
    assert_eq!(host.live(), 1);
    let order: Vec<&str> = host.log.iter().map(String::as_str).collect();
    // The kernel asks for the page, the stand-in network answers with the
    // script, and the answer commits: the old renderer is killed and a new one
    // gets the Commit.
    assert!(
        matches!(order.as_slice(),
            [net, kill, commit] if net.starts_with("network (stand-in): tab 0 <- \"https://b.example/\"")
                && kill.starts_with("renderer 0 exited: killed by the kernel")
                && commit.starts_with("renderer 1 <- commit \"https://b.example/\"")),
        "{order:#?}"
    );
}

/// `clazel-renderer` next to the test's own deps directory, built if needed.
fn real_renderer() -> PathBuf {
    let exe = std::env::current_exe().unwrap_or_default();
    let path = exe
        .parent()
        .and_then(Path::parent)
        .map(|d| d.join("clazel-renderer"))
        .unwrap_or_default();
    if !path.exists() {
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
        let built = Command::new(cargo)
            .args(["build", "-p", "clazel-renderer"])
            .status();
        assert!(
            built.is_ok_and(|s| s.success()),
            "cannot build clazel-renderer"
        );
    }
    path
}

fn real_host() -> Host {
    let renderer = real_renderer();
    Host::new(move |_| Command::new(&renderer))
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn a_sandboxed_renderer_runs_a_script_end_to_end() {
    let mut host = real_host();
    let script = "cookie-set a=1; Path=/\ncookie-get\nstorage-set k v\nstorage-get k\nstorage-length\nstorage-key 0\nstorage-remove k\nstorage-key 0";
    host.open_tab("https://example.com/", script);
    assert!(host.run(LONG), "{:#?}", host.log);
    let log = host.log.join("\n");
    // On Linux a kernel or container that refuses a sandbox layer stops the
    // renderer before it reads a byte (fail closed), and the host reports
    // which layer; that is the one other outcome accepted. On macOS the
    // sandbox must work.
    if cfg!(target_os = "linux") && has(&host, "stderr: clazel-renderer: sandbox layer") {
        assert!(log.contains("exit status: 71"), "{log}");
        return;
    }
    for want in [
        "renderer 0 <- commit \"https://example.com/\"",
        "renderer 0 -> document.cookie = \"a=1; Path=/\"",
        "renderer 0 <- result \"a=1\"",
        "renderer 0 -> localStorage.setItem(\"k\", \"v\")",
        "renderer 0 <- result \"v\"",
        "renderer 0 <- result \"k\"",
        "renderer 0 <- result null",
        "renderer 0 exited: closed its socket; exit status: 0",
    ] {
        assert!(log.contains(want), "missing {want:?} in:\n{log}");
    }
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn a_bad_script_is_reported_with_the_renderers_stderr() {
    let mut host = real_host();
    host.open_tab("https://example.com/", "cookie-get\nfly");
    assert!(host.run(LONG), "{:#?}", host.log);
    let log = host.log.join("\n");
    let sandbox_refused = cfg!(target_os = "linux")
        && log.contains("exit status: 71; stderr: clazel-renderer: sandbox layer");
    assert!(
        sandbox_refused
            || log.contains(
                "exit status: 64; stderr: clazel-renderer: script line 2: unknown operation"
            ),
        "{log}"
    );
}
