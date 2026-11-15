//! Item 5.26: a page whose GPU process is killed, again and again. The crash policy
//! (5.17c: restart, then software, then a notice) is not in the kernel yet, so this
//! records what happens today rather than what the item asks for, and checks only
//! that the host stays up and says what happened:
//!
//! 1. the real renderer and GPU process paint a page;
//! 2. the GPU process is killed (`kill -9`, its pid recorded by `/bin/sh`);
//! 3. the user scrolls, so the renderer writes a new list to the dead process's
//!    list socket;
//! 4. steps 2 and 3 repeat while there is a GPU process to kill.
//!
//! What it prints is the record. macOS on Apple silicon only; without a Metal
//! device it skips, except under CI.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

mod support;

#[path = "support/server.rs"]
mod server;

use std::path::PathBuf;
use std::process::Command;
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_kernel::exec::records::{EventRecord, OutputRecord};
use server::{Reply, Request, serve};

const DEJAVU: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf"
);

#[test]
#[cfg_attr(miri, ignore)]
fn a_gpu_process_killed_again_and_again() {
    if let Err(e) = clazel_gpu::metal::MetalBackend::new() {
        eprintln!("gpu_killed: skipped: no Metal device ({})", e.what);
        assert!(std::env::var_os("CI").is_none(), "no Metal device under CI");
        return;
    }
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let built = Command::new(cargo)
        .args([
            "build",
            "--quiet",
            "-p",
            "clazel-gpu",
            "-p",
            "clazel-renderer",
        ])
        .status();
    assert!(built.is_ok_and(|s| s.success()));
    let renderer = support::binary("clazel-renderer");
    let gpu = renderer.with_file_name("clazel-gpu");
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("gpu-killed-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let server = serve(|r: &Request| {
        assert_eq!(r.path, "/");
        Reply {
            head: "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n".to_owned(),
            piece:
                b"<!doctype html><title>t</title><div style='height:5000px;background:#00f'>x</div>"
                    .to_vec(),
            times: 1,
        }
    });
    let piddir = dir.clone();
    let mut host = Host::new(move |_| {
        let mut c = Command::new(&renderer);
        c.args(["--font", DEJAVU]);
        c
    })
    .with_gpu(move |id| {
        let mut c = Command::new("/bin/sh");
        c.arg("-c")
            .arg("echo $$ > \"$PIDDIR/gpu-$ID.pid\"; exec \"$0\" \"$@\"")
            .arg(&gpu)
            .env("PIDDIR", &piddir)
            .env("ID", id.to_string());
        c
    });
    host.route = Some(server.addr);
    let tab = host.open("http://hostile.test/");
    host.event(EventRecord::Resize {
        tab,
        width: 200,
        height: 150,
        scale: 1,
    });
    let pump = |host: &mut Host, d: Duration| {
        let start = Instant::now();
        let mut paints = 0;
        while start.elapsed() < d {
            host.pump(Duration::from_millis(20));
            paints += host
                .shown
                .iter()
                .filter(|o| matches!(o, OutputRecord::Paint { .. }))
                .count();
            host.shown.clear();
        }
        paints
    };
    let first = pump(&mut host, Duration::from_secs(5));
    assert!(first >= 1, "no first paint: {:#?}", host.log);
    eprintln!("gpu_killed: painted ({first} Paint)");
    let mut killed = 0;
    for round in 1..=3 {
        let pids: Vec<String> = std::fs::read_dir(&dir)
            .into_iter()
            .flatten()
            .flatten()
            .filter_map(|e| std::fs::read_to_string(e.path()).ok())
            .map(|p| p.trim().to_owned())
            .collect();
        // Alive and not a zombie: `kill -0` succeeds on a zombie too.
        let alive: Vec<&String> = pids
            .iter()
            .filter(|p| {
                Command::new("ps")
                    .args(["-o", "stat=", "-p", p])
                    .output()
                    .is_ok_and(|o| {
                        o.status.success()
                            && !String::from_utf8_lossy(&o.stdout).trim().starts_with('Z')
                    })
            })
            .collect();
        let Some(pid) = alive.first() else {
            eprintln!(
                "gpu_killed: round {round}: no GPU process left to kill (nothing restarts one)"
            );
            break;
        };
        assert!(
            Command::new("kill")
                .args(["-9", pid])
                .status()
                .is_ok_and(|s| s.success())
        );
        killed += 1;
        host.event(EventRecord::Input {
            tab,
            kind: 1,
            x: 0,
            y: 0,
            negative: false,
            delta: 100,
            key: 0,
        });
        let paints = pump(&mut host, Duration::from_secs(3));
        let renderer_alive = host.state.renderers.iter().any(|r| r.tab == tab);
        eprintln!(
            "gpu_killed: round {round}: killed GPU process {pid}; then {paints} Paint; the tab's renderer {}",
            if renderer_alive {
                "is still in the kernel"
            } else {
                "is gone from the kernel"
            }
        );
    }
    for line in host
        .log
        .iter()
        .filter(|l| l.contains("exited") || l.contains("closed"))
    {
        eprintln!("gpu_killed: host: {line}");
    }
    assert!(killed >= 1);
    assert!(server.seen.lock().is_ok_and(|s| !s.is_empty()));
    drop(host);
    let _ = std::fs::remove_dir_all(&dir);
}
