//! Item 5.21a: the GPU process's sandbox, entered for real on macOS on Apple
//! silicon, by this test binary run again as a child (`CLAZEL_GPU_SANDBOX_CHILD`).
//!
//! What it checks, each in a fresh child:
//!
//! 1. **Drawing works sandboxed.** A child starts as the GPU process does
//!    (`clazel_gpu::sandbox::start_metal`: the Metal device, queue and pipeline,
//!    then the Seatbelt profile) and draws every scene, reading the pixels back and
//!    comparing them with the software reference (each channel within one level, as
//!    `tests/metal.rs`). An unsandboxed child does the same first, as the control.
//! 2. **The order is what makes the profile work.** A child that enters the same
//!    profile *before* making the device must fail to make it: the profile has no
//!    rule, and only the warm-up lets Metal run inside it.
//! 3. **What the sandboxed process cannot do** (the escape attempts of item 5.26,
//!    the ones this item lists): read a file, create a file, list the home
//!    directory, connect to a loopback TCP port, bind a UDP socket, connect to a Unix
//!    socket, reach the WindowServer, fork, and start a program. Each runs first
//!    unsandboxed against the same target and must succeed there, so a denial is the
//!    sandbox's and not a wrong path. A WindowServer control that fails (no GUI
//!    session, as over SSH) is reported and not judged.
//!
//! Nothing here takes window focus or opens a window. Every child is waited for,
//! with a two-minute limit after which it is killed; the listeners are closed and
//! the scratch directory removed at the end, so nothing is left running.
//!
//! A missing Metal device is a skip on a developer's machine and a failure under CI
//! (`CI` set), as in `tests/metal.rs`. Under Miri the test does nothing (it starts
//! processes and calls the OS). It is `harness = false` so that the child runs on
//! the main thread with no test harness around it.

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod mac {
    use std::io::Read;
    use std::net::{TcpListener, TcpStream, UdpSocket};
    use std::os::unix::net::{UnixListener, UnixStream};
    use std::path::{Path, PathBuf};
    use std::process::{Command, ExitCode, Output, Stdio};
    use std::time::{Duration, Instant};

    use clazel_displaylist::exec::encode_list;
    use clazel_gpu::metal::MetalBackend;
    use clazel_gpu::reference::{self, Masks};
    use clazel_gpu::start::Launch;
    use clazel_gpu::{Backend, Gpu, Viewport, sandbox, scenes};

    const CHILD: &str = "CLAZEL_GPU_SANDBOX_CHILD";
    const LIMIT: Duration = Duration::from_secs(120);

    /// The attempts, by name.
    const ATTEMPTS: &[(&str, &str)] = &[
        ("read-file", "read a file the test wrote"),
        ("create-file", "create a file in the test's directory"),
        ("list-home", "list the home directory"),
        ("tcp-connect", "connect to a loopback TCP port"),
        ("udp-bind", "bind a UDP socket"),
        ("unix-connect", "connect to a Unix socket"),
        ("window-server", "reach the WindowServer"),
        ("fork", "fork"),
        ("exec", "start /usr/bin/true"),
    ];

    /// Draw every scene and compare it with the reference.
    fn draw_all(backend: MetalBackend) -> Result<usize, String> {
        let mut backend = Some(backend);
        let mut lists: usize = 0;
        for scene in scenes::all() {
            let viewport = Viewport::new(scene.width, scene.height).ok_or("viewport")?;
            let b = backend.take().ok_or("backend")?;
            let (mut gpu, _) = Gpu::start(b, Launch::HARDWARE).map_err(|e| format!("{e:?}"))?;
            let mut masks = Masks::default();
            for (n, list) in scene.lists.iter().enumerate() {
                let bytes = encode_list(list).ok_or("encode")?;
                gpu.draw(&bytes, viewport)
                    .map_err(|e| format!("{} list {n}: {e}", scene.name))?;
                let mut got = Vec::new();
                gpu.backend()
                    .read_pixels(&mut got)
                    .map_err(|e| format!("{e:?}"))?;
                let want = reference::draw(list, viewport, &mut masks).ok_or("reference")?;
                let worst = got
                    .iter()
                    .zip(&want)
                    .map(|(a, b)| a.abs_diff(*b))
                    .max()
                    .unwrap_or(0);
                if got.len() != want.len() || worst > 1 {
                    return Err(format!(
                        "{} list {n}: differs from the reference by {worst}",
                        scene.name
                    ));
                }
                lists = lists.checked_add(1).ok_or("count")?;
            }
            backend = Some(gpu.into_backend());
        }
        Ok(lists)
    }

    /// One attempt; `Ok` means the OS allowed it.
    fn attempt(name: &str, target: &str) -> Result<(), String> {
        let e = |e: std::io::Error| e.to_string();
        match name {
            "read-file" => {
                let mut s = String::new();
                std::fs::File::open(target)
                    .and_then(|mut f| f.read_to_string(&mut s))
                    .map(|_| ())
                    .map_err(e)
            }
            "create-file" => std::fs::File::create(Path::new(target).join("created"))
                .map(|_| ())
                .map_err(e),
            "list-home" => std::fs::read_dir(target).map(|_| ()).map_err(e),
            "tcp-connect" => TcpStream::connect(target).map(|_| ()).map_err(e),
            "udp-bind" => UdpSocket::bind("127.0.0.1:0").map(|_| ()).map_err(e),
            "unix-connect" => UnixStream::connect(target).map(|_| ()).map_err(e),
            "window-server" => {
                if clazel_sys::macos::window::has_window_server() {
                    Ok(())
                } else {
                    Err("no window server session".to_owned())
                }
            }
            "fork" => clazel_sys::macos::attempt_fork().map_err(|e| e.to_string()),
            "exec" => Command::new("/usr/bin/true")
                .status()
                .map_err(e)
                .and_then(|s| {
                    if s.success() {
                        Ok(())
                    } else {
                        Err(format!("{s}"))
                    }
                }),
            _ => Err(format!("unknown attempt {name}")),
        }
    }

    /// The child: `mode` and its arguments; prints one result line.
    fn child(mode: &str, args: &[String]) {
        let arg = |i: usize| args.get(i).map_or("", String::as_str);
        let line = match mode {
            "draw-plain" => match MetalBackend::new() {
                Ok(b) => match draw_all(b) {
                    Ok(n) => format!("DREW {n}"),
                    Err(e) => format!("FAILED draw: {e}"),
                },
                Err(e) => format!("NO-DEVICE {e:?}"),
            },
            "draw-sandboxed" => match sandbox::start_metal() {
                Ok(b) => match draw_all(b) {
                    Ok(n) => format!("DREW {n}"),
                    Err(e) => format!("FAILED draw: {e}"),
                },
                Err(e) => format!("FAILED start: {e}"),
            },
            "enter-first" => {
                let profile = clazel_sandbox::seatbelt::gpu_profile();
                match clazel_sys::macos::sandbox_init_profile(&profile) {
                    Err(e) => format!("FAILED enter: {e}"),
                    Ok(()) => match MetalBackend::new() {
                        Ok(_) => "DEVICE-MADE".to_owned(),
                        Err(e) => format!("NO-DEVICE {}", e.what),
                    },
                }
            }
            "attempt" => {
                let sandboxed = arg(0) == "sandboxed";
                let started = if sandboxed {
                    sandbox::start_metal()
                        .map(|_| ())
                        .map_err(|e| e.to_string())
                } else {
                    MetalBackend::new()
                        .map(|_| ())
                        .map_err(|e| format!("{e:?}"))
                };
                match started {
                    Err(e) => format!("FAILED start: {e}"),
                    Ok(()) => match attempt(arg(1), arg(2)) {
                        Ok(()) => "ALLOWED".to_owned(),
                        Err(e) => format!("DENIED {e}"),
                    },
                }
            }
            _ => format!("FAILED unknown mode {mode}"),
        };
        println!("{line}");
    }

    /// Run this binary as a child and return its last stdout line, killing it
    /// after [`LIMIT`].
    fn run(mode: &str, args: &[&str]) -> Result<String, String> {
        let exe = std::env::current_exe().map_err(|e| e.to_string())?;
        let mut c = Command::new(exe)
            .env(CHILD, mode)
            .args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| e.to_string())?;
        let start = Instant::now();
        loop {
            match c.try_wait().map_err(|e| e.to_string())? {
                Some(_) => break,
                None if start.elapsed() > LIMIT => {
                    let _ = c.kill();
                    let _ = c.wait();
                    return Err(format!("{mode} {args:?}: killed after {LIMIT:?}"));
                }
                None => std::thread::sleep(Duration::from_millis(50)),
            }
        }
        let out: Output = c.wait_with_output().map_err(|e| e.to_string())?;
        let text = String::from_utf8_lossy(&out.stdout);
        text.lines().last().map(str::to_owned).ok_or_else(|| {
            format!(
                "{mode} {args:?}: no result ({}; stderr {:?})",
                out.status,
                String::from_utf8_lossy(&out.stderr)
            )
        })
    }

    /// The scratch directory, removed on drop.
    struct Scratch(PathBuf);

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn check() -> Result<String, String> {
        let mut failures = Vec::new();
        let mut report = Vec::new();

        // 1. Drawing, unsandboxed then sandboxed.
        let plain = run("draw-plain", &[])?;
        if plain.starts_with("NO-DEVICE") {
            if std::env::var_os("CI").is_some() {
                return Err(format!(
                    "no usable Metal device under CI ({plain}); a missing device is a skip \
                     only on a developer's machine"
                ));
            }
            return Ok(format!("skipped: no usable Metal device ({plain})"));
        }
        if !plain.starts_with("DREW ") {
            return Err(format!("the unsandboxed control did not draw: {plain}"));
        }
        let sandboxed = run("draw-sandboxed", &[])?;
        report.push(format!(
            "draw, unsandboxed: {plain}; sandboxed: {sandboxed}"
        ));
        if sandboxed != plain {
            failures.push(format!("sandboxed drawing: {sandboxed} (control: {plain})"));
        }

        // 2. Entering first leaves Metal no device.
        let first = run("enter-first", &[])?;
        report.push(format!("entering before the device: {first}"));
        if !first.starts_with("NO-DEVICE") {
            failures.push(format!("entering before the device: {first}"));
        }

        // 3. The attempts.
        let dir = Scratch(
            std::env::temp_dir().join(format!("clazel-gpu-sandbox-{}", std::process::id())),
        );
        std::fs::create_dir_all(&dir.0).map_err(|e| e.to_string())?;
        let file = dir.0.join("secret");
        std::fs::write(&file, "not for the GPU process").map_err(|e| e.to_string())?;
        let tcp = TcpListener::bind("127.0.0.1:0").map_err(|e| e.to_string())?;
        let tcp_addr = tcp.local_addr().map_err(|e| e.to_string())?.to_string();
        let sock = dir.0.join("s");
        let unix = UnixListener::bind(&sock).map_err(|e| e.to_string())?;
        let home = std::env::var("HOME").unwrap_or_else(|_| "/Users".to_owned());
        let path = |p: &Path| p.to_string_lossy().into_owned();
        for (name, what) in ATTEMPTS {
            let target = match *name {
                "read-file" => path(&file),
                "create-file" => path(&dir.0),
                "list-home" => home.clone(),
                "tcp-connect" => tcp_addr.clone(),
                "unix-connect" => path(&sock),
                _ => String::new(),
            };
            let control = run("attempt", &["plain", name, &target])?;
            let inside = run("attempt", &["sandboxed", name, &target])?;
            report.push(format!("{what}: unsandboxed {control}; sandboxed {inside}"));
            if control != "ALLOWED" {
                if *name == "window-server" {
                    report.push("  (no WindowServer session: not judged)".to_owned());
                    continue;
                }
                failures.push(format!("{what}: the unsandboxed control failed: {control}"));
            }
            if !inside.starts_with("DENIED") {
                failures.push(format!("{what}: sandboxed: {inside}"));
            }
        }
        drop(tcp);
        drop(unix);
        if failures.is_empty() {
            Ok(report.join("\n"))
        } else {
            Err(format!(
                "{}\nFAILED:\n{}",
                report.join("\n"),
                failures.join("\n")
            ))
        }
    }

    pub fn main() -> ExitCode {
        if let Ok(mode) = std::env::var(CHILD) {
            let args: Vec<String> = std::env::args().skip(1).collect();
            child(&mode, &args);
            return ExitCode::SUCCESS;
        }
        if cfg!(miri) {
            println!("sandbox_macos: skipped under Miri (starts processes and calls the OS)");
            return ExitCode::SUCCESS;
        }
        match check() {
            Ok(report) => {
                println!("sandbox_macos:\n{report}");
                ExitCode::SUCCESS
            }
            Err(why) => {
                eprintln!("sandbox_macos:\n{why}");
                ExitCode::FAILURE
            }
        }
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn main() -> std::process::ExitCode {
    mac::main()
}

#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
fn main() {
    println!("sandbox_macos: nothing to run (macOS on Apple silicon only)");
}
