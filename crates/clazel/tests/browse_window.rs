//! Phase-5.md item 5.23: the frame of `browse_gpu.rs` (a hand-built list drawn by
//! the real GPU process, through the kernel's `Paint`) shown in a real window, with
//! the address bar strip drawn from the `Paint`'s URL and the title bar set after
//! it. No pixel is read back from the screen (that needs the Screen Recording
//! permission); what is checked is that every step is accepted and the window
//! closes.
//!
//! Its own `main` (`harness = false`): AppKit needs the main thread. Skipped,
//! saying so on stderr, under Miri, off macOS on Apple silicon, without a window
//! server session, and without a Metal device (a failure under CI). The window is
//! small, takes no focus and closes within a second; the host ends both processes
//! when it is dropped, and a watchdog ends the test after 120 s.
//!
//! With `CLAZEL_WINDOW_TAKE_FOCUS=1` it also runs the real thing once: `clazel
//! browse URL` (which activates its window, so it takes focus, hence opt-in)
//! against a page served here, with the real renderer and GPU process, until it
//! logs that the window shows the page's `Paint`; then it ends `clazel`, whose
//! renderer and GPU process end with their sockets.

use std::process::ExitCode;

fn main() -> ExitCode {
    if cfg!(miri) {
        eprintln!("clazel browse_window: skipped: Miri cannot start processes");
        return ExitCode::SUCCESS;
    }
    run()
}

#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
fn run() -> ExitCode {
    eprintln!("clazel browse_window: skipped: not macOS on Apple silicon");
    ExitCode::SUCCESS
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn run() -> ExitCode {
    mac::run()
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "support/gpu.rs"]
mod gpu;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "../cli/strip.rs"]
mod strip;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod mac {
    use std::process::ExitCode;
    use std::time::{Duration, Instant};

    use clazel_window::{Event, Window, has_window_server};

    use crate::gpu::{close, fixture, host, metal, open, painted, reference};
    use crate::strip::{self, Contents, STRIP_POINTS};

    const WATCHDOG: Duration = Duration::from_secs(120);

    pub fn run() -> ExitCode {
        if let Err(why) = metal() {
            eprintln!("clazel browse_window: skipped: no Metal device ({why})");
            return if std::env::var_os("CI").is_some() {
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            };
        }
        if !has_window_server() {
            eprintln!("clazel browse_window: skipped: no window server session");
            return ExitCode::SUCCESS;
        }
        std::thread::spawn(|| {
            std::thread::sleep(WATCHDOG);
            eprintln!("clazel browse_window: FAILED: still running after {WATCHDOG:?}");
            std::process::exit(1);
        });
        let started = Instant::now();
        a_paint_is_shown_in_the_window();
        eprintln!("clazel browse_window: ran in {:?}", started.elapsed());
        if std::env::var_os("CLAZEL_WINDOW_TAKE_FOCUS").is_some_and(|v| v == "1") {
            let started = Instant::now();
            browse_shows_a_real_page();
            eprintln!(
                "clazel browse_window: clazel browse showed a page in {:?}",
                started.elapsed()
            );
        } else {
            eprintln!(
                "clazel browse_window: clazel browse not run: it takes focus \
                 (set CLAZEL_WINDOW_TAKE_FOCUS=1 to)"
            );
        }
        ExitCode::SUCCESS
    }

    /// Serve `page` to every request on a loopback port; its address.
    fn serve(page: &'static str) -> Option<std::net::SocketAddr> {
        use std::io::{Read, Write};
        let listener = std::net::TcpListener::bind("127.0.0.1:0").ok()?;
        let addr = listener.local_addr().ok()?;
        std::thread::spawn(move || {
            for mut s in listener.incoming().flatten() {
                let mut head = [0u8; 4096];
                let _ = s.read(&mut head);
                let reply = format!(
                    "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nContent-Length: {}\r\n\
                     Connection: close\r\n\r\n{page}",
                    page.len()
                );
                let _ = s.write_all(reply.as_bytes());
            }
        });
        Some(addr)
    }

    fn browse_shows_a_real_page() {
        use std::io::{BufRead, BufReader};
        use std::process::{Command, Stdio};
        let f = fixture("browse-window-real");
        assert!(f.is_ok(), "{:?}", f.as_ref().err());
        let Ok(f) = f else { return };
        let addr = serve(
            "<!doctype html><title>Real</title><body style='background:#2050c0'>\
             <p style='color:#ffffff'>Hello from the pipeline</p></body>",
        );
        assert!(addr.is_some());
        let Some(addr) = addr else { return };
        let child = Command::new(&f.clazel)
            .arg(format!("http://{addr}/"))
            .env("CLAZEL_RENDERER", &f.renderer)
            .env("CLAZEL_GPU", &f.gpu)
            .stderr(Stdio::piped())
            .spawn();
        assert!(child.is_ok(), "{child:?}");
        let Ok(mut child) = child else { return };
        let (tx, rx) = std::sync::mpsc::channel();
        if let Some(err) = child.stderr.take() {
            std::thread::spawn(move || {
                for line in BufReader::new(err).lines().map_while(Result::ok) {
                    if tx.send(line).is_err() {
                        break;
                    }
                }
            });
        }
        let end = Instant::now().checked_add(Duration::from_secs(30));
        let mut log = Vec::new();
        let mut shown = false;
        while !shown && end.is_some_and(|e| Instant::now() < e) {
            if let Ok(line) = rx.recv_timeout(Duration::from_millis(100)) {
                shown = line.starts_with("clazel: showing http://");
                log.push(line);
            }
        }
        let _ = child.kill();
        let _ = child.wait();
        assert!(
            shown,
            "clazel browse never showed the page:\n{}",
            log.join("\n")
        );
    }

    fn a_paint_is_shown_in_the_window() {
        let f = fixture("browse-window");
        assert!(f.is_ok(), "{:?}", f.as_ref().err());
        let Ok(f) = f else { return };
        let mut host = host(&f);
        let tab = open(&mut host, "http://window.test/", (80, 60));
        let got = painted(&mut host, tab);
        assert!(
            got.is_some(),
            "no Paint with its pixels; the host's log:\n{}",
            host.log.join("\n")
        );
        let Some(p) = got else { return };
        drop(host);
        assert_eq!((p.buffer, p.size), (0, (80, 60)));
        assert!(f.clazel.exists() && f.renderer.exists());
        assert!(
            reference(80, 60)
                .as_deref()
                .is_some_and(|w| close(&p.frame.pixels, w))
        );

        let opened = Window::open_sized("clazel browse_window", 120.0, 100.0);
        assert!(opened.is_ok(), "{opened:?}");
        let Ok(mut window) = opened else { return };
        let (width, _) = window.size();
        let backing = f64::from(window.dpi().unwrap_or(96)) / 96.0;
        let strip_px = (STRIP_POINTS * backing).round() as u32;
        // Premultiplied RGBA over white, as `cli/window.rs` shows it.
        let pixels: Vec<u32> = p
            .frame
            .pixels
            .as_chunks::<4>()
            .0
            .iter()
            .map(|[r, g, b, a]| {
                [r, g, b]
                    .iter()
                    .fold(0u32, |v, c| v << 8 | u32::from(c.saturating_add(!a)))
            })
            .collect();
        let shown = window.show_page_pixels(&pixels, (0, strip_px), 80, 60);
        assert!(shown.is_ok(), "{shown:?}");
        let font = strip::system_font();
        let what = Contents {
            text: &p.url,
            editing: false,
            committed: true,
            can_go_back: false,
        };
        let bar = strip::render(font.as_deref(), width, strip_px, backing, &what);
        assert!(window.draw(&bar, width, strip_px).is_ok());
        // The back button is on the strip this window draws, at its left.
        let (x0, y0, x1, y1) = strip::back_button(strip_px, backing);
        assert!(strip::on_back_button(x0, y0, strip_px, backing));
        assert!(x1 <= i64::from(width) && y1 <= i64::from(strip_px));
        assert!(
            window
                .set_title(&format!("{} — a hand-built list", p.url))
                .is_ok()
        );
        let shown = Instant::now();
        while shown.elapsed() < Duration::from_millis(300) {
            assert_ne!(
                window.next_event(Duration::from_millis(50)),
                Some(Event::Closed)
            );
        }
        window.close();
        let closing = Instant::now();
        let mut closed = false;
        while !closed && closing.elapsed() < Duration::from_secs(5) {
            closed = window.next_event(Duration::from_millis(50)) == Some(Event::Closed);
        }
        assert!(closed, "the window did not close");
    }
}
