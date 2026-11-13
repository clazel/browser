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
        ExitCode::SUCCESS
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
        assert!(f.clazel.exists());
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
        };
        let bar = strip::render(font.as_deref(), width, strip_px, backing, &what);
        assert!(window.draw(&bar, width, strip_px).is_ok());
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
