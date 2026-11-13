//! Open a real window on macOS, draw in it, read its events and close it
//! (phase-5.md item 5.21). A small window appears for under a second, behind the
//! active application, without a Dock icon and without taking the keyboard, unless
//! `CLAZEL_WINDOW_TAKE_FOCUS=1` asks it to also test `Window::activate`.
//!
//! This is its own `main` (`harness = false` in Cargo.toml) because AppKit may only
//! be used on the main thread, and the test harness runs tests on others.
//!
//! Skipped, saying why on stderr: under Miri (no foreign calls), on any target but
//! macOS on Apple silicon, and without a window server session (an SSH login or a
//! headless machine), where AppKit would end the process; the item asks for the
//! last skip. CI's macOS runner is a virtual machine; whether it has a session
//! decides whether the test runs there, and the line on stderr says which.

use std::process::ExitCode;

fn main() -> ExitCode {
    if cfg!(miri) {
        eprintln!("clazel-window smoke_macos: skipped: Miri cannot make foreign calls");
        return ExitCode::SUCCESS;
    }
    run()
}

#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
fn run() -> ExitCode {
    eprintln!("clazel-window smoke_macos: skipped: not macOS on Apple silicon");
    ExitCode::SUCCESS
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn run() -> ExitCode {
    mac::run()
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod mac {
    use std::process::ExitCode;
    use std::time::{Duration, Instant};

    use clazel_window::pattern::test_pattern;
    use clazel_window::{Error, Event, Surface, Window, has_window_server};

    /// The whole test ends within this, or the process exits, closing the window.
    const WATCHDOG: Duration = Duration::from_secs(20);

    pub fn run() -> ExitCode {
        let ci = std::env::var_os("CI").is_some();
        if !has_window_server() {
            eprintln!(
                "clazel-window smoke_macos: skipped: no window server session{}",
                if ci { " (CI)" } else { "" }
            );
            return ExitCode::SUCCESS;
        }
        let watchdog = std::thread::spawn(|| {
            std::thread::sleep(WATCHDOG);
            eprintln!("clazel-window smoke_macos: FAILED: still running after {WATCHDOG:?}");
            std::process::exit(1);
        });
        drop(watchdog);
        let started = Instant::now();
        a_window_opens_draws_reports_and_closes();
        eprintln!(
            "clazel-window smoke_macos: ran: a window opened, drew, reported and closed in {:?}",
            started.elapsed()
        );
        ExitCode::SUCCESS
    }

    fn a_window_opens_draws_reports_and_closes() {
        // AppKit is refused off the main thread, before any AppKit call.
        let off_main = std::thread::spawn(|| {
            matches!(
                Window::open_sized("clazel-window smoke test", 240.0, 160.0),
                Err(Error::NotMainThread)
            )
        })
        .join();
        assert!(matches!(off_main, Ok(true)), "{off_main:?}");

        let opened = Window::open_sized("clazel-window smoke test", 240.0, 160.0);
        assert!(opened.is_ok(), "open failed: {opened:?}");
        let Ok(mut window) = opened else { return };

        let (width, height) = window.size();
        assert!(
            width >= 240 && height >= 160,
            "content area {width} by {height}"
        );

        // A new window is told to draw first.
        assert_eq!(
            window.next_event(Duration::from_millis(100)),
            Some(Event::Expose)
        );

        let pixels = test_pattern(width, height, 0, None);
        let drew = window.draw(&pixels, width, height);
        assert!(drew.is_ok(), "draw failed: {drew:?}");
        // The wrong length is refused, not read.
        assert!(
            window
                .draw(&pixels, width.saturating_add(1), height)
                .is_err()
        );
        assert!(window.draw(&[], 0, 0).is_err());

        let titled = window.set_title("clazel-window smoke test, renamed");
        assert!(titled.is_ok(), "set_title failed: {titled:?}");
        assert!(window.set_title("a\0b").is_err());

        let dpi = window.dpi();
        assert!(dpi.is_some_and(|d| d >= 96), "dpi {dpi:?}");

        // Taking focus is opt-in, so that a default run never takes the keyboard
        // from someone working: CLAZEL_WINDOW_TAKE_FOCUS=1 makes the application an
        // ordinary one in front with this window key, then checks that the window
        // keeps working. The display may be asleep; nothing here waits on it.
        if std::env::var_os("CLAZEL_WINDOW_TAKE_FOCUS").is_some_and(|v| v == "1") {
            window.activate();
            let activated = Instant::now();
            while activated.elapsed() < Duration::from_millis(300) {
                let event = window.next_event(Duration::from_millis(50));
                assert_ne!(event, Some(Event::Closed), "closed by activating");
            }
            assert!(window.draw(&pixels, width, height).is_ok());
            eprintln!("clazel-window smoke_macos: took focus (CLAZEL_WINDOW_TAKE_FOCUS=1)");
        } else {
            eprintln!(
                "clazel-window smoke_macos: did not take focus (set CLAZEL_WINDOW_TAKE_FOCUS=1 to)"
            );
        }

        // A page surface twice the content area, shown in its lower half: the
        // layer is cut to that rectangle (the clip is not read back from the
        // screen here; see the README).
        let surface = Surface::new(
            usize::try_from(width).unwrap_or(1).saturating_mul(2),
            usize::try_from(height).unwrap_or(1).saturating_mul(2),
        );
        assert!(surface.is_ok(), "{surface:?}");
        if let Ok(surface) = surface {
            let half = height / 2;
            let shown = window.show_page(&surface, 0, half, width, height.saturating_sub(half));
            assert!(shown.is_ok(), "show_page failed: {shown:?}");
        }
        let hidden = window.hide_page();
        assert!(hidden.is_ok(), "hide_page failed: {hidden:?}");

        // Let AppKit work through whatever opening queued.
        let settling = Instant::now();
        while settling.elapsed() < Duration::from_millis(300) {
            let event = window.next_event(Duration::from_millis(50));
            assert_ne!(event, Some(Event::Closed), "closed by itself");
        }

        // Closing is seen by polling, through the real queue.
        window.close();
        let closing = Instant::now();
        let mut closed = false;
        while !closed && closing.elapsed() < Duration::from_secs(5) {
            closed = window.next_event(Duration::from_millis(50)) == Some(Event::Closed);
        }
        assert!(closed, "no Event::Closed within five seconds of close");
        assert_eq!(window.next_event(Duration::ZERO), None);
        assert!(window.draw(&pixels, width, height).is_ok());
        assert_eq!(window.dpi(), None);
        drop(window);
    }
}
