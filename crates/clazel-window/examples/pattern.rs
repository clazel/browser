//! Show the test pattern in a window, and print each event and how long each frame
//! took. Click to move the crosshair, use the wheel to shift the gradient, and resize
//! the window.

#[cfg(any(windows, all(target_os = "macos", target_arch = "aarch64")))]
fn main() -> Result<(), clazel_window::Error> {
    use std::time::{Duration, Instant};

    use clazel_window::pattern::test_pattern;
    use clazel_window::{Event, Window};

    let mut window = Window::open("Clazel: test pattern")?;
    // On macOS a window opens without the keyboard; this one is for a person.
    #[cfg(target_os = "macos")]
    window.activate();
    let mut shift = 0i32;
    let mut mark = None;
    let mut dirty = true;
    let mut titled = None;
    loop {
        // Everything already queued is applied before one frame is drawn. Drawing
        // once per event falls behind whenever events outrun frames, and input
        // then waits behind the backlog.
        let mut wait = Duration::from_millis(16);
        let mut batch = 0u32;
        while let Some(event) = window.next_event(wait) {
            wait = Duration::ZERO;
            batch = batch.saturating_add(1);
            println!("{event:?}");
            match event {
                Event::Closed => return Ok(()),
                Event::Click { x, y } => mark = Some((x, y)),
                Event::Wheel { delta, .. } => shift = shift.saturating_add(i32::from(delta) / 4),
                Event::Resized { .. } | Event::Expose => {}
                Event::Key { .. } | Event::Char { .. } => continue,
            }
            dirty = true;
        }
        if dirty {
            dirty = false;
            let (width, height) = window.size();
            if titled != Some((width, height)) {
                titled = Some((width, height));
                let dpi = window.dpi().unwrap_or(0);
                window.set_title(&format!(
                    "Clazel: test pattern, {width}x{height} at {dpi} dpi"
                ))?;
            }
            let start = Instant::now();
            let pixels = test_pattern(width, height, shift, mark);
            let built = start.elapsed();
            window.draw(&pixels, width, height)?;
            println!(
                "frame {width}x{height}: built in {built:?}, shown in {:?}, {batch} events",
                start.elapsed().saturating_sub(built)
            );
        }
    }
}

#[cfg(not(any(windows, all(target_os = "macos", target_arch = "aarch64"))))]
fn main() {
    println!(
        "clazel-window has a window on Windows (5.22a) and on macOS on Apple silicon (5.21) so far."
    );
}
