//! `clazel browse` with a window, and `browse --headless OUT URL` (phase-5.md item
//! 5.23). Outside the line-counted shell in `src/`: it only calls `Host`'s public
//! functions. The text-mode browser of item 4.15 is `browse.rs`.
//!
//! # Modelling choices
//!
//! - **Two regions**: the address bar strip (`strip.rs`, `STRIP_POINTS`
//!   tall), drawn here, and the content area below it, showing the pixels of the
//!   latest `Paint` for the tab, clipped to it by the window's layer. The kernel's
//!   viewport is the content area: `Resize { width, height − strip, scale }`.
//! - **The scale** sent with `Resize` is 2 when the backing scale is 1.5 or more,
//!   else 1 (the kernel takes 1 or 2).
//! - **A `Paint` is shown with its pixels**: the address bar's URL, the window's
//!   title and the content area change together, when the slot the `Paint` names
//!   holds pixels of the `Paint`'s size from the tab's GPU process. A `Paint`
//!   whose pixels have not arrived yet (they come on another socket) waits for
//!   them; a newer `Paint` replaces it.
//! - **The title bar** is `URL — title`, the URL first, so a title cannot look
//!   like the address; control characters are replaced by U+FFFD and the title is
//!   cut at 200 characters.
//! - **The loop applies every queued event before it draws one frame**: it waits
//!   up to 16 ms for a window event, takes every other queued one, carries out
//!   everything the host has queued, then draws once if anything changed.
//! - **Input**: a click in the content area is `Input` kind 0 at its position
//!   relative to the content area; a wheel turn is kind 1 with the delta in
//!   device pixels, positive down, 48 CSS pixels a notch (3 lines of 16);
//!   Space and Page Down scroll down by 7/8 of the content area, Page Up up
//!   by as much, and Up and Down by 40 CSS pixels, each sent as a scroll (kind
//!   1), since the renderer (5.20) scrolls on scrolls and ignores keys; Left
//!   and Right do nothing (scrolling is vertical, 5.20). A click in the strip
//!   focuses the address bar.
//! - **The shortcut modifier** is Command on macOS and Control on Linux
//!   (`clazel_window::Event::Key`'s `command`); "Command" below means either.
//! - **The address bar**: Command-L focuses it with its URL selected (typing
//!   replaces it); typing edits it (Backspace deletes the last character);
//!   Return navigates (`navigate_tab`) to what was typed, Escape cancels. A
//!   control character is never typed. Command-`[`, or a click on the strip's
//!   back button, goes back along the URLs the
//!   tab has committed (this loop's list, as in item 4.15), Command-R reloads.
//! - **Headless**: one tab sized `--size W×H` (default 1024 by 768) at scale 1;
//!   the first `Paint` with its pixels is written, PPM if `OUT` ends in `.ppm`,
//!   else PNG (`picture.rs`); 30 seconds (or `--wait S`) without one is a
//!   failure.

use std::path::Path;
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_gpu::channel::SurfaceFrame;
use clazel_kernel::exec::records::{EventRecord, OutputRecord};
use clazel_window::keys::Named;

use crate::picture;

/// The font files a renderer is given (`--font`, item 5.20), those of these
/// that exist: TrueType faces only (5.0(c)), sans-serif, serif and monospace.
pub const RENDERER_FONTS: &[&str] = &[
    "/System/Library/Fonts/Supplemental/Arial.ttf",
    "/System/Library/Fonts/Supplemental/Arial Bold.ttf",
    "/System/Library/Fonts/Supplemental/Times New Roman.ttf",
    "/System/Library/Fonts/Supplemental/Courier New.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSerif.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf",
    "C:\\Windows\\Fonts\\arial.ttf",
    "C:\\Windows\\Fonts\\arialbd.ttf",
    "C:\\Windows\\Fonts\\times.ttf",
    "C:\\Windows\\Fonts\\cour.ttf",
];

/// The [`RENDERER_FONTS`] that exist here.
pub fn renderer_fonts() -> Vec<std::path::PathBuf> {
    RENDERER_FONTS
        .iter()
        .map(std::path::PathBuf::from)
        .filter(|p| p.is_file())
        .collect()
}

/// How long `--headless` waits for a frame unless `--wait` says otherwise.
pub const HEADLESS_WAIT: Duration = Duration::from_secs(30);

/// A `Paint` for one tab, as the host shows it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Paint {
    /// The kernel's committed URL.
    pub url: String,
    /// The renderer's title.
    pub title: String,
    /// The ring slot.
    pub buffer: u32,
    /// Width in device pixels.
    pub width: u32,
    /// Height in device pixels.
    pub height: u32,
}

/// `s` with every control character replaced by U+FFFD.
pub fn clean(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_control() { '\u{FFFD}' } else { c })
        .collect()
}

/// The newest `Paint` for `tab` in the host's queue, taking every one for it out.
pub fn take_paint(host: &mut Host, tab: u64) -> Option<Paint> {
    let mut newest = None;
    host.shown.retain(|o| match o {
        OutputRecord::Paint {
            tab: t,
            url,
            title,
            buffer,
            width,
            height,
        } if *t == tab => {
            newest = Some(Paint {
                url: clean(
                    &url.iter()
                        .filter_map(|c| char::from_u32(*c))
                        .collect::<String>(),
                ),
                title: clean(&String::from_utf8_lossy(title)),
                buffer: u32::try_from(*buffer).unwrap_or(u32::MAX),
                width: u32::try_from(*width).unwrap_or(0),
                height: u32::try_from(*height).unwrap_or(0),
            });
            false
        }
        _ => true,
    });
    newest
}

/// The renderer of `tab`, which names its GPU process.
pub fn renderer_of(host: &Host, tab: u64) -> Option<u64> {
    host.state
        .renderers
        .iter()
        .find(|r| r.tab == tab)
        .map(|r| r.id)
}

/// The pixels `paint` names, if they have arrived: taken out of the host. Pixels
/// of another size in that slot are dropped.
pub fn pixels_for(host: &mut Host, tab: u64, paint: &Paint) -> Option<SurfaceFrame> {
    let frame = host.take_frame(renderer_of(host, tab)?, paint.buffer)?;
    (frame.width == paint.width && frame.height == paint.height).then_some(frame)
}

/// The title bar's text.
pub fn title_bar(url: &str, title: &str) -> String {
    let title: String = title.chars().take(200).collect();
    if title.trim().is_empty() {
        url.to_owned()
    } else {
        format!("{url} — {title}")
    }
}

/// The text being typed in the address bar.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edit {
    /// What is typed.
    pub text: String,
    /// The text is still the selected URL: the next character replaces it.
    pub selected: bool,
    /// A high surrogate waiting for its low one.
    high: Option<u16>,
}

/// What a key or a character asks of the loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Action {
    /// Nothing.
    None,
    /// The strip changed.
    Redraw,
    /// Navigate the tab to this URL.
    Navigate(String),
    /// Go back.
    Back,
    /// Reload.
    Reload,
    /// Send the renderer this key (`Input` kind 2), by DOM `keyCode`.
    Key(u32),
}

/// The address bar: the URL shown and, while the user types, the edit.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Bar {
    /// The URL the bar shows (the latest `Paint`'s, or the one asked for).
    pub url: String,
    /// Whether `url` is the kernel's.
    pub committed: bool,
    /// The edit, while the user types.
    pub edit: Option<Edit>,
}

impl Bar {
    /// Focus the bar, its URL selected.
    pub fn focus(&mut self) -> Action {
        self.edit = Some(Edit {
            text: self.url.clone(),
            selected: true,
            high: None,
        });
        Action::Redraw
    }

    /// A key went down.
    pub fn key(&mut self, key: Option<Named>, command: bool) -> Action {
        match (key, command, self.edit.as_mut()) {
            (Some(Named::L), true, _) => self.focus(),
            (Some(Named::LeftBracket), true, _) => Action::Back,
            (Some(Named::R), true, _) => Action::Reload,
            (_, true, _) => Action::None,
            (Some(Named::Return), false, Some(edit)) => {
                let url = edit.text.trim().to_owned();
                self.edit = None;
                if url.is_empty() {
                    Action::Redraw
                } else {
                    Action::Navigate(url)
                }
            }
            (Some(Named::Escape), false, Some(_)) => {
                self.edit = None;
                Action::Redraw
            }
            (Some(Named::Backspace), false, Some(edit)) => {
                if edit.selected {
                    edit.text.clear();
                } else {
                    edit.text.pop();
                }
                edit.selected = false;
                Action::Redraw
            }
            (_, false, Some(_)) => Action::None,
            (Some(k @ (Named::Space | Named::PageUp | Named::PageDown)), false, None)
            | (Some(k @ (Named::Up | Named::Down | Named::Left | Named::Right)), false, None) => {
                Action::Key(k.dom_key_code())
            }
            (_, false, None) => Action::None,
        }
    }

    /// A UTF-16 code unit was typed.
    pub fn char(&mut self, unit: u16) -> Action {
        let Some(edit) = self.edit.as_mut() else {
            return Action::None;
        };
        let c = match (edit.high.take(), unit) {
            (_, 0xD800..=0xDBFF) => {
                edit.high = Some(unit);
                return Action::None;
            }
            (Some(high), 0xDC00..=0xDFFF) => {
                char::decode_utf16([high, unit]).next().and_then(Result::ok)
            }
            (_, _) => char::from_u32(u32::from(unit)),
        };
        match c {
            Some(c) if !c.is_control() => {
                if edit.selected {
                    edit.text.clear();
                    edit.selected = false;
                }
                edit.text.push(c);
                Action::Redraw
            }
            _ => Action::None,
        }
    }
}

/// The URLs a tab committed, the current one last, for going back.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct History {
    urls: Vec<String>,
    going_back: bool,
}

impl History {
    /// A `Paint` showed `url`.
    pub fn shown(&mut self, url: &str) {
        if !self.going_back && self.urls.last().map(String::as_str) != Some(url) {
            self.urls.push(url.to_owned());
        }
        self.going_back = false;
    }

    /// Whether there is a URL to go back to.
    pub fn can_go_back(&self) -> bool {
        self.urls.len() >= 2
    }

    /// Where going back goes, if anywhere.
    pub fn back(&mut self) -> Option<String> {
        if self.urls.len() < 2 {
            return None;
        }
        self.urls.pop();
        self.going_back = true;
        self.urls.last().cloned()
    }
}

/// The wheel's `delta` (120 a notch, positive away from the user) as device
/// pixels to scroll, positive down.
pub fn wheel_pixels(delta: i16, scale: u64) -> i64 {
    let scale = i64::try_from(scale).unwrap_or(1);
    i64::from(delta).saturating_mul(-48).saturating_mul(scale) / 120
}

/// The scroll, in device pixels (positive down), that a key with DOM `keyCode`
/// `code` asks for in a content area `page` pixels tall at `scale`.
pub fn key_scroll(code: u32, page: u32, scale: u64) -> Option<i64> {
    let page = (i64::from(page) / 8).saturating_mul(7);
    let line = 40i64.saturating_mul(i64::try_from(scale).unwrap_or(1));
    match code {
        32 | 34 => Some(page),
        33 => Some(page.saturating_neg()),
        38 => Some(line.saturating_neg()),
        40 => Some(line),
        _ => None,
    }
}

/// RGBA8 premultiplied pixels as the window's `0x00RRGGBB`, over white.
pub fn window_pixels(rgba: &[u8]) -> Vec<u32> {
    picture::rgb_over_white(rgba)
        .as_chunks::<3>()
        .0
        .iter()
        .map(|[r, g, b]| u32::from(*r) << 16 | u32::from(*g) << 8 | u32::from(*b))
        .collect()
}

/// `browse --headless OUT URL`: open a tab at `url` sized `width` by `height`,
/// and write its first frame to `out`, waiting up to `wait` for it.
pub fn headless(
    host: &mut Host,
    out: &Path,
    url: &str,
    (width, height): (u32, u32),
    wait: Duration,
) -> Result<(), String> {
    let tab = host.open(url);
    if renderer_of(host, tab).is_none() {
        return Err(format!("cannot open {url}"));
    }
    host.event(EventRecord::Resize {
        tab,
        width: width.into(),
        height: height.into(),
        scale: 1,
    });
    let end = Instant::now()
        .checked_add(wait)
        .unwrap_or_else(Instant::now);
    let mut pending = None;
    while Instant::now() < end {
        host.pump(Duration::from_millis(20));
        pending = take_paint(host, tab).or(pending);
        let Some(paint) = &pending else { continue };
        let Some(frame) = pixels_for(host, tab, paint) else {
            continue;
        };
        let rgb = picture::rgb_over_white(&frame.pixels);
        let ppm = out
            .extension()
            .is_some_and(|e| e.eq_ignore_ascii_case("ppm"));
        let bytes = if ppm {
            picture::ppm(frame.width, frame.height, &rgb)
        } else {
            picture::png(frame.width, frame.height, &rgb)
        };
        let bytes = bytes.ok_or("the frame's size and its pixels disagree")?;
        std::fs::write(out, bytes).map_err(|e| format!("cannot write {}: {e}", out.display()))?;
        eprintln!(
            "clazel: wrote {} ({} by {}) for {}",
            out.display(),
            frame.width,
            frame.height,
            paint.url
        );
        return Ok(());
    }
    if renderer_of(host, tab).is_none() {
        return Err(format!("the tab for {url} is gone"));
    }
    Err(format!("no frame for {url} within {wait:?}"))
}

/// The user's input on `tab`'s content area (`EventRecord::Input`): `kind` 0 a
/// click, 1 a scroll, 2 a key; the scroll delta signed.
pub fn input(host: &mut Host, tab: u64, kind: u64, (x, y): (u64, u64), delta: i64, key: u64) {
    host.event(EventRecord::Input {
        tab,
        kind,
        x,
        y,
        negative: delta < 0,
        delta: delta.unsigned_abs(),
        key,
    });
}

/// The window loop, on macOS on Apple silicon, on Linux and on Windows: the same
/// loop over `clazel_window::Window`, whose three backends give the same calls.
/// On Windows it has been compiled and never run.
#[cfg(any(
    all(target_os = "macos", target_arch = "aarch64"),
    target_os = "linux",
    windows
))]
pub mod windowed {
    use std::time::Duration;

    use clazel::Host;
    use clazel_kernel::exec::records::EventRecord;
    use clazel_window::{Event, Window, keys};

    use super::{
        Action, Bar, History, input, key_scroll, pixels_for, renderer_of, take_paint, title_bar,
        wheel_pixels, window_pixels,
    };
    use crate::strip::{self, Contents, STRIP_POINTS};

    /// The kernel's scale for a backing scale (its `dpi() / 96`).
    fn kernel_scale(dpi: u32) -> u64 {
        if dpi >= 144 { 2 } else { 1 }
    }

    /// What the loop keeps between frames.
    struct Tab {
        tab: u64,
        bar: Bar,
        history: History,
        pending: Option<super::Paint>,
        strip_px: u32,
        scale: u64,
        size: (u32, u32),
    }

    impl Tab {
        fn content(&self) -> (u32, u32) {
            (self.size.0, self.size.1.saturating_sub(self.strip_px))
        }

        fn resize(&mut self, host: &mut Host, window: &Window) {
            self.size = window.size();
            self.scale = kernel_scale(window.dpi().unwrap_or(96));
            let backing = f64::from(window.dpi().unwrap_or(96)) / 96.0;
            self.strip_px = (STRIP_POINTS * backing).round() as u32;
            let (w, h) = self.content();
            host.event(EventRecord::Resize {
                tab: self.tab,
                width: w.into(),
                height: h.into(),
                scale: self.scale,
            });
        }

        fn navigate(&mut self, host: &mut Host, url: &str) {
            self.bar.url = url.to_owned();
            self.bar.committed = false;
            host.navigate_tab(self.tab, url);
        }

        fn act(&mut self, host: &mut Host, action: Action) -> bool {
            match action {
                Action::None => false,
                Action::Redraw => true,
                Action::Navigate(url) => {
                    self.navigate(host, &url);
                    true
                }
                Action::Back => match self.history.back() {
                    Some(url) => {
                        self.navigate(host, &url);
                        true
                    }
                    None => false,
                },
                Action::Reload => {
                    let url = self.bar.url.clone();
                    self.navigate(host, &url);
                    true
                }
                Action::Key(code) => {
                    let page = self.content().1;
                    if let Some(d) = key_scroll(code, page, self.scale) {
                        input(host, self.tab, 1, (0, 0), d, 0);
                    }
                    false
                }
            }
        }

        /// One window event; whether the strip changed.
        fn on(&mut self, host: &mut Host, window: &Window, event: Event) -> bool {
            let strip = i32::try_from(self.strip_px).unwrap_or(i32::MAX);
            match event {
                Event::Expose => true,
                Event::Resized { .. } => {
                    self.resize(host, window);
                    true
                }
                Event::Click { x, y } if y < strip => {
                    let backing = f64::from(window.dpi().unwrap_or(96)) / 96.0;
                    if strip::on_back_button(x.into(), y.into(), self.strip_px, backing) {
                        self.bar.edit = None;
                        self.act(host, Action::Back)
                    } else {
                        self.bar.focus() == Action::Redraw
                    }
                }
                Event::Click { x, y } => {
                    let at = (
                        u64::try_from(x).unwrap_or(0),
                        u64::try_from(y.saturating_sub(strip)).unwrap_or(0),
                    );
                    input(host, self.tab, 0, at, 0, 0);
                    false
                }
                Event::Wheel { delta, x, y } if y >= strip => {
                    let at = (
                        u64::try_from(x).unwrap_or(0),
                        u64::try_from(y.saturating_sub(strip)).unwrap_or(0),
                    );
                    input(host, self.tab, 1, at, wheel_pixels(delta, self.scale), 0);
                    false
                }
                Event::Wheel { .. } | Event::Closed => false,
                Event::Key { code, command } => {
                    let action = self.bar.key(keys::named(code), command);
                    self.act(host, action)
                }
                Event::Char { unit } => {
                    let action = self.bar.char(unit);
                    self.act(host, action)
                }
            }
        }
    }

    /// Open a window and browse `url` in it until the window closes.
    pub fn run(host: &mut Host, url: &str) -> Result<(), String> {
        let mut window =
            Window::open("Clazel").map_err(|e| format!("cannot open a window: {e:?}"))?;
        window.activate();
        let font = strip::system_font();
        if font.is_none() {
            eprintln!(
                "clazel: no TrueType font found (strip.rs FONT_PATHS); the address bar has no text"
            );
        }
        let tab = host.open(url);
        if renderer_of(host, tab).is_none() {
            return Err(format!("cannot open {url}"));
        }
        let mut t = Tab {
            tab,
            bar: Bar {
                url: url.to_owned(),
                committed: false,
                edit: None,
            },
            history: History::default(),
            pending: None,
            strip_px: 0,
            scale: 1,
            size: (0, 0),
        };
        t.resize(host, &window);
        let _ = window.set_title(&title_bar(url, ""));
        let mut dirty = true;
        loop {
            // Every queued window event, then everything the host has, then one frame.
            let mut next = window.next_event(Duration::from_millis(16));
            while let Some(event) = next {
                if event == Event::Closed {
                    return Ok(());
                }
                dirty |= t.on(host, &window, event);
                next = window.next_event(Duration::ZERO);
            }
            for _ in 0..256 {
                if !host.pump(Duration::ZERO) {
                    break;
                }
            }
            if renderer_of(host, tab).is_none() {
                return Err("the tab is gone".to_owned());
            }
            t.pending = take_paint(host, tab).or(t.pending.take());
            let ready = t
                .pending
                .clone()
                .and_then(|p| Some((pixels_for(host, tab, &p)?, p)));
            if let Some((frame, paint)) = ready {
                t.pending = None;
                t.history.shown(&paint.url);
                t.bar.url = paint.url.clone();
                t.bar.committed = true;
                let _ = window.set_title(&title_bar(&paint.url, &paint.title));
                let pixels = window_pixels(&frame.pixels);
                let shown =
                    window.show_page_pixels(&pixels, (0, t.strip_px), frame.width, frame.height);
                match shown {
                    Ok(()) => eprintln!(
                        "clazel: showing {} ({} by {}, slot {})",
                        paint.url, frame.width, frame.height, paint.buffer
                    ),
                    Err(e) => eprintln!("clazel: cannot show the page: {e:?}"),
                }
                dirty = true;
            }
            if dirty {
                let text = t
                    .bar
                    .edit
                    .as_ref()
                    .map_or(t.bar.url.as_str(), |e| e.text.as_str());
                let what = Contents {
                    text,
                    editing: t.bar.edit.is_some(),
                    committed: t.bar.committed || t.bar.edit.is_some(),
                    can_go_back: t.history.can_go_back(),
                };
                let backing = f64::from(window.dpi().unwrap_or(96)) / 96.0;
                let pixels = strip::render(font.as_deref(), t.size.0, t.strip_px, backing, &what);
                if let Err(e) = window.draw(&pixels, t.size.0, t.strip_px) {
                    eprintln!("clazel: cannot draw the address bar: {e:?}");
                }
                dirty = false;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use clazel_window::keys::Named;

    use super::{Action, Bar, History, clean, key_scroll, title_bar, wheel_pixels, window_pixels};

    fn bar() -> Bar {
        Bar {
            url: "http://a.test/".to_owned(),
            committed: true,
            edit: None,
        }
    }

    fn typed(b: &Bar) -> Option<&str> {
        b.edit.as_ref().map(|e| e.text.as_str())
    }

    #[test]
    fn command_l_selects_the_url_and_typing_replaces_it() {
        let mut b = bar();
        assert_eq!(b.key(Some(Named::L), true), Action::Redraw);
        assert_eq!(typed(&b), Some("http://a.test/"));
        for u in "b.test".encode_utf16() {
            assert_eq!(b.char(u), Action::Redraw);
        }
        assert_eq!(typed(&b), Some("b.test"));
        assert_eq!(b.key(Some(Named::Backspace), false), Action::Redraw);
        assert_eq!(
            b.key(Some(Named::Return), false),
            Action::Navigate("b.tes".to_owned())
        );
        assert_eq!(b.edit, None);
    }

    #[test]
    fn escape_cancels_and_control_characters_are_never_typed() {
        let mut b = bar();
        b.focus();
        assert_eq!(b.char(0x0D), Action::None);
        assert_eq!(b.char(0x1B), Action::None);
        assert_eq!(b.char(0x7F), Action::None);
        assert_eq!(typed(&b), Some("http://a.test/"));
        assert_eq!(b.key(Some(Named::Escape), false), Action::Redraw);
        assert_eq!(b.edit, None);
        assert_eq!(b.char(u16::from(b'x')), Action::None);
    }

    #[test]
    fn a_character_outside_the_bmp_is_typed_whole() {
        let mut b = bar();
        b.focus();
        let units: Vec<u16> = "😀".encode_utf16().collect();
        assert_eq!(units.len(), 2);
        assert_eq!(b.char(units.first().copied().unwrap_or(0)), Action::None);
        assert_eq!(b.char(units.get(1).copied().unwrap_or(0)), Action::Redraw);
        assert_eq!(typed(&b), Some("😀"));
        // A lone low surrogate types nothing.
        assert_eq!(b.char(0xDC00), Action::None);
    }

    #[test]
    fn shortcuts_and_scrolling_keys() {
        let mut b = bar();
        assert_eq!(b.key(Some(Named::LeftBracket), true), Action::Back);
        assert_eq!(b.key(Some(Named::R), true), Action::Reload);
        assert_eq!(b.key(Some(Named::Space), false), Action::Key(32));
        assert_eq!(b.key(Some(Named::PageDown), false), Action::Key(34));
        assert_eq!(b.key(Some(Named::Down), false), Action::Key(40));
        assert_eq!(b.key(Some(Named::Return), false), Action::None);
        assert_eq!(b.key(None, false), Action::None);
        // While typing, Space is a character and the arrows do nothing.
        b.focus();
        assert_eq!(b.key(Some(Named::Space), false), Action::None);
        assert_eq!(b.key(Some(Named::Down), false), Action::None);
        // An empty address navigates nowhere.
        assert_eq!(b.key(Some(Named::Backspace), false), Action::Redraw);
        assert_eq!(b.key(Some(Named::Return), false), Action::Redraw);
    }

    #[test]
    fn scrolling_keys_scroll_by_the_page_or_a_line() {
        assert_eq!(key_scroll(32, 800, 1), Some(700));
        assert_eq!(key_scroll(34, 800, 2), Some(700));
        assert_eq!(key_scroll(33, 800, 1), Some(-700));
        assert_eq!(key_scroll(40, 800, 2), Some(80));
        assert_eq!(key_scroll(38, 800, 1), Some(-40));
        assert_eq!(key_scroll(37, 800, 1), None);
        assert_eq!(key_scroll(39, 800, 1), None);
    }

    #[test]
    fn back_walks_the_committed_urls() {
        let mut h = History::default();
        assert_eq!(h.back(), None);
        assert!(!h.can_go_back());
        h.shown("a");
        h.shown("a");
        h.shown("b");
        h.shown("c");
        assert_eq!(h.back(), Some("b".to_owned()));
        h.shown("b");
        assert_eq!(h.back(), Some("a".to_owned()));
        h.shown("a");
        assert_eq!(h.back(), None);
    }

    #[test]
    fn the_title_comes_after_the_url_and_is_cleaned() {
        assert_eq!(title_bar("http://a/", ""), "http://a/");
        assert_eq!(title_bar("http://a/", "Hi"), "http://a/ — Hi");
        assert_eq!(clean("a\u{0}b\u{1b}[2J"), "a\u{FFFD}b\u{FFFD}[2J");
        assert_eq!(title_bar("u", &"x".repeat(500)).chars().count(), 4 + 200);
    }

    #[test]
    fn wheel_and_pixels() {
        assert_eq!(wheel_pixels(120, 1), -48);
        assert_eq!(wheel_pixels(-120, 2), 96);
        assert_eq!(wheel_pixels(0, 1), 0);
        assert_eq!(
            window_pixels(&[0, 0, 0, 0, 1, 2, 3, 255]),
            [0x00FF_FFFF, 0x0001_0203]
        );
    }
}
