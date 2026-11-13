//! The window on macOS (phase-5.md item 5.21), over
//! `clazel_sys::macos::window`, on Apple silicon.
//!
//! # Decisions (ours, each listed; the event-level ones are in [`crate::nsevent`])
//!
//! - **The main thread, and no thread of our own.** AppKit may only be used on
//!   the process's main thread, so [`Window::open`] refuses any other
//!   ([`Error::NotMainThread`]), [`Window`] is neither `Send` nor `Sync`, and
//!   [`Window::next_event`] reads AppKit's queue itself. Windows reads messages on
//!   a thread of its own instead; the interface is the same. A test that opens a
//!   window therefore runs without the test harness, whose tests run on other
//!   threads.
//! - **A drag blocks.** A live resize or a drag of the title bar runs AppKit's own
//!   loop inside `sendEvent:` until it ends, and [`Window::next_event`] returns
//!   only then; the host draws nothing meanwhile. What was drawn stays at the top
//!   left of the content area (the layers keep their distance from the top), and
//!   the new size is reported when the drag ends. This is the cost of defining no
//!   callback (phase-5.md 5.0(e)); 5.23 measures whether it matters.
//! - **Size, scale and closing are polled**, as on Windows: each call to
//!   [`Window::next_event`] compares the content area's size in pixels (which a
//!   move to a screen of another scale also changes) and checks that the window is
//!   still on screen. [`Window::dpi`] reads the scale when asked.
//! - **Two layers in a layer-hosting content view.** The page's layer is below and
//!   clips to its bounds (`masksToBounds`), so a surface larger than the rectangle
//!   the host gave it, as a hostile GPU process may make, is cut at its edges
//!   (5.22a found a surface must be clipped by the host). The strip's layer, where
//!   [`Window::draw`] puts the host's own pixels (the address bar in 5.23), is
//!   above it, so nothing of the page can cover it. Layer changes are applied
//!   without Core Animation's implicit animations.
//! - **The page is an IOSurface.** [`Window::show_page`] sets the page layer's
//!   contents to a surface, shown pixel for pixel from its top left. For now the
//!   surface is one this process made; carrying one from the GPU process (a Mach
//!   port, `IOSurfaceLookupFromMachPort`) is 5.18's and 5.21a's.
//! - **No focus until asked.** [`Window::open`] shows the window without making
//!   the application active, as an accessory application (no Dock icon or menu
//!   bar), so a test's window never takes the keyboard from the user;
//!   [`Window::activate`] makes it an ordinary application in front with the
//!   window key, which `clazel browse` (5.23) will call.
//! - **No menu bar** of our own yet, so Command-Q does nothing: the window closes
//!   with its close button, or [`Window::close`].

use std::cell::Cell;
use std::collections::VecDeque;
use std::time::{Duration, Instant};

use clazel_sys::macos::window::{
    self as sys, ActivationPolicy, App, Autoresizing, Image, Layer, MainThread, Rect, Style,
    WindowError,
};

pub use clazel_sys::macos::metal::Surface;

use crate::Event;
use crate::nsevent::{self, Geometry, PointRect, Recorded};

/// The content area of a window [`Window::open`] makes, in points.
const DEFAULT_SIZE: (f64, f64) = (1024.0, 768.0);

thread_local! {
    /// Whether this process has finished launching as an application. AppKit is
    /// only used on the main thread, so a thread-local is the process's.
    static LAUNCHED: Cell<bool> = const { Cell::new(false) };
}

/// Why a window could not be opened or drawn to.
#[derive(Debug)]
pub enum Error {
    /// AppKit was asked for on a thread other than the main thread.
    NotMainThread,
    /// There is no window server session (an SSH login, a headless machine).
    NoWindowServer,
    /// A call failed, or a value was refused before it.
    Os(WindowError),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::NotMainThread => f.write_str("AppKit may only be used on the main thread"),
            Error::NoWindowServer => f.write_str("there is no window server session"),
            Error::Os(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<WindowError> for Error {
    fn from(e: WindowError) -> Error {
        Error::Os(e)
    }
}

/// Whether this process may open windows: it is in a window server session.
pub fn has_window_server() -> bool {
    sys::has_window_server()
}

/// An open window. Dropping it closes it.
#[derive(Debug)]
pub struct Window {
    main: MainThread,
    app: App,
    window: sys::Window,
    /// The content view's own layer; holds the two below.
    _root: Layer,
    page: Layer,
    strip: Layer,
    geometry: Geometry,
    size: (u32, u32),
    pending: VecDeque<Event>,
    closed: bool,
}

impl Window {
    /// Open a window of the default size. Only on the main thread.
    pub fn open(title: &str) -> Result<Window, Error> {
        Window::open_sized(title, DEFAULT_SIZE.0, DEFAULT_SIZE.1)
    }

    /// Open a window whose content area is `width` by `height` points, shown in
    /// front of this application's others without taking the keyboard. Only on
    /// the main thread, and only in a window server session.
    pub fn open_sized(title: &str, width: f64, height: f64) -> Result<Window, Error> {
        let main = MainThread::new().ok_or(Error::NotMainThread)?;
        if !sys::has_window_server() {
            return Err(Error::NoWindowServer);
        }
        let app = App::shared(main)?;
        if !LAUNCHED.get() {
            // Refused only if the policy cannot change, which leaves it as it was.
            let _ = app.set_activation_policy(ActivationPolicy::Accessory);
            app.finish_launching();
            LAUNCHED.set(true);
        }
        let style = Style {
            closable: true,
            miniaturizable: true,
            resizable: true,
        };
        let window = sys::Window::new(&app, title, width, height, style)?;
        let root = Layer::new(main)?;
        let page = Layer::new(main)?;
        let strip = Layer::new(main)?;
        let keep_to_top = Autoresizing {
            flexible_bottom_margin: true,
        };
        sys::without_animation(main, || -> Result<(), WindowError> {
            page.set_masks_to_bounds(true);
            page.set_gravity_top_left()?;
            page.set_autoresizing(keep_to_top);
            page.set_hidden(true);
            strip.set_masks_to_bounds(true);
            strip.set_autoresizing(keep_to_top);
            root.add_sublayer(&page);
            root.add_sublayer(&strip);
            window.host_layer(&root)
        })??;
        window.order_front();
        let mut opened = Window {
            main,
            app,
            window,
            _root: root,
            page,
            strip,
            geometry: Geometry {
                width,
                height,
                scale: 1.0,
            },
            size: (0, 0),
            // Nothing tells a new window to draw, as WM_PAINT does on Windows, so
            // the first event says so.
            pending: VecDeque::from([Event::Expose]),
            closed: false,
        };
        opened.geometry = opened.read_geometry()?;
        opened.size = opened.geometry.pixels();
        Ok(opened)
    }

    fn read_geometry(&self) -> Result<Geometry, WindowError> {
        let (width, height) = self.window.content_size()?;
        Ok(Geometry {
            width,
            height,
            scale: self.window.backing_scale(),
        })
    }

    /// The content area's size in pixels, as of the last [`Event::Resized`] or
    /// [`Window::open`].
    pub fn size(&self) -> (u32, u32) {
        self.size
    }

    /// The next event, waiting up to `timeout`. `None` if nothing happened.
    /// After [`Event::Closed`] this is always `None`. A drag of the window's frame
    /// or title bar holds this call until the drag ends.
    pub fn next_event(&mut self, timeout: Duration) -> Option<Event> {
        if self.closed {
            return None;
        }
        if let Some(event) = self.pending.pop_front() {
            return Some(event);
        }
        if let Some(event) = self.closed_or_resized() {
            return Some(event);
        }
        let deadline = Instant::now().checked_add(timeout);
        loop {
            let left = deadline.map_or(sys::MAX_WAIT, |d| {
                d.saturating_duration_since(Instant::now())
                    .min(sys::MAX_WAIT)
            });
            let raw = self
                .app
                .next_event(left, |raw| nsevent::forward(raw.kind))
                .ok()
                .flatten();
            if let Some(event) = self.closed_or_resized() {
                if let Some(raw) = &raw {
                    self.queue(raw);
                }
                return Some(event);
            }
            let raw = raw?;
            self.queue(&raw);
            if let Some(event) = self.pending.pop_front() {
                return Some(event);
            }
            if deadline.is_some_and(|d| Instant::now() >= d) {
                return None;
            }
        }
    }

    /// Queue what `raw` means, read against the current geometry.
    fn queue(&mut self, raw: &sys::RawEvent) {
        let recorded = Recorded {
            kind: raw.kind,
            modifiers: raw.modifiers,
            this_window: raw.window == Some(self.window.id()),
            location: raw.location,
            key_code: raw.key_code,
            characters: raw.characters.clone(),
            scroll_y: raw.scroll.map(|s| (s.dy, s.precise)),
        };
        self.pending
            .extend(nsevent::translate(&recorded, &self.geometry));
    }

    /// [`Event::Closed`] if the window has left the screen, else
    /// [`Event::Resized`] if its size in pixels changed since it was last
    /// reported.
    fn closed_or_resized(&mut self) -> Option<Event> {
        let gone = nsevent::is_closed(
            self.window.is_visible(),
            self.window.is_miniaturized(),
            self.app.is_hidden(),
        );
        if gone {
            self.closed = true;
            self.pending.clear();
            return Some(Event::Closed);
        }
        let geometry = self.read_geometry().ok()?;
        self.geometry = geometry;
        let now = geometry.pixels();
        if now == self.size {
            return None;
        }
        self.size = now;
        Some(Event::Resized {
            width: now.0,
            height: now.1,
        })
    }

    /// Copy `width` by `height` pixels to the content area's top left corner, in
    /// rows from the top, each `0x00RRGGBB`. The length of `pixels` must match.
    /// Drawing to a window that has closed does nothing, as on Windows.
    pub fn draw(&self, pixels: &[u32], width: u32, height: u32) -> Result<(), Error> {
        if self.closed {
            return Ok(());
        }
        let w = usize::try_from(width).map_err(|_| Error::Os(size_error()))?;
        let h = usize::try_from(height).map_err(|_| Error::Os(size_error()))?;
        let image = Image::new(pixels, w, h)?;
        let frame = nsevent::layer_frame(0, 0, width, height, &self.geometry);
        let scale = self.geometry.scale;
        sys::without_animation(self.main, || -> Result<(), WindowError> {
            self.strip.set_frame(rect(frame))?;
            self.strip.set_contents_scale(scale)?;
            self.strip.set_contents_image(&image);
            Ok(())
        })??;
        Ok(())
    }

    /// Show `surface` in the page's rectangle: `width` by `height` pixels at `x`,
    /// `y` from the content area's top left. The surface is shown pixel for pixel
    /// from its top left and cut at the rectangle's edges, whatever its size.
    pub fn show_page(
        &self,
        surface: &Surface,
        x: u32,
        y: u32,
        width: u32,
        height: u32,
    ) -> Result<(), Error> {
        if self.closed {
            return Ok(());
        }
        let frame = nsevent::layer_frame(x, y, width, height, &self.geometry);
        let scale = self.geometry.scale;
        sys::without_animation(self.main, || -> Result<(), WindowError> {
            self.page.set_frame(rect(frame))?;
            self.page.set_contents_scale(scale)?;
            self.page.set_contents_surface(surface);
            self.page.set_hidden(false);
            Ok(())
        })??;
        Ok(())
    }

    /// Show no page.
    pub fn hide_page(&self) -> Result<(), Error> {
        sys::without_animation(self.main, || {
            self.page.set_hidden(true);
            self.page.clear_contents();
        })?;
        Ok(())
    }

    /// Set the title bar's text. Text with a NUL in it is an error, as on Windows.
    /// Like [`Window::draw`], this does nothing to a closed window.
    pub fn set_title(&self, title: &str) -> Result<(), Error> {
        if title.contains('\0') {
            return Err(Error::Os(WindowError {
                what: "a title without NUL",
            }));
        }
        if self.closed {
            return Ok(());
        }
        self.window.set_title(title)?;
        Ok(())
    }

    /// The dots per inch of the window's screen now, 96 being unscaled, as on
    /// Windows: the backing scale times 96. `None` once the window has closed.
    pub fn dpi(&self) -> Option<u32> {
        if self.closed {
            return None;
        }
        nsevent::dpi(self.window.backing_scale())
    }

    /// Make this an ordinary application (in the Dock), bring it to the front and
    /// give this window the keyboard.
    pub fn activate(&self) {
        if self.closed {
            return;
        }
        let _ = self.app.set_activation_policy(ActivationPolicy::Regular);
        self.app.activate();
        self.window.make_key_and_order_front();
    }

    /// Close the window; [`Window::next_event`] then reports [`Event::Closed`].
    pub fn close(&self) {
        self.window.close();
    }
}

fn size_error() -> WindowError {
    WindowError {
        what: "an image size",
    }
}

fn rect(r: PointRect) -> Rect {
    Rect {
        x: r.x,
        y: r.y,
        width: r.width,
        height: r.height,
    }
}
