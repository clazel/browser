//! The window on Linux (phase-5.md item 5.22): an X11 client of our own, in safe
//! Rust, over the Unix socket `DISPLAY` names. What each request's bytes are and
//! what the server's bytes mean is [`crate::x11proto`]; this module owns the
//! socket, the window's state and the order of requests.
//!
//! # Decisions (ours, each listed; the protocol-level ones are in `x11proto`)
//!
//! - **No foreign call and no dependency.** The connection is a
//!   `std::os::unix::net::UnixStream`. Pixels reach the server as `PutImage`
//!   requests on that socket, so nothing is passed as a descriptor; the plan's
//!   MIT-SHM and DRI3 paths (which need `sendmsg`) are not built, because the GPU
//!   process does not yet export a buffer (`clazel_gpu::channel`).
//! - **Wayland sessions are reached through XWayland**, as the plan says; there
//!   is no Wayland client.
//! - **Replies and events are read on a thread of their own**, which only frames
//!   them (32 bytes, or a reply's stated length) and hands them over a channel,
//!   so [`Window::next_event`] can wait with a timeout and a request that has a
//!   reply can wait for it while events queue behind. The thread ends when the
//!   socket closes.
//! - **Two windows.** The top-level window holds the host's own pixels
//!   ([`Window::draw`]: the address bar strip, at its top left); the page is a
//!   child window the host places and sizes ([`Window::show_page_pixels`]), so
//!   the server clips the page's pixels to the rectangle the host gave it and
//!   nothing of the page can cover the strip. The child selects no input:
//!   clicks and keys over it are reported to the top-level window, in its
//!   coordinates.
//! - **What was drawn is kept and drawn again on `Expose`.** An X server keeps
//!   no window contents (no backing store is asked for), so the last strip and
//!   the last page are held here, as the pixels given, and sent again when the
//!   server says a window was uncovered.
//! - **Closing** is the window manager's `WM_DELETE_WINDOW` message (ICCCM
//!   §4.2.8.1), asked for at open; with no window manager nothing closes the
//!   window but [`Window::close`] or dropping it.
//! - **96 dots per inch, always.** The core protocol's screen size in
//!   millimetres is rarely true and `Xft.dpi` is a resource this client does not
//!   read, so [`Window::dpi`] is 96 and a HiDPI screen shows the page at scale 1.
//! - **The shortcut modifier is Control** (`Event::Key::command`), and a key
//!   pressed with it types no character.
//! - **Focus is the window manager's.** [`Window::activate`] does nothing: a
//!   window manager gives a new window the keyboard or does not, by its policy.
//! - **Errors from the server are not reported**, except for a request whose
//!   reply is being waited for: a failed draw to a window the user has just
//!   closed is expected, and the next event says the window is gone.

use std::collections::VecDeque;
use std::io::{self, Read, Write};
use std::net::Shutdown;
use std::os::unix::net::UnixStream;
use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender, channel};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use crate::Event;
use crate::x11proto::{self as proto, Geometry, Keymap, Raw, Setup, SetupReply};

/// The size a window [`Window::open`] makes asks for, in pixels.
const DEFAULT_SIZE: (u16, u16) = (1024, 768);

/// How long a request's reply is waited for.
const REPLY_WAIT: Duration = Duration::from_secs(10);

/// The largest reply read, in bytes: a keyboard mapping is at most 248 keycodes
/// of 255 keysyms of 4 bytes, under 256 KiB.
const MAX_REPLY: usize = 1 << 20;

/// Why a window could not be opened or drawn to.
#[derive(Debug)]
pub enum Error {
    /// `DISPLAY` is not set, or does not name a local display.
    NoDisplay,
    /// The socket failed.
    Io(io::Error),
    /// The server refused the connection, with its reason.
    Refused(String),
    /// The server lacks something this client needs.
    Unsupported(&'static str),
    /// The server's bytes were not what the protocol says, or a value did not
    /// fit a request.
    Protocol(&'static str),
    /// The connection has ended.
    Closed,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::NoDisplay => f.write_str("DISPLAY names no local X display"),
            Error::Io(e) => write!(f, "the X connection failed: {e}"),
            Error::Refused(why) => write!(f, "the X server refused the connection: {why}"),
            Error::Unsupported(what) => write!(f, "this window needs {what}"),
            Error::Protocol(what) => write!(f, "X protocol: {what}"),
            Error::Closed => f.write_str("the X connection has ended"),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error::Io(e)
    }
}

/// Whether `DISPLAY` names a local X display (nothing is connected to).
pub fn has_display() -> bool {
    display().is_some()
}

fn display() -> Option<u32> {
    proto::display_number(&std::env::var("DISPLAY").ok()?)
}

/// The cookie for display `number`, from `$XAUTHORITY` or `~/.Xauthority`.
fn cookie(number: u32) -> Option<Vec<u8>> {
    let path = std::env::var_os("XAUTHORITY")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            Some(std::path::PathBuf::from(std::env::var_os("HOME")?).join(".Xauthority"))
        })?;
    let entries = proto::parse_xauthority(&std::fs::read(path).ok()?);
    let hostname = std::fs::read_to_string("/proc/sys/kernel/hostname").unwrap_or_default();
    proto::cookie_for(&entries, hostname.trim().as_bytes(), number).map(<[u8]>::to_vec)
}

/// Connect to display `number`: its socket in the filesystem, else the abstract
/// socket of the same name (X(7); an X server listens on both on Linux).
fn connect(number: u32) -> io::Result<UnixStream> {
    let path = proto::socket_path(number);
    UnixStream::connect(&path).or_else(|e| abstract_socket(&path).map_err(|_| e))
}

#[cfg(target_os = "linux")]
fn abstract_socket(path: &str) -> io::Result<UnixStream> {
    use std::os::linux::net::SocketAddrExt;
    let addr = std::os::unix::net::SocketAddr::from_abstract_name(path.as_bytes())?;
    UnixStream::connect_addr(&addr)
}

#[cfg(not(target_os = "linux"))]
fn abstract_socket(_: &str) -> io::Result<UnixStream> {
    Err(io::ErrorKind::Unsupported.into())
}

/// What the reader thread hands over.
enum Message {
    /// An event or an error: its 32 bytes.
    Event(Vec<u8>),
    /// A reply, whole.
    Reply(Vec<u8>),
}

/// Frame the server's bytes until the socket ends or the receiver is gone.
fn read_messages(mut stream: UnixStream, tx: &Sender<Message>) {
    loop {
        let mut message = vec![0u8; 32];
        if stream.read_exact(&mut message).is_err() {
            return;
        }
        let Some(len) = proto::message_len(&message).filter(|n| *n <= MAX_REPLY) else {
            return;
        };
        message.resize(len, 0);
        if let Some(rest) = message.get_mut(32..)
            && stream.read_exact(rest).is_err()
        {
            return;
        }
        let is_reply = message.first().is_some_and(|c| c & 0x7F == 1);
        let sent = tx.send(if is_reply {
            Message::Reply(message)
        } else {
            Message::Event(message)
        });
        if sent.is_err() {
            return;
        }
    }
}

/// Pixels kept to draw again on `Expose`.
#[derive(Debug)]
struct Kept {
    pixels: Vec<u32>,
    width: u32,
    height: u32,
}

/// An open window. Dropping it closes it.
#[derive(Debug)]
pub struct Window {
    stream: UnixStream,
    messages: Receiver<Message>,
    reader: Option<JoinHandle<()>>,
    setup: Setup,
    /// Requests not yet written.
    out: Vec<u8>,
    /// How many requests have been sent, modulo 2^16: the last one's sequence
    /// number (§8: the first request is 1).
    sequence: u16,
    /// Events that arrived while a reply was waited for.
    early: VecDeque<Vec<u8>>,
    /// Events translated and not yet returned.
    pending: VecDeque<Event>,
    top: u32,
    page: u32,
    gc: u32,
    wm_protocols: u32,
    wm_delete_window: u32,
    net_wm_name: u32,
    utf8_string: u32,
    keymap: Keymap,
    size: (u32, u32),
    strip: Option<Kept>,
    shown: Option<Kept>,
    closed: bool,
}

impl Window {
    /// Open a window of the default size (1024 by 768; a window manager may
    /// give it another, reported as [`Event::Resized`]).
    pub fn open(title: &str) -> Result<Window, Error> {
        let number = display().ok_or(Error::NoDisplay)?;
        let mut stream = connect(number)?;
        let hello = match cookie(number) {
            Some(data) => proto::setup_request(proto::MIT_MAGIC_COOKIE, &data),
            None => proto::setup_request(b"", b""),
        }
        .ok_or(Error::Protocol(
            "an authorization that fits the setup request",
        ))?;
        stream.write_all(&hello)?;
        let mut reply = vec![0u8; 8];
        stream.read_exact(&mut reply)?;
        let rest = proto::setup_rest_len(&reply).ok_or(Error::Protocol("a setup reply"))?;
        reply.resize(rest.saturating_add(8), 0);
        if let Some(tail) = reply.get_mut(8..) {
            stream.read_exact(tail)?;
        }
        let setup = match proto::parse_setup(&reply) {
            Some(SetupReply::Success(setup)) => setup,
            Some(SetupReply::Refused(why)) => return Err(Error::Refused(why)),
            None => return Err(Error::Protocol("a setup reply")),
        };
        setup.usable().map_err(Error::Unsupported)?;
        let id = |n: u32| setup.resource_id(n).ok_or(Error::Protocol("a resource id"));
        let (top, page, gc) = (id(0)?, id(1)?, id(2)?);
        let (tx, messages) = channel();
        let reading = stream.try_clone()?;
        let reader = std::thread::Builder::new()
            .name("clazel-window".to_owned())
            .spawn(move || read_messages(reading, &tx))?;
        let mut window = Window {
            stream,
            messages,
            reader: Some(reader),
            setup,
            out: Vec::new(),
            sequence: 0,
            early: VecDeque::new(),
            pending: VecDeque::new(),
            top,
            page,
            gc,
            wm_protocols: 0,
            wm_delete_window: 0,
            net_wm_name: 0,
            utf8_string: 0,
            keymap: Keymap::default(),
            size: (u32::from(DEFAULT_SIZE.0), u32::from(DEFAULT_SIZE.1)),
            strip: None,
            shown: None,
            closed: false,
        };
        window.start(title)?;
        Ok(window)
    }

    /// Everything [`Window::open`] sends once the connection is up.
    fn start(&mut self, title: &str) -> Result<(), Error> {
        let (root, white) = (self.setup.root, self.setup.white_pixel);
        let (top, page, gc) = (self.top, self.page, self.gc);
        let whole = Geometry {
            x: 0,
            y: 0,
            width: DEFAULT_SIZE.0,
            height: DEFAULT_SIZE.1,
        };
        let events = proto::KEY_PRESS_MASK
            | proto::BUTTON_PRESS_MASK
            | proto::EXPOSURE_MASK
            | proto::STRUCTURE_NOTIFY_MASK;
        self.request(|out| proto::create_window(out, top, root, whole, white, events))?;
        let dot = Geometry {
            x: 0,
            y: 0,
            width: 1,
            height: 1,
        };
        // The page's window: unmapped until there is a page, and exposures only.
        self.request(|out| proto::create_window(out, page, top, dot, white, proto::EXPOSURE_MASK))?;
        self.request(|out| proto::create_gc(out, gc, top))?;
        self.wm_protocols = self.intern(b"WM_PROTOCOLS")?;
        self.wm_delete_window = self.intern(b"WM_DELETE_WINDOW")?;
        self.net_wm_name = self.intern(b"_NET_WM_NAME")?;
        self.utf8_string = self.intern(b"UTF8_STRING")?;
        let (protocols, delete) = (self.wm_protocols, self.wm_delete_window);
        self.request(|out| proto::change_property_atoms(out, top, protocols, &[delete]))?;
        // WM_CLASS (ICCCM §4.1.2.5): the instance and class names, each ended by NUL.
        self.request(|out| {
            proto::change_property_bytes(
                out,
                top,
                proto::ATOM_WM_CLASS,
                proto::ATOM_STRING,
                b"clazel\0Clazel\0",
            )
        })?;
        self.title(title)?;
        self.read_keymap()?;
        self.request(|out| proto::map_window(out, top))?;
        self.flush()
    }

    /// Append one request.
    fn request(&mut self, build: impl FnOnce(&mut Vec<u8>) -> Option<()>) -> Result<(), Error> {
        let before = self.out.len();
        if build(&mut self.out).is_none() {
            self.out.truncate(before);
            return Err(Error::Protocol("a value that fits its request"));
        }
        self.sequence = self.sequence.wrapping_add(1);
        Ok(())
    }

    /// Write every request appended so far.
    fn flush(&mut self) -> Result<(), Error> {
        if self.out.is_empty() {
            return Ok(());
        }
        let written = self.stream.write_all(&self.out);
        self.out.clear();
        Ok(written?)
    }

    /// Flush, and wait for the reply to the last request appended. Events that
    /// arrive first are kept for [`Window::next_event`]; an error for that
    /// request, or no reply in ten seconds, is an error here.
    fn reply(&mut self) -> Result<Vec<u8>, Error> {
        self.flush()?;
        let deadline = Instant::now().checked_add(REPLY_WAIT);
        loop {
            let left = deadline.map_or(REPLY_WAIT, |d| d.saturating_duration_since(Instant::now()));
            match self.messages.recv_timeout(left) {
                Ok(Message::Reply(reply)) => return Ok(reply),
                Ok(Message::Event(event)) => {
                    let failed = matches!(
                        proto::parse_event(&event),
                        Some(Raw::Error { sequence, .. }) if sequence == self.sequence
                    );
                    if failed {
                        return Err(Error::Protocol("the server refused a request"));
                    }
                    self.early.push_back(event);
                }
                Err(RecvTimeoutError::Timeout) => return Err(Error::Protocol("no reply")),
                Err(RecvTimeoutError::Disconnected) => return Err(Error::Closed),
            }
        }
    }

    fn intern(&mut self, name: &[u8]) -> Result<u32, Error> {
        self.request(|out| proto::intern_atom(out, name))?;
        proto::atom_of(&self.reply()?).ok_or(Error::Protocol("an atom"))
    }

    fn read_keymap(&mut self) -> Result<(), Error> {
        let first = self.setup.min_keycode;
        let count = self
            .setup
            .max_keycode
            .saturating_sub(first)
            .saturating_add(1);
        self.request(|out| proto::get_keyboard_mapping(out, first, count))?;
        let reply = self.reply()?;
        self.keymap = proto::parse_keyboard_mapping(&reply, first)
            .ok_or(Error::Protocol("a keyboard mapping"))?;
        Ok(())
    }

    fn title(&mut self, title: &str) -> Result<(), Error> {
        let (top, name, utf8) = (self.top, self.net_wm_name, self.utf8_string);
        let latin1 = proto::latin1(title);
        self.request(|out| {
            proto::change_property_bytes(out, top, proto::ATOM_WM_NAME, proto::ATOM_STRING, &latin1)
        })?;
        // _NET_WM_NAME (Extended Window Manager Hints, "Application Window
        // Properties"): the title in UTF-8, which window managers prefer.
        self.request(|out| proto::change_property_bytes(out, top, name, utf8, proto::utf8(title)))
    }

    /// The window's size in pixels, as of the last [`Event::Resized`] or
    /// [`Window::open`].
    pub fn size(&self) -> (u32, u32) {
        self.size
    }

    /// The next event, waiting up to `timeout`. `None` if nothing happened.
    /// After [`Event::Closed`] this is always `None`.
    pub fn next_event(&mut self, timeout: Duration) -> Option<Event> {
        if self.closed {
            return None;
        }
        let deadline = Instant::now().checked_add(timeout);
        loop {
            if let Some(event) = self.pending.pop_front() {
                return Some(event);
            }
            let raw = match self.early.pop_front() {
                Some(raw) => raw,
                None => {
                    let left =
                        deadline.map_or(timeout, |d| d.saturating_duration_since(Instant::now()));
                    match self.messages.recv_timeout(left) {
                        Ok(Message::Event(raw)) => raw,
                        // A reply nobody waits for: one that came after its wait
                        // gave up.
                        Ok(Message::Reply(_)) => continue,
                        Err(RecvTimeoutError::Timeout) => return None,
                        Err(RecvTimeoutError::Disconnected) => {
                            self.closed = true;
                            return Some(Event::Closed);
                        }
                    }
                }
            };
            self.translate(&raw);
        }
    }

    /// Queue what one event means.
    fn translate(&mut self, raw: &[u8]) {
        match proto::parse_event(raw) {
            Some(Raw::Key { keycode, state }) => {
                let (code, typed) = proto::key_symbols(&self.keymap, keycode, state);
                let command = state & proto::CONTROL != 0;
                self.pending.push_back(Event::Key { code, command });
                if let Some(c) = typed.filter(|c| !command && !c.is_control()) {
                    let mut units = [0u16; 2];
                    for unit in c.encode_utf16(&mut units) {
                        self.pending.push_back(Event::Char { unit: *unit });
                    }
                }
            }
            Some(Raw::Button {
                button,
                x,
                y,
                window,
            }) if window == self.top => {
                let (x, y) = (i32::from(x), i32::from(y));
                match button {
                    1 => self.pending.push_back(Event::Click { x, y }),
                    4 => self.pending.push_back(Event::Wheel { delta: 120, x, y }),
                    5 => self.pending.push_back(Event::Wheel { delta: -120, x, y }),
                    _ => {}
                }
            }
            Some(Raw::Expose { window, last: true }) => {
                // Draw again what the server dropped; a failure shows as the
                // connection ending.
                let _ = self.redraw(window);
                if window == self.top {
                    self.pending.push_back(Event::Expose);
                }
            }
            Some(Raw::Configure {
                window,
                width,
                height,
            }) if window == self.top => {
                let now = (u32::from(width), u32::from(height));
                if now != self.size {
                    self.size = now;
                    self.pending.push_back(Event::Resized {
                        width: now.0,
                        height: now.1,
                    });
                }
            }
            Some(Raw::Destroyed { window }) if window == self.top => self.ended(),
            Some(Raw::Client {
                window,
                kind,
                first,
            }) if window == self.top
                && kind == self.wm_protocols
                && first == self.wm_delete_window =>
            {
                self.close();
                self.ended();
            }
            Some(Raw::KeyboardMapping) => {
                // A failed read keeps the old map.
                let _ = self.read_keymap();
            }
            _ => {}
        }
    }

    fn ended(&mut self) {
        self.closed = true;
        self.pending.clear();
        self.pending.push_back(Event::Closed);
    }

    /// Send the kept pixels of `window` again.
    fn redraw(&mut self, window: u32) -> Result<(), Error> {
        let kept = if window == self.top {
            self.strip.take()
        } else if window == self.page {
            self.shown.take()
        } else {
            None
        };
        let Some(kept) = kept else { return Ok(()) };
        let put = self.put(window, &kept.pixels, kept.width, kept.height);
        if window == self.top {
            self.strip = Some(kept);
        } else {
            self.shown = Some(kept);
        }
        put
    }

    /// `PutImage` the whole of `pixels` at the top left of `drawable`, in as many
    /// requests as the server's limit needs, each written as it is built.
    fn put(&mut self, drawable: u32, pixels: &[u32], width: u32, height: u32) -> Result<(), Error> {
        let (gc, depth) = (self.gc, self.setup.root_depth);
        for tile in proto::tiles(width, height, self.setup.max_request_bytes()) {
            self.request(|out| {
                proto::put_image(out, (drawable, gc, depth), pixels, width, tile, (0, 0))
            })?;
            self.flush()?;
        }
        Ok(())
    }

    /// `pixels` as an image of `width` by `height`, if its length matches and
    /// neither side is 0 or over what a window can be.
    fn image(pixels: &[u32], width: u32, height: u32) -> Result<(u16, u16), Error> {
        let area = usize::try_from(width)
            .ok()
            .zip(usize::try_from(height).ok())
            .and_then(|(w, h)| w.checked_mul(h));
        let sides = u16::try_from(width).ok().zip(u16::try_from(height).ok());
        match sides {
            Some((w, h)) if w > 0 && h > 0 && area == Some(pixels.len()) => Ok((w, h)),
            _ => Err(Error::Protocol("an image whose size and length agree")),
        }
    }

    /// Copy `width` by `height` pixels to the window's top left corner, in rows
    /// from the top, each `0x00RRGGBB`. The length of `pixels` must match.
    /// Drawing to a window that has closed does nothing, as on Windows.
    pub fn draw(&mut self, pixels: &[u32], width: u32, height: u32) -> Result<(), Error> {
        Window::image(pixels, width, height)?;
        if self.closed {
            return Ok(());
        }
        self.strip = Some(Kept {
            pixels: pixels.to_vec(),
            width,
            height,
        });
        self.put(self.top, pixels, width, height)
    }

    /// Show `width` by `height` pixels, each `0x00RRGGBB`, rows from the top, as
    /// the page, at `x`, `y` from the window's top left: the page's child window
    /// is moved and sized to that rectangle, so the server cuts the pixels at
    /// its edges and at the window's. The length of `pixels` must match.
    pub fn show_page_pixels(
        &mut self,
        pixels: &[u32],
        (x, y): (u32, u32),
        width: u32,
        height: u32,
    ) -> Result<(), Error> {
        let (w, h) = Window::image(pixels, width, height)?;
        if self.closed {
            return Ok(());
        }
        let place = Geometry {
            x: i16::try_from(x).map_err(|_| Error::Protocol("a page position"))?,
            y: i16::try_from(y).map_err(|_| Error::Protocol("a page position"))?,
            width: w,
            height: h,
        };
        let page = self.page;
        self.request(|out| proto::configure_window(out, page, place))?;
        self.request(|out| proto::map_window(out, page))?;
        self.shown = Some(Kept {
            pixels: pixels.to_vec(),
            width,
            height,
        });
        self.put(page, pixels, width, height)
    }

    /// Show no page.
    pub fn hide_page(&mut self) -> Result<(), Error> {
        self.shown = None;
        if self.closed {
            return Ok(());
        }
        let page = self.page;
        self.request(|out| proto::unmap_window(out, page))?;
        self.flush()
    }

    /// Set the title bar's text. Text with a NUL in it is an error, as on
    /// Windows. Like [`Window::draw`], this does nothing to a closed window.
    pub fn set_title(&mut self, title: &str) -> Result<(), Error> {
        if title.contains('\0') {
            return Err(Error::Protocol("a title without NUL"));
        }
        if self.closed {
            return Ok(());
        }
        self.title(title)?;
        self.flush()
    }

    /// 96, the unscaled value, while the window is open (see the module
    /// documentation); `None` once it has closed.
    pub fn dpi(&self) -> Option<u32> {
        (!self.closed).then_some(96)
    }

    /// Nothing: focus is the window manager's to give.
    pub fn activate(&self) {}

    /// Close the window; [`Window::next_event`] then reports [`Event::Closed`]
    /// (the server's `DestroyNotify`).
    pub fn close(&mut self) {
        let top = self.top;
        // A failure means the connection is gone, which closes the window too.
        let _ = self.request(|out| proto::destroy_window(out, top));
        let _ = self.flush();
    }
}

impl Drop for Window {
    fn drop(&mut self) {
        if !self.closed {
            self.close();
        }
        // Ends the reader thread's read.
        let _ = self.stream.shutdown(Shutdown::Both);
        if let Some(reader) = self.reader.take() {
            // A panic on that thread has nothing more to report here.
            let _ = reader.join();
        }
    }
}
