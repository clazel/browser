//! The renderer (phase-2.md item 2.15; the document pipeline of phase-4.md
//! item 4.13; the page's scripts and event loop, phase-7.md item 7.17).
//!
//! The binary's first act is [`sandbox::enter`], before it reads a byte;
//! then it reads frames from its socket (standard input, with the same
//! socket as standard output) and waits for a committed document: a
//! `Commit`, its `Body` frames and `BodyEnd` (phase-4.md item 4.12).
//!
//! - Kind 1, a user script (the Phase 2 path): the body is JavaScript, which
//!   runs in an empty document at the committed URL. Its `document.cookie`
//!   and `localStorage` are the kernel's Phase 2 messages, sent by script
//!   ([`page::scripts`]); the host shell sees every request and reply on the
//!   socket and prints them, so the renderer needs no channel besides the
//!   one the kernel also reads. It exits when the script and what it queued
//!   for now are done; the host sees the socket close. (Phase 2's line
//!   format, `cookie-get` and the rest, is retired: item 7.17.)
//! - Kind 0, a document: the document pipeline ([`pipeline`]: content
//!   type, encoding, the HTML parser, the document base URL and the text
//!   layout) gives one `Display`, made to fit one frame ([`pipeline::fit`]);
//!   then the renderer waits for the next document (a same-origin
//!   navigation commits into the same renderer). The socket closing while
//!   it waits is the end of the tab, not an error. The text path runs no
//!   page scripts.
//! - Kind 0 in the graphical renderer ([`run_graphics`], [`page`]): the
//!   document's scripts run, and the event loop keeps running them (timers,
//!   tasks, microtasks, fetched scripts, a clicked `javascript:` link); the
//!   page is styled, laid out and painted again after a script changed it.
//!
//! An `Error` while it waits (a navigation that failed, item 3.7) changes
//! nothing: the renderer keeps its document and waits on.

pub mod escape;
pub mod hostile;
pub mod launch;
pub mod page;
pub mod pipeline;
pub mod sandbox;

use std::fmt;
use std::io::{self, Read, Write};
use std::sync::Arc;

use clazel_ipc::frame::codec::payload_length;
use clazel_ipc::message::codec::{Msg, decode_framed};
use clazel_web::scripting::time::{Clock, SystemClock};
use page::link::{Link, LinkHandle, lock};

/// Why the renderer stopped.
#[derive(Debug)]
pub enum RunError {
    /// The socket failed or closed.
    Io(io::Error),
    /// The kernel sent something the protocol does not allow here.
    Protocol(&'static str),
    /// The script engine could not start.
    Engine(String),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::Io(e) => write!(f, "socket: {e}"),
            RunError::Protocol(why) => write!(f, "protocol: {why}"),
            RunError::Engine(why) => write!(f, "script engine: {why}"),
        }
    }
}

impl From<io::Error> for RunError {
    fn from(e: io::Error) -> Self {
        RunError::Io(e)
    }
}

/// The next message, waiting for it: the link's inbox first. `Ok(None)` is
/// the socket closed between messages, which is the end of the tab.
fn next_message(link: &LinkHandle) -> Result<Option<Msg>, RunError> {
    loop {
        let polled = lock(link).poll();
        match polled {
            Ok(Some(m)) => return Ok(Some(m)),
            Ok(None) => {}
            Err(RunError::Io(e)) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(e),
        }
    }
}

/// The most body octets a renderer takes: `clazel-http`'s 64 MiB limit on a
/// response body, which the kernel never exceeds.
pub const MAX_BODY: usize = 64 * 1024 * 1024;

/// A committed document: its URL, content type, kind and body.
#[derive(Debug, PartialEq, Eq)]
pub struct Document {
    /// The committed URL, UTF-8.
    pub url: Vec<u8>,
    /// The content type, possibly empty.
    pub content_type: Vec<u8>,
    /// 0 a document, 1 a user script.
    pub kind: u64,
    /// The body.
    pub body: Vec<u8>,
}

/// Read one whole message; the length is checked against `MAX_FRAME` from
/// the first 4 bytes, before the payload is read.
fn read_message<R: Read>(r: &mut R) -> Result<Msg, RunError> {
    let mut header = [0u8; 4];
    r.read_exact(&mut header)?;
    let len = payload_length(&header).ok_or(RunError::Protocol("frame over MAX_FRAME"))?;
    let mut frame = header.to_vec();
    let mut payload = vec![0u8; len];
    r.read_exact(&mut payload)?;
    frame.extend_from_slice(&payload);
    decode_framed(&frame).ok_or(RunError::Protocol("frame does not decode"))
}

/// Wait for the next committed document on a plain reader: skip `Error`s,
/// take a `Commit`, then its `Body` frames up to `BodyEnd`. `None` if the
/// socket closes before a `Commit`.
pub fn next_document<R: Read>(r: &mut R) -> Result<Option<Document>, RunError> {
    let (url, content_type, kind) = loop {
        match read_message(r) {
            Ok(Msg::Commit {
                url,
                content_type,
                kind,
            }) => break (url, content_type, kind),
            Ok(Msg::Error { .. }) => {}
            Ok(_) => return Err(RunError::Protocol("expected Commit")),
            Err(RunError::Io(e)) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(e),
        }
    };
    let mut body = Vec::new();
    loop {
        match read_message(r)? {
            Msg::Body { bytes } => {
                if body.len().saturating_add(bytes.len()) > MAX_BODY {
                    return Err(RunError::Protocol("body over 64 MiB"));
                }
                body.extend_from_slice(&bytes);
            }
            Msg::BodyEnd => break,
            _ => return Err(RunError::Protocol("expected Body or BodyEnd")),
        }
    }
    Ok(Some(Document {
        url,
        content_type,
        kind,
        body,
    }))
}

/// [`next_document`] on the renderer's link.
fn next_document_on(link: &LinkHandle) -> Result<Option<Document>, RunError> {
    let (url, content_type, kind) = loop {
        match next_message(link)? {
            Some(Msg::Commit {
                url,
                content_type,
                kind,
            }) => break (url, content_type, kind),
            Some(Msg::Error { .. }) => {}
            Some(_) => return Err(RunError::Protocol("expected Commit")),
            None => return Ok(None),
        }
    };
    let body = read_body(link)?;
    Ok(Some(Document {
        url,
        content_type,
        kind,
        body,
    }))
}

/// The width [`run`] lays documents out at: the terminal width most hosts
/// have when `$COLUMNS` says nothing.
pub const DEFAULT_WIDTH: usize = 80;

/// [`run_with_width`] at [`DEFAULT_WIDTH`].
pub fn run<R: Read + Send + 'static, W: Write + Send + 'static>(
    r: R,
    w: W,
) -> Result<usize, RunError> {
    run_with_width(r, w, DEFAULT_WIDTH)
}

/// Take committed documents until a script (kind 1) is run or the socket
/// closes: a document (kind 0) goes through the pipeline and is displayed
/// `width` columns wide (0: no wrapping), a script is run. Returns 1 if a
/// script was run, else 0.
pub fn run_with_width<R: Read + Send + 'static, W: Write + Send + 'static>(
    r: R,
    w: W,
    width: usize,
) -> Result<usize, RunError> {
    let link = Link::shared(r, w);
    loop {
        let Some(doc) = next_document_on(&link)? else {
            return Ok(0);
        };
        match doc.kind {
            1 => return run_user_script(&link, &doc.url, &doc.body, Box::new(SystemClock::new())),
            0 => {
                let shown = pipeline::render(&doc.url, &doc.content_type, &doc.body, width);
                // The body and its tree are gone; only the page is kept.
                drop(doc);
                lock(&link).send(&pipeline::fit(shown))?;
            }
            _ => return Err(RunError::Protocol("unknown document kind")),
        }
    }
}

/// The body of a committed document: its `Body` frames up to `BodyEnd`.
fn read_body(link: &LinkHandle) -> Result<Vec<u8>, RunError> {
    let mut body = Vec::new();
    loop {
        match next_message(link)? {
            Some(Msg::Body { bytes }) => {
                if body.len().saturating_add(bytes.len()) > MAX_BODY {
                    return Err(RunError::Protocol("body over 64 MiB"));
                }
                body.extend_from_slice(&bytes);
            }
            Some(Msg::BodyEnd) => return Ok(body),
            Some(_) => return Err(RunError::Protocol("expected Body or BodyEnd")),
            None => {
                return Err(RunError::Io(io::Error::from(io::ErrorKind::UnexpectedEof)));
            }
        }
    }
}

/// Write one list to the GPU process's socket (`page::frame::frame_bytes`).
fn send_list<L: Write>(
    list: &mut L,
    page: &page::Page,
    view: page::View,
    fonts: &page::fonts::Fonts,
    cache: &mut page::frame::MaskCache,
) -> Result<(), RunError> {
    let Some(dl) = page.list() else {
        return Ok(());
    };
    let items = page::frame::frame(dl, view.width, view.height, page.scroll, fonts, cache);
    let bytes = page::frame::frame_bytes(&items, view)
        .ok_or(RunError::Protocol("display list over its limits"))?;
    list.write_all(&bytes)?;
    list.flush()?;
    Ok(())
}

/// The graphical renderer's state: the current page, the viewport, what the
/// GPU process holds, and the style sheet answers being received.
struct Graphics<'a, L: Write> {
    link: LinkHandle,
    list: &'a mut L,
    fonts: &'a page::fonts::Fonts,
    make_clock: &'a mut dyn FnMut() -> Box<dyn Clock>,
    current: Option<page::Page>,
    view: Option<page::View>,
    cache: page::frame::MaskCache,
    shown_title: Option<String>,
    /// Style sheet answers being received (item 5.19): request id to the
    /// response's content type and the body so far.
    sheets: std::collections::HashMap<u64, (Vec<u8>, Vec<u8>)>,
}

impl<L: Write> Graphics<'_, L> {
    /// Sends `Title` to the kernel if the page's differs from the last sent.
    fn send_title(&mut self) -> Result<(), RunError> {
        let Some(p) = self.current.as_ref() else {
            return Ok(());
        };
        if self.shown_title.as_deref() != Some(p.title.as_str()) {
            let title = p.title.clone().into_bytes();
            lock(&self.link).send(&Msg::Title { title })?;
            self.shown_title = Some(p.title.clone());
        }
        Ok(())
    }

    /// Lays the page out and writes its list, if there is a viewport.
    fn paint(&mut self) -> Result<(), RunError> {
        let (Some(p), Some(v)) = (self.current.as_mut(), self.view) else {
            return Ok(());
        };
        p.lay_out(v, self.fonts);
        send_list(self.list, p, v, self.fonts, &mut self.cache)
    }

    /// A script ran (`ran`): the animation frames that paint would run, the
    /// restyle (`Page::settle`), the title, and a new list if the page
    /// changed.
    fn scripts_ran(&mut self, ran: bool) -> Result<(), RunError> {
        let Some(p) = self.current.as_mut() else {
            return Ok(());
        };
        if ran && self.view.is_some() {
            p.update_the_rendering()?;
        }
        if !p.settle() {
            return Ok(());
        }
        self.send_title()?;
        self.paint()
    }

    /// A sheet of the current page answered (a body, or `None` for a
    /// failure): if that makes the page ready and there is a viewport, lay
    /// it out and paint it.
    fn sheet_answered(
        &mut self,
        request: u64,
        response: Option<(&[u8], &[u8])>,
    ) -> Result<(), RunError> {
        let Some(p) = self.current.as_mut() else {
            return Ok(());
        };
        if p.answer(request, response) {
            // Scripts that ran while the sheets were awaited changed the
            // document: its sources are collected again first.
            p.settle();
            self.send_title()?;
            self.paint()?;
        }
        Ok(())
    }

    /// A committed document: the previous page, its lists and its sheets
    /// are gone; the new one's `FetchStyle`s are sent, its scripts run and
    /// it is painted.
    fn commit(&mut self, url: &[u8], content_type: &[u8], body: &[u8]) -> Result<(), RunError> {
        drop(self.current.take());
        self.sheets.clear();
        let env = page::ScriptEnv {
            link: Arc::clone(&self.link),
            clock: (self.make_clock)(),
        };
        let mut p = page::Page::load_scripted(url, content_type, body, self.view, env);
        // HTML's render-blocking style sheets: a `FetchStyle` each;
        // the page is painted once every one is answered.
        for (request, url) in p.requests() {
            lock(&self.link).send(&Msg::FetchStyle { request, url })?;
        }
        p.start_scripts()?;
        self.current = Some(p);
        // The first settle collects what the scripts changed.
        if let Some(p) = self.current.as_mut() {
            p.settle();
        }
        self.send_title()?;
        self.paint()
    }

    /// One message of the kernel. `Some(n)`: a user script ran, and the
    /// renderer is done.
    fn handle(&mut self, m: Msg) -> Result<Option<usize>, RunError> {
        match m {
            Msg::Commit {
                url,
                content_type,
                kind,
            } => {
                let body = read_body(&self.link)?;
                match kind {
                    1 => {
                        let clock = (self.make_clock)();
                        return run_user_script(&self.link, &url, &body, clock).map(Some);
                    }
                    0 => {}
                    _ => return Err(RunError::Protocol("unknown document kind")),
                }
                self.commit(&url, &content_type, &body)?;
            }
            Msg::Error { .. } => {}
            Msg::StyleResponse {
                request,
                content_type,
            } => {
                self.sheets.insert(request, (content_type, Vec::new()));
            }
            Msg::StyleBody { request, bytes } => {
                let over = match self.sheets.get_mut(&request) {
                    Some((_, body)) if body.len().saturating_add(bytes.len()) <= MAX_BODY => {
                        body.extend_from_slice(&bytes);
                        false
                    }
                    Some(_) => true,
                    None => false,
                };
                // A sheet over the body limit is failed (README, memory).
                if over {
                    self.sheets.remove(&request);
                    self.sheet_answered(request, None)?;
                }
            }
            Msg::StyleEnd { request } => {
                if let Some((content_type, body)) = self.sheets.remove(&request) {
                    self.sheet_answered(request, Some((&content_type, &body)))?;
                }
            }
            Msg::StyleFailed { request } => {
                self.sheets.remove(&request);
                self.sheet_answered(request, None)?;
            }
            Msg::ScriptResponse {
                request,
                content_type,
            } => {
                if let Some(p) = self.current.as_mut() {
                    p.script_response(request, content_type)?;
                }
            }
            Msg::ScriptBody { request, bytes } => {
                let ran = match self.current.as_mut() {
                    Some(p) => p.script_body(request, &bytes)?,
                    None => false,
                };
                self.scripts_ran(ran)?;
            }
            Msg::ScriptEnd { request } => {
                let ran = match self.current.as_mut() {
                    Some(p) => p.script_end(request)?,
                    None => false,
                };
                self.scripts_ran(ran)?;
            }
            Msg::ScriptFailed { request } => {
                let ran = match self.current.as_mut() {
                    Some(p) => p.script_failed(request)?,
                    None => false,
                };
                self.scripts_ran(ran)?;
            }
            Msg::Viewport {
                width,
                height,
                scale,
            } => {
                self.view = page::View::new(width, height, scale);
                if let Some(p) = self.current.as_mut() {
                    p.settle();
                }
                self.paint()?;
            }
            Msg::Input {
                kind,
                x,
                y,
                negative,
                delta,
                ..
            } => self.input(kind, x, y, negative, delta)?,
            _ => return Err(RunError::Protocol("unexpected message")),
        }
        Ok(None)
    }

    /// `Input`: a click follows a link (a `javascript:` URL runs in the
    /// page), a scroll moves the viewport.
    fn input(
        &mut self,
        kind: u64,
        x: u64,
        y: u64,
        negative: bool,
        delta: u64,
    ) -> Result<(), RunError> {
        let (Some(p), Some(v)) = (self.current.as_mut(), self.view) else {
            return Ok(());
        };
        match kind {
            // A click: hit-test, and follow a link. A `javascript:` URL the
            // page drew is the page's own to run (HTML "navigate": it is
            // evaluated in the page, phase-7.md item 7.15), never a
            // navigation for the kernel.
            0 => {
                if let Some(url) = p.click(x, y) {
                    if page::scripts::is_javascript_url(&url) {
                        let ran = p.follow_javascript_url(&url)?;
                        self.scripts_ran(ran)?;
                    } else {
                        lock(&self.link).send(&Msg::Navigate {
                            url: url.into_bytes(),
                        })?;
                    }
                }
            }
            // A scroll: move and paint again.
            1 => {
                let before = p.scroll;
                p.scroll_by(negative, delta);
                if p.scroll != before {
                    send_list(self.list, p, v, self.fonts, &mut self.cache)?;
                }
            }
            // A key: nothing in this phase.
            _ => {}
        }
        Ok(())
    }

    /// The event loop's turn: what the scripts have due runs, and the page
    /// is painted again if they changed it.
    fn turn(&mut self) -> Result<(), RunError> {
        let Some(p) = self.current.as_mut() else {
            return Ok(());
        };
        let ran = p.tick()?;
        self.scripts_ran(ran)
    }
}

/// The graphical renderer (phase-5.md item 5.20, `page`; phase-7.md item
/// 7.17): take committed documents and the kernel's `Viewport` and `Input`;
/// for a document, send `Title` to the kernel when the title changes and
/// write a display list to the GPU process (`list`) for every viewport,
/// scroll, document and change a script makes; run the document's scripts
/// and the event loop that keeps them running; for a click on a link, send
/// `Navigate` (or run its `javascript:` URL). A script (kind 1) runs as in
/// [`run`]. Returns the number of scripts run.
///
/// The socket is owned: a script that reads `document.cookie` waits for the
/// kernel's answer in the middle of its own run, so the page's natives and
/// this loop share it ([`page::link`]). A reader that returns `WouldBlock`
/// or `TimedOut` lets the loop's timers run while it waits.
pub fn run_graphics<R: Read + Send + 'static, W: Write + Send + 'static, L: Write>(
    r: R,
    w: W,
    list: &mut L,
    fonts: &page::fonts::Fonts,
) -> Result<usize, RunError> {
    run_graphics_with(r, w, list, fonts, &mut || Box::new(SystemClock::new()))
}

/// [`run_graphics`] with the page clocks `make_clock` makes, one per
/// document (a test's clock moves when the test says).
pub fn run_graphics_with<R: Read + Send + 'static, W: Write + Send + 'static, L: Write>(
    r: R,
    w: W,
    list: &mut L,
    fonts: &page::fonts::Fonts,
    make_clock: &mut dyn FnMut() -> Box<dyn Clock>,
) -> Result<usize, RunError> {
    let mut g = Graphics {
        link: Link::shared(r, w),
        list,
        fonts,
        make_clock,
        current: None,
        view: None,
        cache: page::frame::MaskCache::default(),
        shown_title: None,
        sheets: std::collections::HashMap::new(),
    };
    loop {
        g.turn()?;
        let polled = lock(&g.link).poll();
        let m = match polled {
            Ok(Some(m)) => m,
            // Nothing yet: the next turn of the event loop.
            Ok(None) => continue,
            Err(RunError::Io(e)) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(0),
            Err(e) => return Err(e),
        };
        if let Some(n) = g.handle(m)? {
            return Ok(n);
        }
    }
}

/// Run a user script (kind 1): the body is JavaScript, run in an empty
/// document at `url`, with the kernel's cookie and storage messages behind
/// `document.cookie` and `localStorage`. What it queued to run at once
/// (microtasks, timers due now) runs; later timers do not. Returns 1.
fn run_user_script(
    link: &LinkHandle,
    url: &[u8],
    body: &[u8],
    clock: Box<dyn Clock>,
) -> Result<usize, RunError> {
    let mut scripts = page::scripts::Scripts::empty(url, Arc::clone(link), clock)?;
    scripts.run_source(&String::from_utf8_lossy(body))?;
    scripts.tick()?;
    Ok(1)
}

#[cfg(test)]
mod tests {
    use super::{Msg, RunError, run};
    use clazel_ipc::message::codec::encode_framed;
    use std::io::{Cursor, Write};
    use std::sync::{Arc, Mutex};

    /// A writer the test can read after the renderer owns it.
    #[derive(Clone, Default)]
    struct Shared(Arc<Mutex<Vec<u8>>>);

    impl Write for Shared {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            if let Ok(mut v) = self.0.lock() {
                v.extend_from_slice(buf);
            }
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    impl Shared {
        fn bytes(&self) -> Vec<u8> {
            self.0.lock().map(|v| v.clone()).unwrap_or_default()
        }
    }

    fn frames(msgs: &[Msg]) -> Vec<u8> {
        msgs.iter()
            .flat_map(|m| encode_framed(m).unwrap_or_default())
            .collect()
    }

    /// The frames that commit `body` of `kind` at a fixed URL, the body in
    /// pieces of `piece` octets.
    fn commit(kind: u64, body: &[u8], piece: usize) -> Vec<Msg> {
        let mut m = vec![Msg::Commit {
            url: b"https://a.example/".to_vec(),
            content_type: Vec::new(),
            kind,
        }];
        m.extend(
            body.chunks(piece.max(1))
                .map(|c| Msg::Body { bytes: c.to_vec() }),
        );
        m.push(Msg::BodyEnd);
        m
    }

    /// Run a script against the kernel's `replies`; the frames it sent.
    fn exchange(script: &str, replies: Vec<Msg>) -> Result<Vec<u8>, RunError> {
        let mut input = commit(1, script.as_bytes(), 3);
        input.extend(replies);
        let sent = Shared::default();
        run(Cursor::new(frames(&input)), sent.clone())?;
        Ok(sent.bytes())
    }

    #[test]
    fn a_read_waits_for_its_answer_and_a_write_does_not() -> Result<(), RunError> {
        let sent = exchange(
            "document.cookie = 'a=1'; document.cookie; localStorage.clear();",
            vec![Msg::CookieValue {
                cookie_string: b"a=1".to_vec(),
            }],
        )?;
        assert_eq!(
            sent,
            frames(&[
                Msg::CookieSet {
                    cookie_string: b"a=1".to_vec()
                },
                Msg::CookieGet,
                Msg::StorageClear
            ])
        );
        Ok(())
    }

    #[test]
    fn set_item_is_followed_by_a_length_barrier() -> Result<(), RunError> {
        // Success: one answer, to the barrier.
        let ok = exchange(
            "localStorage.setItem('k', 'v'); localStorage.getItem('k');",
            vec![
                Msg::StorageLengthValue { length: 1 },
                Msg::StorageValue {
                    value: Some(b"v".to_vec()),
                },
            ],
        )?;
        let set = Msg::StorageSetItem {
            key: b"k".to_vec(),
            value: b"v".to_vec(),
        };
        assert_eq!(
            ok,
            frames(&[
                set,
                Msg::StorageLength,
                Msg::StorageGetItem { key: b"k".to_vec() }
            ])
        );
        // Failure: the `setItem` error, then the barrier's answer, which the
        // next read must not mistake for its own.
        let failed = exchange(
            "try { localStorage.setItem('k', 'v'); } catch (e) {} localStorage.getItem('k');",
            vec![
                Msg::Error { code: 1 },
                Msg::StorageLengthValue { length: 0 },
                Msg::StorageValue { value: None },
            ],
        );
        assert!(failed.is_ok());
        Ok(())
    }

    #[test]
    fn a_script_reads_every_storage_member() -> Result<(), RunError> {
        let sent = exchange(
            "localStorage.key(0); localStorage.length; localStorage.removeItem('k');",
            vec![
                Msg::StorageValue {
                    value: Some(b"k".to_vec()),
                },
                Msg::StorageLengthValue { length: 1 },
            ],
        )?;
        assert_eq!(
            sent,
            frames(&[
                Msg::StorageKey { index: 0 },
                Msg::StorageLength,
                Msg::StorageRemoveItem { key: b"k".to_vec() }
            ])
        );
        Ok(())
    }

    #[test]
    fn a_document_is_displayed_and_the_renderer_waits_for_the_next() -> Result<(), RunError> {
        // Item 4.13: each document goes through the pipeline. No content
        // type: the first is sniffed as HTML, the empty one as text.
        let mut input = vec![Msg::Error { code: 5 }];
        input.extend(commit(0, b"<title>T</title><p>page <a href=b>x</a></p>", 4));
        input.extend(commit(0, b"", 4));
        let sent = Shared::default();
        assert_eq!(run(Cursor::new(frames(&input)), sent.clone())?, 0);
        assert_eq!(
            sent.bytes(),
            frames(&[
                Msg::Display {
                    title: b"T".to_vec(),
                    text: b"page x[1]".to_vec(),
                    links: vec![b"https://a.example/b".to_vec()],
                },
                Msg::Display {
                    title: Vec::new(),
                    text: Vec::new(),
                    links: Vec::new(),
                }
            ])
        );
        Ok(())
    }

    #[test]
    fn protocol_violations_stop_the_script() {
        assert!(matches!(
            exchange("document.cookie", vec![]),
            Err(RunError::Io(_))
        ));
        // A document whose body does not end.
        let mut unended = commit(0, b"x", 1);
        unended.pop();
        unended.push(Msg::CookieValue {
            cookie_string: Vec::new(),
        });
        assert!(matches!(
            run(Cursor::new(frames(&unended)), Shared::default()),
            Err(RunError::Protocol(_))
        ));
        // Phase 2's line format is gone: a body that is not JavaScript is a
        // script that throws, which is reported (to the host's log), not a
        // reason for the renderer to stop. It sent nothing.
        assert!(matches!(exchange("cookie-get\nfly", vec![]), Ok(sent) if sent.is_empty()));
        let not_commit = Cursor::new(frames(&[Msg::CookieGet]));
        assert!(matches!(
            run(not_commit, Shared::default()),
            Err(RunError::Protocol(_))
        ));
        let huge = Cursor::new(vec![0xff, 0xff, 0xff, 0xff]);
        assert!(matches!(
            run(huge, Shared::default()),
            Err(RunError::Protocol(_))
        ));
    }
}
