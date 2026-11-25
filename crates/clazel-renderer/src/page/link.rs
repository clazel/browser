//! The renderer's link to the kernel while a page's scripts run (phase-7.md
//! item 7.17): one socket, shared by the renderer's loop and by the natives
//! a script calls.
//!
//! A script's `document.cookie` and `localStorage` are requests that wait for
//! the kernel's answer in the middle of the script (Phase 2's messages,
//! unchanged), so the native that makes one must read the socket while the
//! renderer's loop is somewhere above it on the stack. Both hold the same
//! [`LinkHandle`]; a native holds the lock only for one exchange, and the loop
//! never holds it while a script runs.
//!
//! **Other messages while a native waits.** The kernel does not stop sending
//! because the renderer waits (a `Viewport`, a `StyleBody`, an `Input`): any
//! message that is not the awaited answer is kept in the link's inbox, in
//! order, and the loop reads the inbox before the socket.
//!
//! **A socket that can say "not yet".** The reader may return
//! `WouldBlock` or `TimedOut` (a read timeout on the socket, set before the
//! sandbox is entered: the renderer cannot make a thread or a `poll` call
//! after it). A frame read that is interrupted that way keeps the bytes it
//! has: the next call goes on from there. [`Link::poll`] then answers `None`,
//! and the loop uses the time to run its timers.

use std::collections::VecDeque;
use std::io::{self, Read, Write};
use std::sync::{Arc, Mutex};

use clazel_ipc::frame::codec::payload_length;
use clazel_ipc::message::codec::{Msg, decode_framed, encode_framed};

use crate::RunError;

/// The link, shared.
pub type LinkHandle = Arc<Mutex<Link>>;

/// How many messages may wait in the inbox: more than any answer needs, and a
/// bound on what a kernel that talks over a waiting native can make the
/// renderer hold.
const MAX_INBOX: usize = 4096;

/// The socket, and what was read from it and not yet used.
pub struct Link {
    r: Box<dyn Read + Send>,
    w: Box<dyn Write + Send>,
    /// Bytes of a frame still arriving.
    pending: Vec<u8>,
    /// Whole messages read while a native waited.
    inbox: VecDeque<Msg>,
    /// The first failure of a send or a read made by a native, which the
    /// loop reports when it gets control back.
    failed: Option<io::ErrorKind>,
}

impl Link {
    /// A link over `r` and `w`.
    pub fn new(r: impl Read + Send + 'static, w: impl Write + Send + 'static) -> Link {
        Link {
            r: Box::new(r),
            w: Box::new(w),
            pending: Vec::new(),
            inbox: VecDeque::new(),
            failed: None,
        }
    }

    /// A shared link over `r` and `w`.
    pub fn shared(r: impl Read + Send + 'static, w: impl Write + Send + 'static) -> LinkHandle {
        Arc::new(Mutex::new(Link::new(r, w)))
    }

    /// Sends `m`.
    ///
    /// # Errors
    /// The socket failed, or the message does not fit a frame.
    pub fn send(&mut self, m: &Msg) -> Result<(), RunError> {
        let frame = encode_framed(m).ok_or(RunError::Protocol("message over MAX_FRAME"))?;
        self.w.write_all(&frame)?;
        self.w.flush()?;
        Ok(())
    }

    /// The next whole message: from the inbox, else from the socket. `None`
    /// if the socket has no whole message now (its read timed out).
    ///
    /// # Errors
    /// The socket failed or closed (`UnexpectedEof`), or sent a frame over
    /// `MAX_FRAME` or one that does not decode.
    pub fn poll(&mut self) -> Result<Option<Msg>, RunError> {
        if let Some(m) = self.inbox.pop_front() {
            return Ok(Some(m));
        }
        self.read_message()
    }

    /// Reads from the socket until one whole message is there.
    fn read_message(&mut self) -> Result<Option<Msg>, RunError> {
        loop {
            if let Some((header, _)) = self.pending.split_first_chunk::<4>() {
                let len =
                    payload_length(header).ok_or(RunError::Protocol("frame over MAX_FRAME"))?;
                let total = len.saturating_add(4);
                if self.pending.len() >= total {
                    let rest = self.pending.split_off(total);
                    let frame = core::mem::replace(&mut self.pending, rest);
                    return decode_framed(&frame)
                        .map(Some)
                        .ok_or(RunError::Protocol("frame does not decode"));
                }
            }
            // What the frame still needs, at most one read's worth.
            let want = match self.pending.split_first_chunk::<4>() {
                Some((header, _)) => payload_length(header)
                    .unwrap_or(0)
                    .saturating_add(4)
                    .saturating_sub(self.pending.len()),
                None => 4usize.saturating_sub(self.pending.len()),
            };
            let mut buf = vec![0u8; want.clamp(1, 64 * 1024)];
            match self.r.read(&mut buf) {
                Ok(0) => {
                    return Err(RunError::Io(io::Error::from(io::ErrorKind::UnexpectedEof)));
                }
                Ok(n) => self
                    .pending
                    .extend_from_slice(buf.get(..n).unwrap_or_default()),
                Err(e)
                    if matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                    ) =>
                {
                    return Ok(None);
                }
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(RunError::Io(e)),
            }
        }
    }

    /// The first failure a native met (see [`Link::note_failure`]), taken.
    pub fn failure(&mut self) -> Option<io::ErrorKind> {
        self.failed.take()
    }

    /// Sends `request` and waits for the first message `is_answer` accepts,
    /// keeping the others in the inbox. A failure is kept for
    /// [`Link::failure`] and answers `None`.
    pub fn call(&mut self, request: &Msg, is_answer: fn(&Msg) -> bool) -> Option<Msg> {
        if let Err(e) = self.send(request) {
            self.note_failure(&e);
            return None;
        }
        self.wait_for(is_answer)
    }

    /// Waits for the first message `is_answer` accepts; as [`Link::call`].
    pub fn wait_for(&mut self, is_answer: fn(&Msg) -> bool) -> Option<Msg> {
        loop {
            match self.read_message() {
                Ok(Some(m)) if is_answer(&m) => return Some(m),
                Ok(Some(m)) => {
                    if self.inbox.len() >= MAX_INBOX {
                        self.note_failure(&RunError::Protocol("too many messages while waiting"));
                        return None;
                    }
                    self.inbox.push_back(m);
                }
                Ok(None) => {}
                Err(e) => {
                    self.note_failure(&e);
                    return None;
                }
            }
        }
    }

    /// Keeps the first failure of a send or a read made on behalf of a
    /// script, for [`Link::failure`].
    pub fn note_failure(&mut self, e: &RunError) {
        let kind = match e {
            RunError::Io(e) => e.kind(),
            _ => io::ErrorKind::InvalidData,
        };
        self.failed.get_or_insert(kind);
    }
}

/// Locks the link; a poisoned lock (a native panicked while holding it) is
/// still the link.
pub fn lock(link: &LinkHandle) -> std::sync::MutexGuard<'_, Link> {
    link.lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}
