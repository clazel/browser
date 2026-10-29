//! The renderer stub (phase-2.md item 2.15).
//!
//! The binary's first act is [`sandbox::enter`], before it reads a byte;
//! then it reads frames from its socket (standard input, with the same
//! socket as standard output) and waits for a committed document: a
//! `Commit`, its `Body` frames and `BodyEnd` (phase-4.md item 4.12).
//!
//! - Kind 1, a user script (the Phase 2 path): it runs the script in the
//!   body ([`script`]): for each operation it sends the renderer-to-kernel
//!   message and reads the kernel's reply. It prints nothing about the
//!   results: the host shell sees every request and reply on the socket and
//!   prints them, so the renderer needs no channel besides the one the
//!   kernel also reads. It exits when the script is done; the host sees the
//!   socket close.
//! - Kind 0, a document: **a stub until item 4.13** (the document pipeline:
//!   content type, encoding, the HTML parser and the text layout). It sends
//!   one `Display` whose title is the committed URL and whose text and links
//!   are empty, then waits for the next document (a same-origin navigation
//!   commits into the same renderer). The socket closing while it waits is
//!   the end of the tab, not an error.
//!
//! An `Error` while it waits (a navigation that failed, item 3.7) changes
//! nothing: the renderer keeps its document and waits on.

pub mod escape;
pub mod hostile;
pub mod sandbox;
pub mod script;

use std::fmt;
use std::io::{self, Read, Write};

use clazel_ipc::frame::codec::payload_length;
use clazel_ipc::message::codec::{Msg, decode_framed, encode_framed};
use script::Op;

/// Why the renderer stopped.
#[derive(Debug)]
pub enum RunError {
    /// The socket failed or closed.
    Io(io::Error),
    /// The kernel sent something the protocol does not allow here.
    Protocol(&'static str),
    /// The script in the `Commit` is not a script.
    Script(script::ScriptError),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::Io(e) => write!(f, "socket: {e}"),
            RunError::Protocol(why) => write!(f, "protocol: {why}"),
            RunError::Script(e) => write!(f, "script line {}: {}", e.line, e.reason),
        }
    }
}

impl From<io::Error> for RunError {
    fn from(e: io::Error) -> Self {
        RunError::Io(e)
    }
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

/// Wait for the next committed document: skip `Error`s, take a `Commit`,
/// then its `Body` frames up to `BodyEnd`. `None` if the socket closes
/// before a `Commit`.
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

fn send<W: Write>(w: &mut W, m: &Msg) -> Result<(), RunError> {
    let frame = encode_framed(m).ok_or(RunError::Protocol("message over MAX_FRAME"))?;
    w.write_all(&frame)?;
    w.flush()?;
    Ok(())
}

/// Take committed documents until a script (kind 1) is run or the socket
/// closes: a document (kind 0) is displayed, a script's operations are each
/// sent and their replies read. Returns the number of operations run.
pub fn run<R: Read, W: Write>(r: &mut R, w: &mut W) -> Result<usize, RunError> {
    loop {
        let Some(doc) = next_document(r)? else {
            return Ok(0);
        };
        match doc.kind {
            1 => return run_script(r, w, &doc.body),
            0 => {
                // Stub until item 4.13 (the renderer's document pipeline):
                // the title is the committed URL, and there is no text and
                // no link yet.
                send(
                    w,
                    &Msg::Display {
                        title: doc.url,
                        text: Vec::new(),
                        links: Vec::new(),
                    },
                )?;
            }
            _ => return Err(RunError::Protocol("unknown document kind")),
        }
    }
}

/// Run a script: send each operation and read its reply.
fn run_script<R: Read, W: Write>(r: &mut R, w: &mut W, script: &[u8]) -> Result<usize, RunError> {
    let ops = script::parse(script).map_err(RunError::Script)?;
    for op in &ops {
        send(w, &op.to_message())?;
        match op {
            Op::CookieGet | Op::StorageGet(_) | Op::StorageKey(_) | Op::StorageLength => {
                read_message(r)?;
            }
            Op::StorageSet(..) => {
                send(w, &Msg::StorageLength)?;
                if matches!(read_message(r)?, Msg::Error { .. }) {
                    read_message(r)?;
                }
            }
            Op::CookieSet(_) | Op::StorageRemove(_) | Op::StorageClear => {}
        }
    }
    Ok(ops.len())
}

#[cfg(test)]
mod tests {
    use super::{Msg, RunError, encode_framed, run};
    use std::io::Cursor;

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
        let mut sent = Vec::new();
        run(&mut Cursor::new(frames(&input)), &mut sent)?;
        Ok(sent)
    }

    #[test]
    fn a_read_waits_for_its_answer_and_a_write_does_not() -> Result<(), RunError> {
        let sent = exchange(
            "cookie-set a=1\ncookie-get\nstorage-clear",
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
            "storage-set k v\nstorage-get k",
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
            "storage-set k v\nstorage-get k",
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
    fn a_document_is_displayed_and_the_renderer_waits_for_the_next() -> Result<(), RunError> {
        // Stub until item 4.13: the title is the URL, no text, no links.
        let mut input = vec![Msg::Error { code: 5 }];
        input.extend(commit(0, b"<p>page</p>", 4));
        input.extend(commit(0, b"", 4));
        let mut sent = Vec::new();
        assert_eq!(run(&mut Cursor::new(frames(&input)), &mut sent)?, 0);
        let shown = Msg::Display {
            title: b"https://a.example/".to_vec(),
            text: Vec::new(),
            links: Vec::new(),
        };
        assert_eq!(
            sent,
            frames(&[
                shown,
                Msg::Display {
                    title: b"https://a.example/".to_vec(),
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
            exchange("cookie-get", vec![]),
            Err(RunError::Io(_))
        ));
        // A document whose body does not end.
        let mut unended = commit(0, b"x", 1);
        unended.pop();
        unended.push(Msg::CookieValue {
            cookie_string: Vec::new(),
        });
        assert!(matches!(
            run(&mut Cursor::new(frames(&unended)), &mut Vec::new()),
            Err(RunError::Protocol(_))
        ));
        assert!(matches!(
            exchange("nonsense", vec![]),
            Err(RunError::Script(_))
        ));
        let mut not_commit = Cursor::new(frames(&[Msg::CookieGet]));
        assert!(matches!(
            run(&mut not_commit, &mut Vec::new()),
            Err(RunError::Protocol(_))
        ));
        let mut huge = Cursor::new(vec![0xff, 0xff, 0xff, 0xff]);
        assert!(matches!(
            run(&mut huge, &mut Vec::new()),
            Err(RunError::Protocol(_))
        ));
    }
}
