//! The renderer stub (phase-2.md item 2.15).
//!
//! The binary's first act is [`sandbox::enter`], before it reads a byte;
//! then it reads frames from its socket (standard input, with the same
//! socket as standard output), waits for a `Commit`, and runs the script in
//! it ([`script`]): for each operation it sends the renderer-to-kernel
//! message and reads the kernel's reply. It prints nothing about the
//! results: the host shell sees every request and reply on the socket and
//! prints them, so the renderer needs no channel besides the one the kernel
//! also reads. It exits when the script is done; the host sees the socket
//! close.

pub mod escape;
pub mod hostile;
pub mod launch;
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

fn send<W: Write>(w: &mut W, m: &Msg) -> Result<(), RunError> {
    let frame = encode_framed(m).ok_or(RunError::Protocol("message over MAX_FRAME"))?;
    w.write_all(&frame)?;
    w.flush()?;
    Ok(())
}

/// Wait for `Commit`, then run its script: send each operation and read its
/// reply. Returns the number of operations run.
pub fn run<R: Read, W: Write>(r: &mut R, w: &mut W) -> Result<usize, RunError> {
    let Msg::Commit { script, .. } = read_message(r)? else {
        return Err(RunError::Protocol("expected Commit first"));
    };
    let ops = script::parse(&script).map_err(RunError::Script)?;
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

    fn commit(script: &str) -> Msg {
        Msg::Commit {
            url: b"https://a.example/".to_vec(),
            script: script.as_bytes().to_vec(),
        }
    }

    /// Run a script against the kernel's `replies`; the frames it sent.
    fn exchange(script: &str, replies: Vec<Msg>) -> Result<Vec<u8>, RunError> {
        let mut input = vec![commit(script)];
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
    fn protocol_violations_stop_the_script() {
        assert!(matches!(
            exchange("cookie-get", vec![]),
            Err(RunError::Io(_))
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
