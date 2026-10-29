//! Helpers shared by the kernel conformance tests: fake renderers that talk
//! to the exec kernel in frames.
//!
//! The kernel is driven by `clazel_kernel::exec::real_urls::step_real`: the
//! exec `step` with the real URL functions (item 2.13), proven equal to the
//! spec's `step` over `clazel_kernel::urls::real_urls()`. (Until item 2.13
//! these helpers used a test-only `TestUrls`, built on the same parser but
//! not proven equal to anything; it is gone.)

use clazel_ipc::frame::codec::payload_length;
use clazel_ipc::message::codec::{Msg, decode_framed, encode_framed};
use clazel_kernel::exec::real_urls::{RealFetch, step_real};
use clazel_kernel::exec::records::{EventRecord, OutputRecord, StateRecord, init_record};

/// The code points of a string.
pub fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// A committed document (phase-4.md item 4.12): the frames `Commit`, `Body`
/// ... and `BodyEnd` of one write, read back.
#[derive(Debug, PartialEq, Eq)]
pub struct Doc {
    /// The committed URL, UTF-8.
    pub url: Vec<u8>,
    /// The content type.
    pub content_type: Vec<u8>,
    /// 0 a document, 1 a user script.
    pub kind: u64,
    /// The `Body` frames' bytes, concatenated.
    pub body: Vec<u8>,
}

/// The messages in `bytes`, whole frames one after another; `None` if they
/// are not that.
pub fn split_frames(mut bytes: &[u8]) -> Option<Vec<Msg>> {
    let mut out = Vec::new();
    while !bytes.is_empty() {
        let len = payload_length(bytes.get(..4)?)?;
        let frame = bytes.get(..4usize.checked_add(len)?)?;
        out.push(decode_framed(frame)?);
        bytes = bytes.get(frame.len()..)?;
    }
    Some(out)
}

/// The document a write commits, if it is `Commit`, `Body` frames and
/// `BodyEnd`.
pub fn read_doc(msgs: Vec<Msg>) -> Option<Doc> {
    let mut it = msgs.into_iter();
    let Some(Msg::Commit {
        url,
        content_type,
        kind,
    }) = it.next()
    else {
        return None;
    };
    let mut body = Vec::new();
    loop {
        match it.next()? {
            Msg::Body { bytes } => body.extend_from_slice(&bytes),
            Msg::BodyEnd => break,
            _ => return None,
        }
    }
    it.next().is_none().then_some(Doc {
        url,
        content_type,
        kind,
        body,
    })
}

/// What the kernel sent, decoded.
#[derive(Debug, PartialEq, Eq)]
pub enum Out {
    /// A frame to a renderer, decoded.
    To(u64, Msg),
    /// A committed document to a renderer.
    Commit(u64, Doc),
    /// What the user is shown of a tab: the tab, the address line (the
    /// kernel's URL), the title, the text and the links.
    Show(u64, Vec<u32>, Vec<u8>, Vec<u8>, Vec<Vec<u8>>),
    /// A frame to a renderer that does not decode (a kernel bug).
    Garbled(u64),
    /// A renderer started.
    Spawn(u64),
    /// A renderer killed.
    Kill(u64),
    /// The kernel asked for connection `conn` to `host:port` (the TLS flag
    /// last).
    Connect(u64, Vec<u8>, u64, bool),
    /// The kernel wrote these octets to connection `conn`.
    Send(u64, Vec<u8>),
    /// The kernel closed connection `conn`.
    Close(u64),
}

/// The exec kernel, driven as the host shell would.
pub struct Kernel {
    /// The state, absent only while a step runs.
    pub state: Option<StateRecord>,
}

impl Kernel {
    /// A kernel before anything happens.
    pub fn new() -> Self {
        Self {
            state: Some(init_record::<RealFetch>()),
        }
    }

    /// One event; the outputs, decoded.
    pub fn event(&mut self, e: &EventRecord) -> Vec<Out> {
        let Some(s) = self.state.take() else {
            return Vec::new();
        };
        let (next, outputs) = step_real(s, e);
        self.state = Some(next);
        outputs
            .into_iter()
            .map(|o| match o {
                OutputRecord::ToRenderer { id, bytes } => match split_frames(&bytes) {
                    Some(msgs) if msgs.len() == 1 && !matches!(msgs.first(), Some(Msg::Commit { .. })) => {
                        msgs.into_iter().next().map_or(Out::Garbled(id), |m| Out::To(id, m))
                    }
                    Some(msgs) => read_doc(msgs).map_or(Out::Garbled(id), |d| Out::Commit(id, d)),
                    None => Out::Garbled(id),
                },
                OutputRecord::Spawn { id } => Out::Spawn(id),
                OutputRecord::Kill { id } => Out::Kill(id),
                OutputRecord::Connect {
                    conn,
                    host,
                    port,
                    tls,
                } => Out::Connect(conn, host, port, tls),
                OutputRecord::Send { conn, bytes } => Out::Send(conn, bytes),
                OutputRecord::Close { conn } => Out::Close(conn),
                OutputRecord::Show {
                    tab,
                    url,
                    title,
                    text,
                    links,
                } => Out::Show(tab, url, title, text, links),
            })
            .collect()
    }

    /// The user opens a tab with a script (the Phase 2 path, committed at
    /// once as kind 1); the id of its renderer, and what was sent.
    pub fn open_tab(&mut self, url: &str, script: &str) -> (Option<u64>, Vec<Out>) {
        let out = self.event(&EventRecord::OpenTab {
            url: code_points(url),
            script: Some(script.as_bytes().to_vec()),
        });
        let id = out.iter().find_map(|o| match o {
            Out::Spawn(id) => Some(*id),
            _ => None,
        });
        (id, out)
    }

    /// Renderer `id` sends `m`, framed by the IPC codec.
    pub fn send(&mut self, id: u64, m: &Msg) -> Vec<Out> {
        let bytes = encode_framed(m).unwrap_or_default();
        self.event(&EventRecord::FromRenderer { id, bytes })
    }
}
