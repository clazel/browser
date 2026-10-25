//! Helpers shared by the kernel conformance tests: fake renderers that talk
//! to the exec kernel in frames.
//!
//! The kernel is driven by `clazel_kernel::exec::real_urls::step_real`: the
//! exec `step` with the real URL functions (item 2.13), proven equal to the
//! spec's `step` over `clazel_kernel::urls::real_urls()`. (Until item 2.13
//! these helpers used a test-only `TestUrls`, built on the same parser but
//! not proven equal to anything; it is gone.)

use clazel_ipc::message::codec::{Msg, decode_framed, encode_framed};
use clazel_kernel::exec::real_urls::step_real;
use clazel_kernel::exec::records::{EventRecord, OutputRecord, StateRecord, init_record};

/// The code points of a string.
pub fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// What the kernel sent, decoded.
#[derive(Debug, PartialEq, Eq)]
pub enum Out {
    /// A frame to a renderer, decoded.
    To(u64, Msg),
    /// A frame to a renderer that does not decode (a kernel bug).
    Garbled(u64),
    /// A renderer started.
    Spawn(u64),
    /// A renderer killed.
    Kill(u64),
    /// The kernel asked for a URL to be fetched for a tab.
    Fetch(u64, Vec<u32>),
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
            state: Some(init_record()),
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
                OutputRecord::ToRenderer { id, bytes } => match decode_framed(&bytes) {
                    Some(m) => Out::To(id, m),
                    None => Out::Garbled(id),
                },
                OutputRecord::Spawn { id } => Out::Spawn(id),
                OutputRecord::Kill { id } => Out::Kill(id),
                OutputRecord::Fetch { tab, url } => Out::Fetch(tab, url),
            })
            .collect()
    }

    /// The user opens a tab; the id of its renderer, and what was sent.
    pub fn open_tab(&mut self, url: &str, script: &str) -> (Option<u64>, Vec<Out>) {
        let out = self.event(&EventRecord::OpenTab {
            url: code_points(url),
            script: script.as_bytes().to_vec(),
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
