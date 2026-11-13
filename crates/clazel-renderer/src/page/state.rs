//! The states of the graphical pipeline (phase-5.md item 5.20), their
//! invariants, and the contracts of the steps over them.
//!
//! - **The wait for linked style sheets** ([`SheetWait`], `sheets.rs`):
//!   HTML's render-blocking style sheets. Steps:
//!   - `SheetWait::start(sources, fetch)`: the document's style sources
//!     (item 5.8) with every `<link rel=stylesheet>` still to fetch. With
//!     `fetch` false (today: item 5.19's `FetchStyle` is not wired), every
//!     pending link is failed at once, as a fetch that failed would be
//!     ("success" false, HTML §4.6.8.23), so the wait starts ready. With
//!     `fetch` true, the indices of the pending links whose `media` matches
//!     are the requests to send. Contract: the wait is ready exactly when no
//!     requested link is unanswered; a link whose `media` does not match is
//!     never waited for.
//!   - `SheetWait::answer(index, response)`: the kernel's answer for one
//!     request (a body, or a failure, which includes the kernel's timeout).
//!     Contract: that link is answered (loaded or failed, by
//!     `Sources::link_loaded`) and leaves the pending set; an index not
//!     pending changes nothing.
//!   - `SheetWait::ready(&self)`: no request is unanswered. Rendering
//!     waits for it.
//!   - Invariant ([`SheetWait::invariant`]): every pending index names a
//!     link of the sources whose state is `Pending`, each at most once.
//! - **The scroll** (`mod.rs`): `clamp_scroll(want, page, viewport)`: the
//!   top of the viewport in the page, in device pixels. Contract: in `0 ..=
//!   max(0, page - viewport)`, and `want` itself when it is in that range.
//! - **The glyph masks the GPU process holds** ([`Masks`], `frame.rs`):
//!   which masks are live, under which ids, and how many coverage bytes
//!   they hold, so that every list keeps item 5.17a's limits (ids below
//!   `MAX_MASKS`, at most `MAX_MASK_BYTES` live). Steps:
//!   - `Masks::allocate(self, bytes) -> Option<(Masks, id)>`: a new mask of
//!     `bytes` coverage bytes. Contract: `None` when it would pass either
//!     limit; otherwise the id is below `MAX_MASKS` and not live, and the
//!     counts grow by one mask and `bytes`.
//!   - `Masks::release(self, id, bytes) -> Masks`: a mask is freed. Contract:
//!     the counts shrink by one mask and `bytes`, and the id may be given
//!     again.
//!   - Invariant ([`Masks::invariant`]): the live count is at most
//!     `MAX_MASKS` and the live bytes at most `MAX_MASK_BYTES`.
//! - **A list on the GPU process's socket** (`frame.rs`): `frame_bytes(list)
//!   -> Vec<u8>`: `clazel_gpu::channel::write_list`'s framing (a 4-byte
//!   little-endian length), then the encoded list. Contract:
//!   the length is the list's, which is at most `MAX_LIST_BYTES`, so a reader
//!   can refuse an oversized list from its first four bytes.

use clazel_displaylist::spec::{MAX_MASK_BYTES, MAX_MASKS};
use clazel_style::sources::Sources;

/// The wait for a document's linked style sheets.
#[derive(Debug, Clone)]
pub struct SheetWait {
    /// The document's style sources.
    pub sources: Sources,
    /// The indices (into `sources.sheets`) of the requests not yet answered.
    pub pending: Vec<usize>,
}

impl SheetWait {
    /// The invariant (see the module).
    pub fn invariant(&self) -> bool {
        let pending_links = self.sources.pending_links();
        let mut seen = self.pending.clone();
        seen.sort_unstable();
        seen.dedup();
        seen.len() == self.pending.len() && self.pending.iter().all(|i| pending_links.contains(i))
    }
}

/// The masks live in the GPU process: their count and coverage bytes, and
/// the ids freed for reuse.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Masks {
    /// How many are live.
    pub live: u32,
    /// Their coverage bytes.
    pub bytes: u64,
    /// The next id never given.
    pub next: u32,
    /// Ids freed, to give again.
    pub free: Vec<u32>,
}

impl Masks {
    /// The invariant: within item 5.17a's limits.
    pub fn invariant(&self) -> bool {
        u64::from(self.live) <= u64::try_from(MAX_MASKS).unwrap_or(u64::MAX)
            && self.bytes <= u64::try_from(MAX_MASK_BYTES).unwrap_or(u64::MAX)
            && u64::from(self.next) <= u64::try_from(MAX_MASKS).unwrap_or(u64::MAX)
    }
}
