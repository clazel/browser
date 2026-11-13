//! The wait for linked style sheets: the one seam item 5.19's `FetchStyle`
//! plugs into (phase-5.md item 5.20: "send a `FetchStyle` for each `<link
//! rel=stylesheet>` whose `media` matches, and wait for all to end or
//! fail").
//!
//! Sources: HTML §4.6.8.23 (`link` type `stylesheet`: "process this type of
//! linked resource", whose failure leaves no sheet) and §4.2.6 (`media`),
//! through `clazel-style`'s `Sources` (item 5.8).
//!
//! Contracts: `state.rs`. Today nothing is fetched: [`SheetWait::start`]
//! with `fetch` false answers every pending link as a failed fetch, so the
//! wait starts ready and the page renders with its `style` elements and
//! attributes only. Wiring 5.19 is: call `start` with `fetch` true, send a
//! `FetchStyle` for each index in `pending`, call [`SheetWait::answer`] for
//! each reply, and render when [`SheetWait::ready`].

use clazel_encoding::labels::spec::Encoding;
use clazel_style::sources::media::evaluate;
use clazel_style::sources::{Device, Response, Sources};

use super::state::SheetWait;

/// A failed fetch, as `link_loaded` reads one: "success" is false.
const FAILED: Response<'static> = Response {
    content_type: None,
    same_origin: false,
    ok: false,
    body: &[],
};

impl SheetWait {
    /// The wait for `sources`' pending links whose `media` matches
    /// `device`; with `fetch` false, every pending link is failed at once
    /// (`state.rs`'s contract). `encoding` is the document's.
    pub fn start(sources: Sources, device: Device, fetch: bool, encoding: Encoding) -> SheetWait {
        let mut w = SheetWait {
            sources,
            pending: Vec::new(),
        };
        let links = w.sources.pending_links();
        for i in links {
            let matches = w
                .sources
                .sheets
                .get(i)
                .is_some_and(|s| evaluate(&s.media, device));
            if fetch && matches {
                w.pending.push(i);
            } else {
                // Not fetched: a link whose media does not match is not
                // render-blocking, and with no fetch at all every link is
                // as a failed one.
                w.sources.link_loaded(i, FAILED, encoding);
            }
        }
        w
    }

    /// The kernel's answer for the request of link `index`: its response,
    /// or a failure (`None`) (`state.rs`'s contract).
    pub fn answer(&mut self, index: usize, response: Option<Response<'_>>, encoding: Encoding) {
        let Some(at) = self.pending.iter().position(|&i| i == index) else {
            return;
        };
        self.pending.remove(at);
        self.sources
            .link_loaded(index, response.unwrap_or(FAILED), encoding);
    }

    /// No request is unanswered: the page may render.
    pub fn ready(&self) -> bool {
        self.pending.is_empty()
    }
}
