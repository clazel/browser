//! The wait for linked style sheets: the one seam item 5.19's `FetchStyle`
//! plugs into (phase-5.md item 5.20: "send a `FetchStyle` for each `<link
//! rel=stylesheet>` whose `media` matches, and wait for all to end or
//! fail").
//!
//! Sources: HTML §4.6.8.23 (`link` type `stylesheet`: "process this type of
//! linked resource", whose failure leaves no sheet) and §4.2.6 (`media`),
//! through `clazel-style`'s `Sources` (item 5.8).
//!
//! Contracts: `state.rs`. `Page::load` starts the wait with fetches; the
//! renderer (`crate::run_graphics`) sends a `FetchStyle` for each index in
//! `pending`, gives each `StyleResponse`, `StyleBody` and `StyleEnd` (or
//! `StyleFailed`) to [`SheetWait::answer`], and renders when
//! [`SheetWait::ready`]. A sheet that never answers is failed by the kernel's
//! timeout (`StyleFailed` after 60 seconds, item 5.19), so the page renders
//! without it.

use clazel_encoding::labels::spec::Encoding;
use clazel_style::sources::media::evaluate;
use clazel_style::sources::{Device, Response, Sources};

use clazel_style::sources::Owner;
use clazel_url::url::record::ParsedUrl;

use super::state::SheetWait;

/// Whether `a` and `b` are same origin (HTML §7.1.1): both tuple origins
/// (`http`, `https`, `ws`, `wss`, `ftp`) with equal schemes, hosts and ports.
pub fn same_origin(a: &ParsedUrl, b: &ParsedUrl) -> bool {
    let tuple = |s: &[u32]| {
        ["http", "https", "ws", "wss", "ftp"]
            .iter()
            .any(|t| s.iter().copied().eq(t.chars().map(u32::from)))
    };
    tuple(&a.scheme)
        && a.scheme == b.scheme
        && a.port == b.port
        && match (&a.host, &b.host) {
            (Some(x), Some(y)) => x.serialize() == y.serialize(),
            _ => false,
        }
}

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

    /// The `href` of link `index`, if it is one.
    pub fn href(&self, index: usize) -> Option<Vec<u32>> {
        match &self.sources.sheets.get(index)?.owner {
            Owner::Link(l) => Some(l.href.clone()),
            Owner::Style => None,
        }
    }

    /// No request is unanswered: the page may render.
    pub fn ready(&self) -> bool {
        self.pending.is_empty()
    }
}
