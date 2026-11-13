//! The graphical pipeline (phase-5.md item 5.20): a committed document to
//! display lists on the GPU process's socket, and the renderer's answers to
//! `Viewport` and `Input`.
//!
//! Tier 0 glue, tested and not proven, like `pipeline.rs` (item 4.13), whose
//! steps 1 to 4 it reuses (content type, encodings, parse, base URL). Every
//! later step is a function of the crate that implements it:
//!
//! 5. collect the style sources in tree order (`clazel-style`, item 5.8:
//!    `style` elements, `<link rel=stylesheet>`, `style` attributes);
//! 6. wait for the linked sheets (`sheets.rs`, the seam for item 5.19);
//! 7. cascade under the user agent sheets (item 5.7) for a screen the
//!    viewport's size in CSS pixels;
//! 8. build the box tree (item 5.13);
//! 9. lay it out at the viewport's width (items 5.14 and 5.15) in the fonts
//!    the renderer read before it entered the sandbox (`fonts.rs`);
//! 10. paint it (item 5.16) at the viewport's scale;
//! 11. for each frame: the items that meet the viewport at the scroll
//!     offset, offset by it, with the glyph masks (item 5.17) the GPU
//!     process does not hold yet, encoded (item 5.17a) and written to the
//!     GPU process's socket (`frame.rs`);
//! 12. `Title` to the kernel when the title changes.
//!
//! On `Viewport`: steps 7 to 11 again. On `Input`: a scroll moves the
//! viewport within the page and paints again (step 11); a click is
//! hit-tested against the links' regions and sends `Navigate`.
//!
//! # Modelling choices (ours, each listed)
//!
//! - **A sibling of `pipeline.rs`**: the plan says "`pipeline.rs`
//!   extended"; the text path of item 4.13 stays as it is (item 5.18: both
//!   display paths stay until 5.26), and this module calls its steps.
//! - **`text/plain`** is the document `<!DOCTYPE html><pre>` and the text,
//!   escaped, parsed by the HTML parser, so it is one `pre` block styled by
//!   the user agent sheet (the plan); a line feed is put after `<pre>`, which
//!   the parser drops, so a leading line feed of the text stays. **Other
//!   types and failures** (an encoding without a decoder) are a `p` holding
//!   the notice item 4.13 shows, drawn the same way.
//! - **The CSS viewport** is the device viewport divided by the scale,
//!   rounded down; the scale is 1 or 2 (`Viewport`).
//! - **Before the first `Viewport`**, and while it is 0 by 0 (a tab the host
//!   never sized, item 5.18), nothing is painted: there is nowhere to draw.
//! - **The title** is HTML's `document.title` for an HTML document: the
//!   first `title` element's child text, "strip and collapse ASCII
//!   whitespace", cut to item 4.13's `MAX_TITLE` characters; it is sent
//!   whenever it differs from the last one sent, so once per document at
//!   most.
//! - **Scrolling** is vertical: `Input`'s delta moves the viewport's top,
//!   clamped to the page (its extent's height in device pixels). A key does
//!   nothing in this phase.
//! - **A click** goes to the last hit region, in paint order, holding the
//!   point (the topmost); one with no URL (the URL parser failed) does
//!   nothing.
//! - **Fonts**: the files the host names with `--font PATH` are read before
//!   the sandbox is entered (`main.rs`); their bytes live as long as the
//!   process. A file that is not a TrueType face is skipped. With no face,
//!   layout uses `BoxFont`'s em boxes and text is not drawn (listed).
//! - **Glyph masks** are kept by the GPU process across lists, under ids
//!   this module gives (`state::Masks`): a mask is uploaded once, the first
//!   frame that draws it; when a frame's new masks would pass item 5.17a's
//!   limits, every live mask that frame does not draw is freed first; glyphs
//!   still beyond the limits are not drawn.
//! - **Frames are bounded**: at most half of 5.17a's item limit goes to
//!   fills, clips and glyph draws (the rest to masks); a frame that would
//!   need more stops there, with its clip balanced.
//! - **The socket's framing** is ours (the GPU process's reader is not
//!   built yet): a 4-byte big-endian length, then one encoded list.
//! - **The list socket is not wired yet**: the host must create a socket
//!   pair and hand the renderer its end, which needs a new `clazel-sys` call
//!   to clear close-on-exec and to adopt the descriptor (item 5.18's plan;
//!   `clazel-sys` is audited and outside this item). Until then
//!   `crate::run_graphics` takes any writer, and the binary runs the text
//!   path.

pub mod fonts;
pub mod frame;
pub mod sheets;
pub mod state;

use clazel_dom::exec::{Arena, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_encoding::labels::spec::Encoding;
use clazel_html::sniff::exec::{sniff, transport_encoding};
use clazel_layout::boxes::build;
use clazel_layout::flow::{Viewport as CssViewport, layout};
use clazel_layout::paint::{DisplayList, paint};
use clazel_mime::mime_type::groups::is_html_mime_type;
use clazel_mime::mime_type::serialize::serialize;
use clazel_style::cascade::{cascade_with, ua};
use clazel_style::sources::{Device, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_url::url::record::ParsedUrl;

use crate::pipeline::{
    Encodings, MAX_TITLE, NotParsed, base_url, code_points, computed_type, encoding_name,
    is_essence, parse_html, string_of,
};
use fonts::{Fonts, Text};
use state::SheetWait;

/// The largest viewport side taken, in device pixels: the GPU process's
/// (`clazel-gpu`'s `MAX_VIEWPORT_SIDE`).
pub const MAX_SIDE: u32 = 8192;

/// The viewport the kernel gave (`Viewport`), checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct View {
    /// Width in device pixels, 1 to [`MAX_SIDE`].
    pub width: u32,
    /// Height in device pixels, 1 to [`MAX_SIDE`].
    pub height: u32,
    /// Device pixels per CSS pixel, 1 or 2.
    pub scale: u32,
}

impl View {
    /// The viewport of a `Viewport` message: `None` for a 0 by 0 one (or any
    /// side 0: nowhere to draw); sides above [`MAX_SIDE`] are cut to it, and
    /// a scale other than 2 is 1 (the schema leaves it to the receiver).
    pub fn new(width: u64, height: u64, scale: u64) -> Option<View> {
        let side = |v: u64| {
            u32::try_from(v.min(u64::from(MAX_SIDE)))
                .ok()
                .filter(|&v| v > 0)
        };
        Some(View {
            width: side(width)?,
            height: side(height)?,
            scale: if scale == 2 { 2 } else { 1 },
        })
    }

    /// The CSS viewport: the device one divided by the scale, rounded down.
    fn css(self) -> (u32, u32) {
        let s = self.scale.max(1);
        (
            self.width.checked_div(s).unwrap_or(0),
            self.height.checked_div(s).unwrap_or(0),
        )
    }
}

/// The top of a viewport `viewport` high scrolled to `want` in a page
/// `page` high, all in device pixels (`state.rs`'s contract).
pub fn clamp_scroll(want: i64, page: i64, viewport: i64) -> i64 {
    want.clamp(0, page.saturating_sub(viewport).max(0))
}

/// A page laid out and painted for one viewport.
struct Laid {
    list: DisplayList,
    /// The page's height, in device pixels.
    height: i64,
}

/// A committed document, as the graphical pipeline holds it.
pub struct Page {
    arena: Arena,
    base: Option<ParsedUrl>,
    wait: SheetWait,
    /// HTML's `document.title`, cut to `MAX_TITLE` characters.
    pub title: String,
    laid: Option<Laid>,
    view: Option<View>,
    /// The viewport's top in the page, in device pixels.
    pub scroll: i64,
}

/// `text` with `&` and `<` escaped, for a document made from it.
fn escape(text: &str) -> String {
    text.replace('&', "&amp;").replace('<', "&lt;")
}

/// The HTML document `source` at `url`, parsed (for `text/plain` and the
/// notices: `mod.rs`).
fn made(source: &str, url: &[u32]) -> Arena {
    let input: Vec<u32> = source.chars().map(u32::from).collect();
    parse_real(&Encodings, &input, url.to_vec(), false, false)
        .0
        .arena
}

/// A notice, drawn: one `p`.
fn notice(text: &str, url: &[u32]) -> Arena {
    made(&format!("<!DOCTYPE html><p>{}", escape(text)), url)
}

/// HTML's `document.title` for an HTML document: "the first title element
/// in the document (in tree order)", its child text content with ASCII
/// whitespace stripped and collapsed; cut to `MAX_TITLE` characters.
pub fn title_of(arena: &Arena) -> String {
    let n = arena.len();
    let mut stack: Vec<usize> = vec![0];
    let mut title: Option<usize> = None;
    for _ in 0..n.saturating_add(1) {
        let Some(id) = stack.pop() else { break };
        if id >= n {
            continue;
        }
        if let ExecKind::Element {
            namespace: Some(Namespace::Html),
            local_name,
            ..
        } = arena.kind(id)
            && local_name
                .iter()
                .copied()
                .eq("title".chars().map(u32::from))
        {
            title = Some(id);
            break;
        }
        stack.extend(arena.children(id).iter().rev());
    }
    let Some(t) = title else {
        return String::new();
    };
    let mut text = String::new();
    for &c in arena.children(t) {
        if let ExecKind::Text { data } = arena.kind(c) {
            text.push_str(&string_of(data).unwrap_or_default());
        }
    }
    // "strip and collapse ASCII whitespace".
    let collapsed = text
        .split(['\t', '\n', '\u{0C}', '\r', ' '])
        .filter(|w| !w.is_empty())
        .collect::<Vec<_>>()
        .join(" ");
    collapsed.chars().take(MAX_TITLE).collect()
}

impl Page {
    /// Steps 1 to 6 for the document committed at `url` with
    /// `content_type` and `body` (the module's pipeline).
    pub fn load(url: &[u8], content_type: &[u8], body: &[u8]) -> Page {
        let url_cps = code_points(url);
        let url_text = String::from_utf8_lossy(url).into_owned();
        let (supplied, computed) = computed_type(content_type, body);
        let transport = supplied.as_ref().and_then(transport_encoding);
        let (arena, encoding) = if is_html_mime_type(&computed) {
            match parse_html(body, transport, &url_cps) {
                Ok(p) => (p.arena, p.encoding),
                Err(NotParsed::Unsupported(e)) => (
                    notice(
                        &format!("encoding {} is not supported", encoding_name(e)),
                        &url_cps,
                    ),
                    Encoding::Utf8,
                ),
            }
        } else if is_essence(&computed, "text", "plain") {
            let (encoding, _) = sniff(body, transport);
            match clazel_encoding::hooks::decode::decode(body, encoding) {
                Some(text) => {
                    let s: String = text
                        .iter()
                        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
                        .collect();
                    (
                        made(&format!("<!DOCTYPE html><pre>\n{}", escape(&s)), &url_cps),
                        encoding,
                    )
                }
                None => (
                    notice(
                        &format!("encoding {} is not supported", encoding_name(encoding)),
                        &url_cps,
                    ),
                    Encoding::Utf8,
                ),
            }
        } else {
            let shown = string_of(&serialize(&computed)).unwrap_or_default();
            (
                notice(&format!("{shown} is not shown: {url_text}"), &url_cps),
                Encoding::Utf8,
            )
        };
        let base = base_url(&arena, &url_cps);
        let title = title_of(&arena);
        // Step 6: no fetch yet (item 5.19); the device only decides which
        // links would block.
        let wait = SheetWait::start(collect(&arena), Device::screen(0, 0), false, encoding);
        Page {
            arena,
            base,
            wait,
            title,
            laid: None,
            view: None,
            scroll: 0,
        }
    }

    /// Whether the page waits for no style sheet (step 6).
    pub fn ready(&self) -> bool {
        self.wait.ready()
    }

    /// Steps 7 to 10 for viewport `view`, in `fonts`.
    pub fn lay_out(&mut self, view: View, fonts: &Fonts) {
        self.view = Some(view);
        if !self.ready() {
            return;
        }
        let (cw, ch) = view.css();
        let device = Device::screen(cw, ch);
        let sheets = ua::sheets().for_document(&self.arena);
        let table = cascade_with(&sheets, &self.arena, &self.wait.sources, device);
        let tree = build(&self.arena, &table);
        let text = Text::of(fonts, &table.families);
        let px64 = |v: u32| i32::try_from(i64::from(v).saturating_mul(64)).unwrap_or(i32::MAX);
        let frags = layout(
            &tree,
            &self.arena,
            &table,
            &text,
            CssViewport {
                width: px64(cw),
                height: px64(ch),
            },
        );
        let list = paint(
            &frags,
            &tree,
            &self.arena,
            &table,
            &text,
            self.base.as_ref(),
            view.scale,
        );
        // The page's height: its extent's bottom, in device pixels, rounded up.
        let bottom = i64::from(frags.extent.bottom()).saturating_mul(i64::from(view.scale));
        let height = bottom.saturating_add(63).div_euclid(64);
        self.laid = Some(Laid { list, height });
        self.scroll = clamp_scroll(self.scroll, height, i64::from(view.height));
    }

    /// The page's display list, once laid out.
    pub fn list(&self) -> Option<&DisplayList> {
        self.laid.as_ref().map(|l| &l.list)
    }

    /// The page's height in device pixels, once laid out.
    pub fn height(&self) -> Option<i64> {
        self.laid.as_ref().map(|l| l.height)
    }

    /// `Input`'s scroll: by `delta` device pixels, up if `negative`,
    /// clamped to the page.
    pub fn scroll_by(&mut self, negative: bool, delta: u64) {
        let (Some(l), Some(v)) = (&self.laid, self.view) else {
            return;
        };
        let d = i64::try_from(delta).unwrap_or(i64::MAX);
        let want = if negative {
            self.scroll.saturating_sub(d)
        } else {
            self.scroll.saturating_add(d)
        };
        self.scroll = clamp_scroll(want, l.height, i64::from(v.height));
    }

    /// `Input`'s click at (`x`, `y`) in the viewport: the URL of the topmost
    /// link region holding it (the last in paint order), if it has one.
    pub fn click(&self, x: u64, y: u64) -> Option<String> {
        let l = self.laid.as_ref()?;
        let px = i64::try_from(x).ok()?;
        let py = i64::try_from(y).ok()?.saturating_add(self.scroll);
        let hit = l.list.hits.iter().rev().find(|h| {
            i64::from(h.rect.x) <= px
                && px < h.rect.right()
                && i64::from(h.rect.y) <= py
                && py < h.rect.bottom()
        })?;
        hit.url.clone()
    }
}
