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
//! - **The socket's framing** is `clazel_gpu::channel`'s, the GPU process's
//!   own (item 5.23): a 4-byte little-endian length, the width and height of
//!   the viewport the list was laid out for, then one encoded list. 5.20 first
//!   defined a big-endian one of its own; there is now one.
//! - **The list socket is not wired yet**: the host must create a socket
//!   pair and hand the renderer its end, which needs a new `clazel-sys` call
//!   to clear close-on-exec and to adopt the descriptor (item 5.18's plan;
//!   `clazel-sys` is audited and outside this item). Until then
//!   `crate::run_graphics` takes any writer, and the binary runs the text
//!   path.

pub mod fonts;
pub mod frame;
pub mod link;
pub mod scripts;
pub mod sheets;
pub mod state;

#[cfg(test)]
mod tests;

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
    is_essence, parse_html_with, string_of,
};
use clazel_web::scripting::time::Clock;
use fonts::{Fonts, Text};
use link::LinkHandle;
use scripts::Scripts;
use sheets::Cached;
use state::SheetWait;
use std::collections::HashMap;

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

/// What a document's tree is read with: the page's other state.
struct Ctx<'a> {
    wait: &'a SheetWait,
    base: Option<&'a ParsedUrl>,
    cache: &'a HashMap<Vec<u32>, Cached>,
}

/// A page laid out and painted for one viewport.
struct Laid {
    list: DisplayList,
    /// The page's height, in device pixels.
    height: i64,
}

/// What a page needs to run its scripts: the kernel's link, and a clock.
pub struct ScriptEnv {
    /// The socket, shared with the renderer's loop.
    pub link: LinkHandle,
    /// The page's monotonic clock (`performance.now()` and the timers).
    pub clock: Box<dyn Clock>,
}

/// A committed document, as the graphical pipeline holds it.
pub struct Page {
    /// The tree, while the page runs no scripts; with scripts it is the
    /// scripts' page's, and `with_arena` reaches it.
    arena: Option<Arena>,
    /// The document's scripts (items 7.15 and 7.17).
    scripts: Option<Scripts>,
    /// A script ran since the style sources were collected.
    dirty: bool,
    /// What the linked sheets answered, by `href`: a restyle after a script
    /// reads them again from here.
    cache: HashMap<Vec<u32>, Cached>,
    base: Option<ParsedUrl>,
    wait: SheetWait,
    /// The document's URL, against which the kernel resolves a sheet's
    /// `href`, and its encoding (a sheet's fallback, CSS Syntax 3 §3.2).
    url: Option<ParsedUrl>,
    encoding: Encoding,
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

/// Steps 7 to 10 over `arena`: the cascade, the box tree, layout and paint
/// for `view`.
fn lay_out_tree(
    arena: &Arena,
    wait: &SheetWait,
    base: Option<&ParsedUrl>,
    view: View,
    fonts: &Fonts,
) -> Laid {
    let (cw, ch) = view.css();
    let device = Device::screen(cw, ch);
    let sheets = ua::sheets().for_document(arena);
    let table = cascade_with(&sheets, arena, &wait.sources, device);
    let tree = build(arena, &table);
    let text = Text::of(fonts, &table.families);
    let px64 = |v: u32| i32::try_from(i64::from(v).saturating_mul(64)).unwrap_or(i32::MAX);
    let frags = layout(
        &tree,
        arena,
        &table,
        &text,
        CssViewport {
            width: px64(cw),
            height: px64(ch),
        },
    );
    let list = paint(&frags, &tree, arena, &table, &text, base, view.scale);
    // The page's height: its extent's bottom, in device pixels, rounded up.
    let bottom = i64::from(frags.extent.bottom()).saturating_mul(i64::from(view.scale));
    let height = bottom.saturating_add(63).div_euclid(64);
    Laid { list, height }
}

impl Page {
    /// Steps 1 to 6 for the document committed at `url` with
    /// `content_type` and `body` (the module's pipeline).
    pub fn load(url: &[u8], content_type: &[u8], body: &[u8], view: Option<View>) -> Page {
        Page::load_with(url, content_type, body, view, None)
    }

    /// [`Page::load`] for a document whose scripts run: HTML is parsed with
    /// the scripting flag on (`noscript` is text) and its tree is handed to
    /// the page's scripts. They do not run until [`Page::start_scripts`].
    pub fn load_scripted(
        url: &[u8],
        content_type: &[u8],
        body: &[u8],
        view: Option<View>,
        env: ScriptEnv,
    ) -> Page {
        Page::load_with(url, content_type, body, view, Some(env))
    }

    fn load_with(
        url: &[u8],
        content_type: &[u8],
        body: &[u8],
        view: Option<View>,
        env: Option<ScriptEnv>,
    ) -> Page {
        let url_cps = code_points(url);
        let url_text = String::from_utf8_lossy(url).into_owned();
        let (supplied, computed) = computed_type(content_type, body);
        let transport = supplied.as_ref().and_then(transport_encoding);
        let mut html = false;
        let (arena, encoding) = if is_html_mime_type(&computed) {
            match parse_html_with(body, transport, &url_cps, env.is_some()) {
                Ok(p) => {
                    html = true;
                    (p.arena, p.encoding)
                }
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
        // Step 6: a `FetchStyle` for each link whose `media` matches the
        // viewport (800 by 600 before the first `Viewport`), which renders
        // nothing until it is answered (`sheets.rs`).
        let (cw, ch) = view.map_or((800, 600), View::css);
        let wait = SheetWait::start(collect(&arena), Device::screen(cw, ch), true, encoding);
        let document_url = crate::pipeline::parse_url_pub(&url_cps, None);
        // The tree goes to the scripts' page, which keeps it for the
        // document's life.
        let (arena, scripts) = match env {
            Some(env) if html => {
                match Scripts::new(&url_text, encoding, arena, env.link, env.clock) {
                    Ok(scripts) => (None, Some(scripts)),
                    Err(e) => {
                        // The engine did not start: the document, without
                        // scripts (parsed again, as the tree was given up).
                        eprintln!("clazel-renderer: scripts did not start: {e}");
                        let again = parse_html_with(body, transport, &url_cps, false)
                            .map_or_else(|_| made("", &url_cps), |p| p.arena);
                        (Some(again), None)
                    }
                }
            }
            _ => (Some(arena), None),
        };
        Page {
            arena,
            scripts,
            dirty: false,
            cache: HashMap::new(),
            base,
            wait,
            url: document_url,
            encoding,
            title,
            laid: None,
            view: None,
            scroll: 0,
        }
    }

    /// The `FetchStyle`s to send: each pending link's index (its request
    /// id) and its `href` as the document wrote it, UTF-8 (the kernel
    /// resolves it against the document's URL).
    pub fn requests(&self) -> Vec<(u64, Vec<u8>)> {
        self.wait
            .pending
            .iter()
            .filter_map(|&i| {
                let href = self.wait.href(i)?;
                Some((u64::try_from(i).ok()?, string_of(&href)?.into_bytes()))
            })
            .collect()
    }

    /// The kernel's answer to request `request`: the response's content
    /// type and body, or `None` for `StyleFailed`. Returns whether the page
    /// became ready by it.
    pub fn answer(&mut self, request: u64, response: Option<(&[u8], &[u8])>) -> bool {
        let Ok(index) = usize::try_from(request) else {
            return false;
        };
        let was = self.ready();
        let same_origin = self
            .wait
            .href(index)
            .and_then(|h| crate::pipeline::parse_url_pub(&h, self.url.as_ref()))
            .zip(self.url.as_ref())
            .is_some_and(|(a, b)| sheets::same_origin(&a, b));
        if let (Some((content_type, body)), Some(href)) = (response, self.wait.href(index)) {
            // Kept for a restyle after a script (`settle`).
            self.cache.insert(
                href,
                Cached {
                    content_type: content_type.to_vec(),
                    same_origin,
                    body: body.to_vec(),
                },
            );
        }
        let response = response.map(|(content_type, body)| clazel_style::sources::Response {
            content_type: (!content_type.is_empty()).then_some(content_type),
            same_origin,
            // `StyleResponse` carries no status: any final response counts as
            // "success" (README, what waits).
            ok: true,
            body,
        });
        self.wait.answer(index, response, self.encoding);
        !was && self.ready()
    }

    /// Whether the page waits for no style sheet (step 6).
    pub fn ready(&self) -> bool {
        self.wait.ready()
    }

    /// Calls `f` with the document's tree and the page's sources, whichever
    /// holds the tree (the page, or its scripts).
    fn with_arena<R>(&mut self, f: impl FnOnce(&Arena, Ctx<'_>) -> R) -> Option<R> {
        let Page {
            arena,
            scripts,
            wait,
            base,
            cache,
            ..
        } = self;
        let ctx = Ctx {
            wait,
            base: base.as_ref(),
            cache,
        };
        match (arena.as_ref(), scripts.as_mut()) {
            (Some(a), _) => Some(f(a, ctx)),
            (None, Some(s)) => s.with_document(|a| f(a, ctx)),
            (None, None) => None,
        }
    }

    /// Steps 7 to 10 for viewport `view`, in `fonts`.
    pub fn lay_out(&mut self, view: View, fonts: &Fonts) {
        self.view = Some(view);
        if !self.ready() {
            return;
        }
        let laid =
            self.with_arena(|arena, ctx| lay_out_tree(arena, ctx.wait, ctx.base, view, fonts));
        if let Some(laid) = laid {
            self.scroll = clamp_scroll(self.scroll, laid.height, i64::from(view.height));
            self.laid = Some(laid);
        }
    }

    /// The client rectangles of every element and text node (item 5.25's
    /// geometry comparison, `clazel_layout::rects`), laid out for `view` in
    /// `fonts` exactly as [`Page::lay_out`] lays out; empty while sheets are
    /// awaited.
    pub fn client_rects(
        &mut self,
        view: View,
        fonts: &Fonts,
    ) -> Vec<clazel_layout::rects::ClientRect> {
        if !self.ready() {
            return Vec::new();
        }
        let (cw, ch) = view.css();
        let device = Device::screen(cw, ch);
        self.with_arena(|arena, ctx| {
            let sheets = ua::sheets().for_document(arena);
            let table = cascade_with(&sheets, arena, &ctx.wait.sources, device);
            let tree = build(arena, &table);
            let text = Text::of(fonts, &table.families);
            let px64 = |v: u32| i32::try_from(i64::from(v).saturating_mul(64)).unwrap_or(i32::MAX);
            let frags = layout(
                &tree,
                arena,
                &table,
                &text,
                CssViewport {
                    width: px64(cw),
                    height: px64(ch),
                },
            );
            clazel_layout::rects::client_rects(&frags, &tree, arena, &table, &text)
        })
        .unwrap_or_default()
    }

    // ---- Scripts (items 7.15 and 7.17) --------------------------------------

    /// Whether the document runs scripts.
    pub fn has_scripts(&self) -> bool {
        self.scripts.is_some()
    }

    /// Runs the document's scripts as far as they can go now (the fetches
    /// they ask for are sent). Returns whether the document may have
    /// changed.
    ///
    /// # Errors
    /// The socket failed.
    pub fn start_scripts(&mut self) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.start()?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
    }

    /// The scripts' event loop: what is due runs. Returns whether anything
    /// did.
    ///
    /// # Errors
    /// The socket failed.
    pub fn tick(&mut self) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.tick()?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
    }

    /// Update the rendering: the animation frame callbacks run, before the
    /// page is painted.
    ///
    /// # Errors
    /// The socket failed.
    pub fn update_the_rendering(&mut self) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.update_the_rendering()?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
    }

    /// A click on a `javascript:` link: the page runs it.
    ///
    /// # Errors
    /// The socket failed.
    pub fn follow_javascript_url(&mut self, url: &str) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.follow_javascript_url(url)?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
    }

    /// The kernel's `ScriptResponse`, `ScriptBody`, `ScriptEnd` and
    /// `ScriptFailed` for the page's script fetches. Each returns whether
    /// the document may have changed.
    ///
    /// # Errors
    /// The socket failed.
    pub fn script_response(
        &mut self,
        request: u64,
        content_type: Vec<u8>,
    ) -> Result<bool, crate::RunError> {
        if let Some(s) = self.scripts.as_mut() {
            s.response(request, content_type);
        }
        Ok(false)
    }

    /// See [`Page::script_response`].
    ///
    /// # Errors
    /// The socket failed.
    pub fn script_body(&mut self, request: u64, bytes: &[u8]) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.body(request, bytes)?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
    }

    /// See [`Page::script_response`].
    ///
    /// # Errors
    /// The socket failed.
    pub fn script_end(&mut self, request: u64) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.end(request)?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
    }

    /// See [`Page::script_response`].
    ///
    /// # Errors
    /// The socket failed.
    pub fn script_failed(&mut self, request: u64) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.failed(request)?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
    }

    /// After scripts ran: collects the style sources and the title of the
    /// changed document again (the restyle that HTML's "update the
    /// rendering" does), once no linked sheet is awaited. A sheet answered
    /// before is read again from what it answered; a link a script added is
    /// not fetched (it is as a failed one). Returns whether the page must be
    /// laid out and painted again.
    pub fn settle(&mut self) -> bool {
        if !self.dirty || !self.wait.pending.is_empty() {
            return false;
        }
        self.dirty = false;
        let encoding = self.encoding;
        let fresh = self.with_arena(|arena, ctx| {
            (
                SheetWait::rebuild(collect(arena), ctx.cache, encoding),
                title_of(arena),
            )
        });
        if let Some((wait, title)) = fresh {
            self.wait = wait;
            self.title = title;
        }
        true
    }

    /// The page clock's time at which the scripts' next timer is due.
    pub fn next_wake_ms(&mut self) -> Option<u64> {
        self.scripts.as_mut().and_then(Scripts::next_wake_ms)
    }

    /// The page clock's time, in milliseconds.
    pub fn now_ms(&mut self) -> u64 {
        self.scripts.as_mut().map_or(0, Scripts::now_ms)
    }

    /// The page's display list, once laid out.
    pub fn list(&self) -> Option<&DisplayList> {
        self.laid.as_ref().map(|l| &l.list)
    }

    /// The page's height in device pixels, once laid out.
    pub fn height(&self) -> Option<i64> {
        self.laid.as_ref().map(|l| l.height)
    }

    /// The node that the point (`x`, `y`) of the viewport, in device pixels,
    /// is over (item 7.14's hit test): of the boxes of every element and text
    /// node that hold it (the client rectangles of the fragment tree, CSS
    /// pixels, document coordinates), the deepest in the tree, the later of
    /// two equally deep ones (a later sibling paints over an earlier one);
    /// the document element if the point is over none (the canvas). `None`
    /// before the page is laid out. `z-index`, clipping, `visibility` and
    /// `pointer-events` are not looked at.
    pub fn hit_test(&mut self, view: View, fonts: &Fonts, x: u64, y: u64) -> Option<usize> {
        self.laid.as_ref()?;
        // Device pixels to 1/64 CSS pixel.
        let scale = i64::from(view.scale.max(1));
        let px = i64::try_from(x).ok()?.saturating_mul(64).div_euclid(scale);
        let py = i64::try_from(y)
            .ok()?
            .saturating_add(self.scroll)
            .saturating_mul(64)
            .div_euclid(scale);
        let rects = self.client_rects(view, fonts);
        let mut best: Option<(usize, &str)> = None;
        for r in &rects {
            let (rx, ry) = (i64::from(r.rect.x), i64::from(r.rect.y));
            let inside = rx <= px
                && px < rx.saturating_add(i64::from(r.rect.width))
                && ry <= py
                && py < ry.saturating_add(i64::from(r.rect.height));
            if !inside {
                continue;
            }
            let depth = r.node.split('/').count();
            if best.is_none_or(|(d, _)| depth >= d) {
                best = Some((depth, r.node.as_str()));
            }
        }
        let path = best.map(|(_, p)| p.to_owned());
        self.with_arena(|arena, _| {
            let mut node = 0usize;
            if let Some(path) = path {
                for step in path.split('/').filter(|s| !s.is_empty()) {
                    let k: usize = step.parse().ok()?;
                    node = *arena.children(node).get(k)?;
                }
                return Some(node);
            }
            // The canvas: the document element.
            arena
                .children(0)
                .iter()
                .copied()
                .find(|&c| matches!(arena.kind(c), clazel_dom::exec::ExecKind::Element { .. }))
        })
        .flatten()
    }

    /// The user's click on `target` (item 7.14); see [`scripts::Scripts::click`].
    ///
    /// # Errors
    /// The socket failed.
    pub fn dispatch_click(
        &mut self,
        input: clazel_web::page::input::MouseInput,
    ) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.click(input)?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
    }

    /// A key typed (item 7.14).
    ///
    /// # Errors
    /// The socket failed.
    pub fn dispatch_key(
        &mut self,
        input: clazel_web::page::input::KeyInput,
    ) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.key(input)?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
    }

    /// A wheel turn (item 7.14): whether the default action, scrolling, is
    /// to happen, and whether a listener ran (the page may have changed).
    ///
    /// # Errors
    /// The socket failed.
    pub fn dispatch_wheel(
        &mut self,
        input: clazel_web::page::input::WheelInput,
    ) -> Result<(bool, bool), crate::RunError> {
        match self.scripts.as_mut() {
            Some(s) => {
                let (scrolls, ran) = s.wheel(input)?;
                self.dirty |= ran;
                Ok((scrolls, ran))
            }
            None => Ok((true, false)),
        }
    }

    /// The viewport scrolled (item 7.14): the `scroll` event.
    ///
    /// # Errors
    /// The socket failed.
    pub fn dispatch_scrolled(&mut self) -> Result<bool, crate::RunError> {
        let ran = match self.scripts.as_mut() {
            Some(s) => s.scrolled()?,
            None => false,
        };
        self.dirty |= ran;
        Ok(ran)
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
