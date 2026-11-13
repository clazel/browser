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

pub mod state;
