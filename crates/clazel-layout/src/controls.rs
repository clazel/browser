//! Form controls: the fixed look and the geometry of their text (phase-6.md
//! item 6.15).
//!
//! # Sources
//!
//! - **HTML**, commit `0793d3d8544eee95a862e6637130a8106c3d11ca` (as item
//!   6.13's `clazel-forms` pins it): §4.10.5.1.x the `input` element's states
//!   (`type`, `value`, `checked`, `placeholder`, `readonly`, `disabled`),
//!   §4.10.11 `textarea`, §4.10.7 and §4.10.10 `select` and `option`
//!   ("label"), §4.10.6 `button`; §15.5 "Widgets" (§15.5.6 the `input`
//!   element as a text entry widget, §15.5.10 checkboxes and radio buttons,
//!   §15.5.17 `textarea`). §15.5 does not say how a control is drawn beyond
//!   its size and "a user agent may" renderings, so the look is ours.
//!
//! # What this module is
//!
//! Item 5.16's `paint` draws replaced boxes as nothing. [`draw`] returns,
//! for one control and the border box layout gave it, the fills and the
//! glyph runs of its look as [`Draw`]s in 1/64 CSS px; `paint::order` turns
//! them into display list items at the control's place in the paint order
//! (E.2 steps 7.1 and 7.2.1.6). The same text geometry answers "which
//! character is at this point" ([`caret_at`]) and "which option is at this
//! point" ([`option_at`]) for the editing layer (`clazel-forms-edit`).
//!
//! # Modelling choices (the listed ones of item 6.15)
//!
//! - **One fixed look**, drawn from rectangles and glyph runs; nothing of
//!   the host platform's. A text field is a white box with a 1px grey border;
//!   a push button a light grey box with the same border and its label; a
//!   checkbox a 13px white square with a check mark made of 2px squares; a
//!   radio button a disc made of one rectangle per row; a `select` a white
//!   list whose selected rows are blue with white text; a focused control has
//!   a 2px blue ring inside its border box; a disabled one is greyed. Author
//!   `border` and `background` still paint first, under the look (the look
//!   covers them), as for any replaced box.
//! - **A `button` element** is not replaced: its content flows as any
//!   inline-block's, and only its chrome (the face, the border, the ring) is
//!   drawn, under its content ([`chrome`]).
//! - **Text** is inset 2px from the border box (1px of border, 1px of
//!   padding) and clipped to the border box inset by 1px. A one-line field
//!   centres its line vertically and scrolls horizontally by whole pixels so
//!   that the caret stays in view (stateless: the scroll is a function of
//!   the caret). A `textarea` wraps at the character where the next one
//!   would overflow, preferring the last space of the line, and scrolls
//!   vertically so that the caret's line is the last one shown at most.
//! - **A `password` field** draws one U+2022 BULLET per character, in the
//!   field's font (the font may lack it: then its `.notdef` shows).
//! - **The text's advance** per character is the sum of the advances of the
//!   shaped glyphs whose cluster starts in it; a ligature's advance falls to
//!   its first character, so a caret inside one lands at its start.
//! - **`placeholder`** (§4.10.5.1.x): shown, in grey, while the value is
//!   empty, in text fields and textareas, whether or not focused.
//! - **A select** shows its options as rows of one line height, `rows` at a
//!   time ([`crate::boxes::replaced::Replaced::Select`]), scrolled so that its
//!   first selected option is the last row at most; `optgroup` labels are not
//!   drawn (listed).

use clazel_dom::exec::Arena;
use clazel_style::cascade::computed::ComputedStyle;
use clazel_style::cascade::hints::{attribute, html_element};

use crate::boxes::replaced::{option_label, select_options};
use crate::flow::TextFns;
use crate::flow::fragment::Rect;
use crate::flow::heights::line_height;

/// An 8-bit RGBA colour, as `clazel-style` computes them.
pub type Rgba = [u8; 4];

/// The look's colours.
pub mod colours {
    use super::Rgba;
    /// A field's and a list's fill.
    pub const FIELD: Rgba = [255, 255, 255, 255];
    /// A push button's face.
    pub const FACE: Rgba = [233, 233, 237, 255];
    /// A disabled control's fill.
    pub const DISABLED_FILL: Rgba = [239, 239, 239, 255];
    /// Every control's border.
    pub const BORDER: Rgba = [118, 118, 118, 255];
    /// Text.
    pub const TEXT: Rgba = [0, 0, 0, 255];
    /// A disabled control's text and border.
    pub const DISABLED_TEXT: Rgba = [109, 109, 109, 255];
    /// A placeholder.
    pub const PLACEHOLDER: Rgba = [117, 117, 117, 255];
    /// The selected text's background.
    pub const SELECTION: Rgba = [179, 212, 255, 255];
    /// A selected option's row.
    pub const HIGHLIGHT: Rgba = [56, 117, 215, 255];
    /// A selected option's text.
    pub const HIGHLIGHT_TEXT: Rgba = [255, 255, 255, 255];
    /// The focus ring and a checked box's mark.
    pub const ACCENT: Rgba = [0, 96, 223, 255];
}

/// What the editing layer says about a control that is being drawn.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ControlView {
    /// The element's node id.
    pub node: usize,
    /// The control's value (a `textarea`'s API value with LF newlines, an
    /// input button's label): what is shown or edited.
    pub value: String,
    /// The checkedness of a checkbox or radio button.
    pub checked: bool,
    /// The selected `option` nodes of a `select`.
    pub selected: Vec<usize>,
    /// Whether the control has the focus.
    pub focused: bool,
    /// Whether the control is disabled (HTML "a form control is disabled",
    /// with the `fieldset` rule, computed by the caller).
    pub disabled: bool,
    /// The caret, as a character index into `value`.
    pub caret: usize,
    /// The selected characters of `value`, `start < end`, if any.
    pub selection: Option<(usize, usize)>,
}

/// How a control is drawn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A one-line text field (the Text, Search, Telephone, URL, Email,
    /// Password and number-like states).
    Text {
        /// Whether the value is drawn as bullets.
        password: bool,
    },
    /// A `textarea`.
    TextArea,
    /// A checkbox or a radio button.
    Check {
        /// Whether it is a radio button.
        radio: bool,
    },
    /// An `input` push button (Submit, Reset, Button, Image).
    Push,
    /// A `select`.
    Select,
    /// Anything else (a `button` element, a link, a `tabindex` element): at
    /// most a focus ring.
    Other,
}

/// One thing to draw, in 1/64 CSS px (document coordinates).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Draw {
    /// Fill a rectangle.
    Fill(Rect, Rgba),
    /// Draw a run of glyphs.
    Text {
        /// The face, as [`TextFns`] numbers faces.
        face: u32,
        /// The size in 1/64 CSS px.
        size: i32,
        /// The colour.
        colour: Rgba,
        /// The baseline.
        baseline: i32,
        /// Each glyph: id, origin x and y offset from the baseline.
        glyphs: Vec<(u16, i32, i32)>,
    },
    /// Clip what follows to a rectangle, until [`Draw::Unclip`].
    Clip(Rect),
    /// End the clip.
    Unclip,
}

/// 1px in 1/64.
const PX: i32 = 64;
/// The inset of text from the border box: border plus padding.
const INSET: i32 = 2 * PX;
/// The side of a checkbox's and a radio button's box (item 5.14's 13px).
const BOX: i32 = 13 * PX;

fn keyword(s: &[u32], k: &str) -> bool {
    s.len() == k.len()
        && s.iter().zip(k.bytes()).all(|(&c, b)| {
            let lower = if (u32::from(b'A')..=u32::from(b'Z')).contains(&c) {
                c.saturating_add(32)
            } else {
                c
            };
            lower == u32::from(b)
        })
}

/// Whether `node` is an HTML element named `name`.
pub fn is_element(arena: &Arena, node: usize, name: &str) -> bool {
    html_element(arena, node).is_some_and(|(n, _)| keyword(n, name))
}

/// How element `node` is drawn.
pub fn kind_of(arena: &Arena, node: usize) -> Kind {
    let Some((name, attrs)) = html_element(arena, node) else {
        return Kind::Other;
    };
    if keyword(name, "textarea") {
        return Kind::TextArea;
    }
    if keyword(name, "select") {
        return Kind::Select;
    }
    if !keyword(name, "input") {
        return Kind::Other;
    }
    let ty = attribute(attrs, "type").unwrap_or(&[]);
    let is = |k: &str| keyword(ty, k);
    if is("hidden") || is("file") || is("range") || is("color") {
        Kind::Other
    } else if is("checkbox") || is("radio") {
        Kind::Check { radio: is("radio") }
    } else if is("submit") || is("reset") || is("button") || is("image") {
        Kind::Push
    } else {
        Kind::Text {
            password: is("password"),
        }
    }
}

fn attr_present(arena: &Arena, node: usize, name: &str) -> bool {
    html_element(arena, node).is_some_and(|(_, a)| attribute(a, name).is_some())
}

fn attr_string(arena: &Arena, node: usize, name: &str) -> Option<String> {
    html_element(arena, node)
        .and_then(|(_, a)| attribute(a, name))
        .map(crate::boxes::replaced::string)
}

fn rect(x: i32, y: i32, width: i32, height: i32) -> Rect {
    Rect {
        x,
        y,
        width,
        height,
    }
}

fn inset(r: Rect, by: i32) -> Rect {
    rect(
        r.x.saturating_add(by),
        r.y.saturating_add(by),
        r.width.saturating_sub(by.saturating_mul(2)).max(0),
        r.height.saturating_sub(by.saturating_mul(2)).max(0),
    )
}

/// `r`'s border: top, bottom, left and right strips of `w` px (the order
/// the look is dumped in).
fn border(r: Rect, w: i32, colour: Rgba, out: &mut Vec<Draw>) {
    let mid = r.height.saturating_sub(w.saturating_mul(2)).max(0);
    out.push(Draw::Fill(rect(r.x, r.y, r.width, w.min(r.height)), colour));
    out.push(Draw::Fill(
        rect(
            r.x,
            r.y.saturating_add(r.height).saturating_sub(w).max(r.y),
            r.width,
            w.min(r.height),
        ),
        colour,
    ));
    out.push(Draw::Fill(
        rect(r.x, r.y.saturating_add(w), w.min(r.width), mid),
        colour,
    ));
    out.push(Draw::Fill(
        rect(
            r.x.saturating_add(r.width).saturating_sub(w).max(r.x),
            r.y.saturating_add(w),
            w.min(r.width),
            mid,
        ),
        colour,
    ));
}

/// The focus ring: 2px inside the border box.
fn ring(r: Rect, out: &mut Vec<Draw>) {
    border(r, 2 * PX, colours::ACCENT, out);
}

/// A shaped string.
struct Shaped {
    face: u32,
    glyphs: Vec<(u16, i32, i32)>,
    /// The advance of each character.
    adv: Vec<i32>,
}

/// `text` shaped in `style`'s fonts: glyphs placed from x = 0 and the
/// advance of each character (the module's third choice).
fn shape(style: &ComputedStyle, fonts: &impl TextFns, text: &str) -> Shaped {
    let starts: Vec<usize> = text.char_indices().map(|(i, _)| i).collect();
    let mut adv = vec![0i32; starts.len()];
    let mut glyphs = Vec::new();
    let mut face = 0;
    let mut pen = 0i32;
    for g in fonts.shape(style, text) {
        face = g.face;
        glyphs.push((g.id, pen.saturating_add(g.x_offset), g.y_offset));
        pen = pen.saturating_add(g.advance);
        let at = starts
            .partition_point(|&s| s <= g.cluster)
            .saturating_sub(1);
        if let Some(a) = adv.get_mut(at) {
            *a = a.saturating_add(g.advance);
        }
    }
    Shaped { face, glyphs, adv }
}

fn text_draw(
    style: &ComputedStyle,
    sh: &Shaped,
    x: i32,
    baseline: i32,
    colour: Rgba,
) -> Option<Draw> {
    if sh.glyphs.is_empty() {
        return None;
    }
    Some(Draw::Text {
        face: sh.face,
        size: style.font_size,
        colour,
        baseline,
        glyphs: sh
            .glyphs
            .iter()
            .map(|&(id, gx, gy)| (id, x.saturating_add(gx), gy))
            .collect(),
    })
}

fn sum(adv: &[i32], from: usize, to: usize) -> i32 {
    adv.get(from..to.max(from))
        .map_or(0, |s| s.iter().fold(0i32, |a, &b| a.saturating_add(b)))
}

/// The text geometry of a text field or a `textarea`.
struct Geo {
    chars: Vec<char>,
    adv: Vec<i32>,
    /// Visual lines as character ranges, `end` exclusive (a newline is not
    /// in its line).
    lines: Vec<(usize, usize)>,
    line_h: i32,
    ascent: i32,
    /// Where the first shown line's text starts.
    left: i32,
    /// The baseline of the first shown line.
    base: i32,
    /// The first line shown (textarea) and how many fit.
    first: usize,
    shown: usize,
    /// Horizontal scroll of a one-line field.
    scroll: i32,
    multi: bool,
    clip: Rect,
}

/// The displayed text of a view: bullets for a password.
fn displayed(view: &ControlView, password: bool) -> String {
    if password {
        view.value.chars().map(|_| '\u{2022}').collect()
    } else {
        view.value.clone()
    }
}

fn wrap(chars: &[char], adv: &[i32], width: i32) -> Vec<(usize, usize)> {
    let mut lines = Vec::new();
    let mut start = 0usize;
    let n = chars.len();
    loop {
        // The logical line: up to the next newline.
        let end = chars
            .get(start..)
            .and_then(|s| s.iter().position(|&c| c == '\n'))
            .map_or(n, |p| start.saturating_add(p));
        let mut s = start;
        loop {
            let mut w = 0i32;
            let mut e = s;
            let mut last_space = None;
            while e < end {
                let a = adv.get(e).copied().unwrap_or(0);
                if w.saturating_add(a) > width && e > s {
                    break;
                }
                w = w.saturating_add(a);
                if chars.get(e) == Some(&' ') {
                    last_space = Some(e);
                }
                e = e.saturating_add(1);
            }
            if e < end
                && let Some(sp) = last_space
                && sp > s
            {
                // Break after the last space.
                e = sp.saturating_add(1);
            }
            lines.push((s, e));
            if e >= end {
                break;
            }
            s = e;
        }
        if end >= n {
            break;
        }
        start = end.saturating_add(1);
    }
    lines
}

fn geo(
    view: &ControlView,
    kind: Kind,
    style: &ComputedStyle,
    fonts: &impl TextFns,
    bb: Rect,
) -> Geo {
    let m = fonts.metrics(style);
    let line_h = line_height(style, &m).max(1);
    let multi = kind == Kind::TextArea;
    let password = matches!(kind, Kind::Text { password: true });
    let text = displayed(view, password);
    let chars: Vec<char> = text.chars().collect();
    let sh = shape(style, fonts, &text);
    let mut adv = sh.adv;
    for (a, c) in adv.iter_mut().zip(&chars) {
        if *c == '\n' {
            *a = 0;
        }
    }
    let clip = inset(bb, PX);
    let inner_w = bb.width.saturating_sub(INSET.saturating_mul(2)).max(0);
    let lines = if multi {
        wrap(&chars, &adv, inner_w)
    } else {
        vec![(0, chars.len())]
    };
    let inner_h = bb.height.saturating_sub(INSET.saturating_mul(2)).max(0);
    let fit = usize::try_from(inner_h.checked_div(line_h).unwrap_or(1).max(1)).unwrap_or(1);
    let caret = view.caret.min(chars.len());
    let caret_line = line_of(&lines, caret);
    let first = if multi {
        caret_line.saturating_add(1).saturating_sub(fit)
    } else {
        0
    };
    let top = if multi {
        bb.y.saturating_add(INSET)
    } else {
        bb.y.saturating_add((bb.height.saturating_sub(line_h) / 2).max(PX))
    };
    let scroll = if multi {
        0
    } else {
        sum(&adv, 0, caret)
            .saturating_sub(inner_w.saturating_sub(PX))
            .max(0)
    };
    Geo {
        chars,
        adv,
        lines,
        line_h,
        ascent: m.ascent,
        left: bb.x.saturating_add(INSET),
        base: top.saturating_add(m.ascent),
        first,
        shown: fit,
        scroll,
        multi,
        clip,
    }
}

/// The line holding the caret `at`: the last line starting at or before it.
fn line_of(lines: &[(usize, usize)], at: usize) -> usize {
    lines.partition_point(|&(s, _)| s <= at).saturating_sub(1)
}

impl Geo {
    /// The x of character boundary `at` on line `line`.
    fn x_at(&self, line: usize, at: usize) -> i32 {
        let start = self.lines.get(line).map_or(0, |l| l.0);
        self.left
            .saturating_add(sum(&self.adv, start, at))
            .saturating_sub(self.scroll)
    }

    /// The top of line `line` (it may be above the box when scrolled).
    fn top_of(&self, line: usize) -> i32 {
        let rel = i32::try_from(line.saturating_sub(self.first)).unwrap_or(i32::MAX);
        self.base
            .saturating_sub(self.ascent)
            .saturating_add(rel.saturating_mul(self.line_h))
    }

    fn visible(&self, line: usize) -> bool {
        line >= self.first && line < self.first.saturating_add(self.shown)
    }
}

/// The character index nearest to point (`x`, `y`) in 1/64 CSS px, for
/// text field or `textarea` `view` laid out in border box `bb`.
pub fn caret_at(
    view: &ControlView,
    arena: &Arena,
    style: &ComputedStyle,
    fonts: &impl TextFns,
    bb: Rect,
    x: i32,
    y: i32,
) -> usize {
    let kind = kind_of(arena, view.node);
    let g = geo(view, kind, style, fonts, bb);
    let rows = i32::try_from(g.lines.len()).unwrap_or(i32::MAX);
    let rel = y
        .saturating_sub(g.top_of(g.first))
        .div_euclid(g.line_h)
        .saturating_add(i32::try_from(g.first).unwrap_or(0))
        .clamp(0, rows.saturating_sub(1));
    let line = usize::try_from(rel).unwrap_or(0);
    let Some(&(s, e)) = g.lines.get(line) else {
        return 0;
    };
    // The boundary whose x is nearest: a character is hit in its left half
    // or its right half.
    let mut best = s;
    let mut at = s;
    while at < e {
        let mid = g
            .x_at(line, at)
            .saturating_add(g.adv.get(at).copied().unwrap_or(0) / 2);
        if x <= mid {
            break;
        }
        at = at.saturating_add(1);
        best = at;
    }
    best
}

/// The index, in `select_options` order, of the option at (`x`, `y`) of a
/// select's border box `bb`, if the point is on a row.
pub fn option_at(
    arena: &Arena,
    select: usize,
    selected: &[usize],
    style: &ComputedStyle,
    fonts: &impl TextFns,
    bb: Rect,
    y: i32,
) -> Option<usize> {
    let (first, _, line_h) = list_geometry(arena, select, selected, style, fonts, bb);
    let rel = y.saturating_sub(bb.y.saturating_add(INSET));
    if rel < 0 {
        return None;
    }
    let row = usize::try_from(rel.div_euclid(line_h)).ok()?;
    let i = first.saturating_add(row);
    (i < select_options(arena, select).len()).then_some(i)
}

/// The first shown option, how many rows fit and the row height.
fn list_geometry(
    arena: &Arena,
    select: usize,
    selected: &[usize],
    style: &ComputedStyle,
    fonts: &impl TextFns,
    bb: Rect,
) -> (usize, usize, i32) {
    let m = fonts.metrics(style);
    let line_h = line_height(style, &m).max(1);
    let inner_h = bb.height.saturating_sub(INSET.saturating_mul(2)).max(0);
    let fit = usize::try_from(inner_h.checked_div(line_h).unwrap_or(1).max(1)).unwrap_or(1);
    let first_sel = select_options(arena, select)
        .iter()
        .position(|o| selected.contains(o))
        .unwrap_or(0);
    (first_sel.saturating_add(1).saturating_sub(fit), fit, line_h)
}

/// The chrome of a `button` element: its face, border and ring, under its
/// content (the module's second choice).
pub fn chrome(view: &ControlView, bb: Rect) -> Vec<Draw> {
    let mut out = Vec::new();
    let (fill, line) = if view.disabled {
        (colours::DISABLED_FILL, colours::DISABLED_TEXT)
    } else {
        (colours::FACE, colours::BORDER)
    };
    out.push(Draw::Fill(bb, fill));
    border(bb, PX, line, &mut out);
    if view.focused && !view.disabled {
        ring(bb, &mut out);
    }
    out
}

/// Only the focus ring of border box `bb`.
pub fn chrome_ring(bb: Rect) -> Vec<Draw> {
    let mut out = Vec::new();
    ring(bb, &mut out);
    out
}

/// A disc of diameter 13px at (`x`, `y`): one rectangle per row (the
/// module's first choice), `shrink` px smaller on each side.
fn disc(x: i32, y: i32, shrink: i32, colour: Rgba, out: &mut Vec<Draw>) {
    // Work in half pixels: the centre is (13, 13) of 26, the radius 13 less
    // twice the shrink.
    let r2 = 13i32.saturating_sub(shrink.saturating_mul(2));
    for row in 0..13i32 {
        let dy = row.saturating_mul(2).saturating_add(1).saturating_sub(13);
        let rem = r2.saturating_mul(r2).saturating_sub(dy.saturating_mul(dy));
        if rem <= 0 {
            continue;
        }
        let mut half = 0i32;
        while half
            .saturating_add(1)
            .saturating_mul(half.saturating_add(1))
            <= rem
        {
            half = half.saturating_add(1);
        }
        // `half` is the half-width in half pixels; widths are whole pixels
        // of the same parity as 13 so the disc is symmetric.
        let w = if half % 2 == 0 {
            half.saturating_add(1)
        } else {
            half
        }
        .min(13);
        out.push(Draw::Fill(
            rect(
                x.saturating_add((13i32.saturating_sub(w) / 2).saturating_mul(PX)),
                y.saturating_add(row.saturating_mul(PX)),
                w.saturating_mul(PX),
                PX,
            ),
            colour,
        ));
    }
}

/// The squares of a check mark in a 13px box, in px from its corner.
const CHECK_MARK: [(i32, i32); 7] = [(3, 6), (4, 7), (5, 8), (6, 7), (7, 6), (8, 5), (9, 4)];

/// What to draw for control `view` (element `view.node` of `arena`), whose
/// computed style is `style` and whose border box layout gave as `bb`:
/// fills, clips and glyph runs, in paint order. A kind with no look of its
/// own ([`Kind::Other`]) gets a ring when focused.
pub fn draw(
    view: &ControlView,
    arena: &Arena,
    style: &ComputedStyle,
    fonts: &impl TextFns,
    bb: Rect,
) -> Vec<Draw> {
    let kind = kind_of(arena, view.node);
    let mut out = Vec::new();
    let (fill, line, ink) = if view.disabled {
        (
            colours::DISABLED_FILL,
            colours::DISABLED_TEXT,
            colours::DISABLED_TEXT,
        )
    } else {
        (colours::FIELD, colours::BORDER, colours::TEXT)
    };
    let ring_on = view.focused && !view.disabled;
    match kind {
        Kind::Other => {
            if ring_on {
                ring(bb, &mut out);
            }
        }
        Kind::Check { radio } => {
            // Anchored at the box's top left: the box is 13px by 13px.
            let (x, y) = (bb.x, bb.y);
            if radio {
                disc(x, y, 0, line, &mut out);
                disc(x, y, 1, fill, &mut out);
                if view.checked {
                    disc(x, y, 4, colours::ACCENT, &mut out);
                }
            } else {
                let b = rect(x, y, BOX, BOX);
                out.push(Draw::Fill(b, fill));
                border(b, PX, line, &mut out);
                if view.checked {
                    for (cx, cy) in CHECK_MARK {
                        out.push(Draw::Fill(
                            rect(
                                x.saturating_add(cx.saturating_mul(PX)),
                                y.saturating_add(cy.saturating_mul(PX)),
                                2 * PX,
                                2 * PX,
                            ),
                            colours::ACCENT,
                        ));
                    }
                }
            }
            if ring_on {
                ring(rect(x, y, BOX, BOX), &mut out);
            }
        }
        Kind::Push => {
            out.push(Draw::Fill(
                bb,
                if view.disabled {
                    colours::DISABLED_FILL
                } else {
                    colours::FACE
                },
            ));
            border(bb, PX, line, &mut out);
            let label = push_label(arena, view);
            let sh = shape(style, fonts, &label);
            let w = sh.adv.iter().fold(0i32, |a, &b| a.saturating_add(b));
            let m = fonts.metrics(style);
            let lh = line_height(style, &m).max(1);
            let x =
                bb.x.saturating_add(bb.width.saturating_sub(w) / 2)
                    .max(bb.x);
            let base =
                bb.y.saturating_add(bb.height.saturating_sub(lh) / 2)
                    .saturating_add(m.ascent);
            out.push(Draw::Clip(inset(bb, PX)));
            out.extend(text_draw(style, &sh, x, base, ink));
            out.push(Draw::Unclip);
            if ring_on {
                ring(bb, &mut out);
            }
        }
        Kind::Text { .. } | Kind::TextArea => {
            out.push(Draw::Fill(bb, fill));
            border(bb, PX, line, &mut out);
            let g = geo(view, kind, style, fonts, bb);
            out.push(Draw::Clip(g.clip));
            let first = g.first;
            let last = first.saturating_add(g.shown).min(g.lines.len());
            // The selection, behind the text.
            if let Some((a, b)) = view.selection
                && !view.disabled
            {
                for (i, &(s, e)) in g.lines.iter().enumerate().take(last).skip(first) {
                    // A newline inside the selection extends it past the
                    // line's last character by one space-width-less pixel.
                    let from = a.max(s);
                    let to = b.min(e);
                    if from < to || (g.multi && a <= e && e < b) {
                        let x0 = g.x_at(i, from.min(to));
                        let x1 = g.x_at(i, to).max(x0);
                        let extra = if g.multi && e < b { PX } else { 0 };
                        out.push(Draw::Fill(
                            rect(
                                x0,
                                g.top_of(i),
                                x1.saturating_sub(x0).saturating_add(extra),
                                g.line_h,
                            ),
                            colours::SELECTION,
                        ));
                    }
                }
            }
            if g.chars.is_empty() {
                if let Some(p) = attr_string(arena, view.node, "placeholder") {
                    let p: String = if g.multi {
                        p
                    } else {
                        p.chars().filter(|&c| c != '\n' && c != '\r').collect()
                    };
                    let sh = shape(style, fonts, &p);
                    out.extend(text_draw(style, &sh, g.left, g.base, colours::PLACEHOLDER));
                }
            } else {
                for (i, &(s, e)) in g.lines.iter().enumerate().take(last).skip(first) {
                    let t: String = g.chars.get(s..e).unwrap_or(&[]).iter().collect();
                    let sh = shape(style, fonts, &t);
                    let base = g.top_of(i).saturating_add(g.ascent);
                    out.extend(text_draw(style, &sh, g.x_at(i, s), base, ink));
                }
            }
            // The caret: a 1px bar, only in a focused field with no
            // selection.
            if view.focused && !view.disabled && view.selection.is_none() {
                let at = view.caret.min(g.chars.len());
                let i = line_of(&g.lines, at);
                if g.visible(i) {
                    out.push(Draw::Fill(
                        rect(g.x_at(i, at), g.top_of(i), PX, g.line_h),
                        colours::TEXT,
                    ));
                }
            }
            out.push(Draw::Unclip);
            if ring_on {
                ring(bb, &mut out);
            }
        }
        Kind::Select => {
            out.push(Draw::Fill(bb, fill));
            border(bb, PX, line, &mut out);
            let options = select_options(arena, view.node);
            let (first, fit, lh) =
                list_geometry(arena, view.node, &view.selected, style, fonts, bb);
            let m = fonts.metrics(style);
            out.push(Draw::Clip(inset(bb, PX)));
            for (row, &o) in options.iter().enumerate().skip(first).take(fit) {
                let top = bb.y.saturating_add(INSET).saturating_add(
                    i32::try_from(row.saturating_sub(first))
                        .unwrap_or(0)
                        .saturating_mul(lh),
                );
                let on = view.selected.contains(&o);
                let off = view.disabled || attr_present(arena, o, "disabled");
                if on {
                    out.push(Draw::Fill(
                        rect(
                            bb.x.saturating_add(PX),
                            top,
                            bb.width.saturating_sub(2 * PX).max(0),
                            lh,
                        ),
                        if view.disabled {
                            colours::DISABLED_TEXT
                        } else {
                            colours::HIGHLIGHT
                        },
                    ));
                }
                let sh = shape(style, fonts, &option_label(arena, o));
                let colour = if on {
                    colours::HIGHLIGHT_TEXT
                } else if off {
                    colours::DISABLED_TEXT
                } else {
                    colours::TEXT
                };
                out.extend(text_draw(
                    style,
                    &sh,
                    bb.x.saturating_add(INSET),
                    top.saturating_add(m.ascent),
                    colour,
                ));
            }
            out.push(Draw::Unclip);
            if ring_on {
                ring(bb, &mut out);
            }
        }
    }
    out
}

/// An input button's label: its value, else the default of its state.
fn push_label(arena: &Arena, view: &ControlView) -> String {
    if !view.value.is_empty() {
        return view.value.clone();
    }
    match attr_string(arena, view.node, "type")
        .map(|t| t.to_ascii_lowercase())
        .as_deref()
    {
        Some("submit") => "Submit".to_owned(),
        Some("reset") => "Reset".to_owned(),
        _ => String::new(),
    }
}

/// The deepest box of `tree` at (`x`, `y`) in 1/64 CSS px, as its node: the
/// last box in tree order whose border box holds the point (a later box is
/// painted over an earlier one). `None` when no box with a node does.
pub fn node_at(
    frags: &crate::flow::FragmentTree,
    tree: &crate::boxes::BoxTree,
    x: i32,
    y: i32,
) -> Option<usize> {
    (0..tree.boxes.len()).rev().find_map(|b| {
        let node = frags.node(b)?;
        let r = frags.fragment(b)?.border_box;
        let inside = x >= r.x && x < r.right() && y >= r.y && y < r.bottom();
        (inside && node != 0).then_some(node)
    })
}

/// The border box of the box generated by `node`, if it has one.
pub fn border_box_of(
    frags: &crate::flow::FragmentTree,
    tree: &crate::boxes::BoxTree,
    node: usize,
) -> Option<Rect> {
    let b = (0..tree.boxes.len()).find(|&b| frags.node(b) == Some(node))?;
    frags.fragment(b).map(|f| f.border_box)
}
