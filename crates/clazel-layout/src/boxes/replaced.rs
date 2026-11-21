//! Replaced elements: which elements are, and what HTML gives for their
//! size (phase-5.md item 5.13).
//!
//! Source: HTML, whatwg/html at commit
//! `4c54fae106900a24130da614b7ad29d85c6981c6` (the commit `clazel-style`
//! vendors §15 from, `crates/clazel-style/data/html-4c54fae1/`): §15.4
//! "Replaced elements" (§15.4.1 "Embedded content", §15.4.2 "Images",
//! §15.4.3 "Attributes for embedded content and images"), §15.5 "Widgets"
//! (§15.5.6 "The input element as a text entry widget", §15.5.17 "The
//! textarea element"), and the `textarea` element's `cols` and `rows`
//! (`#attr-textarea-cols-value`, `#attr-textarea-rows-value`). §15.5 is not
//! vendored; its text was read at that commit.
//!
//! Modelling choices:
//!
//! - **Which elements are replaced**: of §15.4's list ("audio, canvas,
//!   embed, iframe, img, input, object, and video"), the four phase-5.md
//!   names: `img`, `input`, `iframe`, and `textarea` (a widget §15.5.17
//!   renders as "an 'inline-block' box depicting a multiline text
//!   control", which is drawn as an empty box like `input`). `audio`,
//!   `canvas`, `embed`, `object` and `video` are ordinary elements in this
//!   phase, so their fallback content is rendered (Phase 6). `button` is an
//!   ordinary element (its content is its label). **`select` is replaced
//!   since item 6.15**: a list drawn in the content area, [`Replaced::Select`]
//!   rows high and as wide as its longest option label (a native popup would
//!   be outside the tab's surface). HTML leaves a `select`'s size to the user
//!   agent, so the choice is ours, listed.
//! - **No image is decoded** (Phase 6), so every `img` is §15.4.2's "img
//!   element that represents nothing": "a replaced element whose natural
//!   dimensions are 0". Its used size comes from `width` and `height`,
//!   which the dimension attributes map to (§15.4.3, `clazel-style`'s
//!   presentational hints). The alternative text is not shown.
//! - **An `iframe`** is a replaced element (§15.4.1) with no natural size,
//!   so CSS's default object size (300 by 150, CSS Images 3 §4.3†) applies;
//!   its `src` is kept for item 5.24's link.
//! - **Sizes that need a font** are kept as HTML gives them, in characters:
//!   §15.5.6's "converting a character width to pixels" and §15.5.17's
//!   "textarea effective width" and "height" need the primary font's
//!   average and maximum character widths and line height, which layout
//!   (item 5.14) has. The scrollbar width those formulas add is 0 (this
//!   phase draws no scrollbars).
//! - **An `input`'s type** is read as HTML's `type` attribute states, by
//!   the keyword, ASCII case-insensitively, with the invalid value default
//!   and missing value default the Text state (`#attr-input-type`). Only
//!   the states this phase sizes differently are kept apart ([`Input`]).
//!   An `input` in the Hidden state has `display: none` from the user agent
//!   style sheet and gets no box.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_style::cascade::hints::{attribute, html_element};
use clazel_style::cascade::legacy::non_negative_integer;

/// What an `input` element is sized as.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Input {
    /// A one-line text control (§15.5.6: the Text, Search, Telephone, URL,
    /// Email and Password states), `chars` characters wide.
    Text {
        /// The character width §15.5.6 converts to pixels.
        chars: u32,
    },
    /// A button (the Submit, Reset, Button and Image states): "about one line
    /// in height and whatever width is necessary to render the text on one
    /// line" (§15.4.2, §15.5.3), which layout measures.
    Button,
    /// A checkbox or a radio button (§15.5.10).
    Check,
    /// Any other state (dates, numbers, ranges, colours, files): sized by
    /// layout as a text control of the default width.
    Other,
}

/// A replaced element and what HTML gives for its size.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Replaced {
    /// `img`: natural size 0 by 0 (§15.4.2, "represents nothing").
    Image,
    /// `input`.
    Input(Input),
    /// `textarea`: its character width and height (`cols`, `rows`).
    TextArea {
        /// `cols`: "If applying the rules for parsing non-negative integers
        /// to the attribute's value results in a number greater than zero,
        /// then the element's character width is that value; otherwise, it is
        /// 20."
        cols: u32,
        /// `rows`, likewise with 2.
        rows: u32,
    },
    /// `select` (item 6.15): drawn as a list of `rows` rows, `chars`
    /// characters wide (the longest option label, at least 1).
    Select {
        /// The visible rows: the `size` attribute when it is greater than 1,
        /// else 4 for a `multiple` select, else the number of options (at
        /// least 1, at most [`SELECT_DROPDOWN_ROWS`]): a drop-down is drawn
        /// as the list it would open.
        rows: u32,
        /// The width in characters.
        chars: u32,
    },
    /// `iframe`, with its `src` attribute (item 5.24 draws it as a link).
    Iframe {
        /// The `src` attribute's value, if it has one.
        src: Option<String>,
    },
}

/// The most rows a `select` without `multiple` or a `size` above 1 shows.
pub const SELECT_DROPDOWN_ROWS: u32 = 8;

/// Whether `n` is an HTML element named `name`.
fn named_element(arena: &Arena, n: usize, name: &str) -> bool {
    html_element(arena, n).is_some_and(|(l, _)| l.iter().copied().eq(name.chars().map(u32::from)))
}

/// Infra "strip and collapse ASCII whitespace".
fn collapse(s: &[u32]) -> String {
    let mut out = String::new();
    for word in s
        .split(|&c| matches!(c, 0x09 | 0x0A | 0x0C | 0x0D | 0x20))
        .filter(|w| !w.is_empty())
    {
        if !out.is_empty() {
            out.push(' ');
        }
        out.push_str(&string(word));
    }
    out
}

/// The `option` elements of `select` `sel` in tree order: its `option`
/// children and those of its `optgroup` children (HTML §4.10.7 "list of
/// options"; item 6.13's `list_of_options` is the proven one, this is the
/// layout's own read of the same shape).
pub fn select_options(arena: &Arena, sel: usize) -> Vec<usize> {
    let mut out = Vec::new();
    for &c in arena.children(sel) {
        if named_element(arena, c, "option") {
            out.push(c);
        } else if named_element(arena, c, "optgroup") {
            out.extend(
                arena
                    .children(c)
                    .iter()
                    .copied()
                    .filter(|&o| named_element(arena, o, "option")),
            );
        }
    }
    out
}

/// An option's label as drawn: HTML §4.10.10 "label": the `label` attribute
/// if it is not empty, else the option's text with ASCII whitespace
/// stripped and collapsed ("the `text` IDL attribute").
pub fn option_label(arena: &Arena, option: usize) -> String {
    if let Some((_, attrs)) = html_element(arena, option)
        && let Some(l) = attribute(attrs, "label")
        && !l.is_empty()
    {
        return string(l);
    }
    let mut text: Vec<u32> = Vec::new();
    for &c in arena.children(option) {
        if let ExecKind::Text { data } = arena.kind(c) {
            text.extend_from_slice(data);
        }
    }
    collapse(&text)
}

/// The `select`'s display row count, from [`Replaced::Select`]'s rule.
fn select_rows(attrs: &[ExecAttr], options: usize) -> u32 {
    let size = attribute(attrs, "size")
        .and_then(non_negative_integer)
        .and_then(|n| u32::try_from(n).ok())
        .unwrap_or(0);
    if size > 1 {
        size
    } else if attribute(attrs, "multiple").is_some() {
        4
    } else {
        u32::try_from(options)
            .unwrap_or(u32::MAX)
            .clamp(1, SELECT_DROPDOWN_ROWS)
    }
}

/// Code points to a `String`, with any that is not a scalar value replaced
/// by U+FFFD (a DOM string may hold lone surrogates).
pub fn string(s: &[u32]) -> String {
    s.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// ASCII case-insensitive equality of a DOM string and a lowercase ASCII
/// keyword.
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

/// "Rules for parsing non-negative integers" with a default for an error or
/// a value that is not greater than zero (`#attr-textarea-cols-value`),
/// clamped to `u32`.
fn positive_or(value: Option<&[u32]>, default: u32) -> u32 {
    value
        .and_then(non_negative_integer)
        .filter(|&n| n > 0)
        .map_or(default, |n| u32::try_from(n).unwrap_or(u32::MAX))
}

/// §15.5.6 steps 2 and 3: the `size` attribute "if … parsing that
/// attribute's value using the rules for parsing non-negative integers
/// doesn't generate an error", else 20. (A `size` of 0 converts to the
/// maximum character width less the average, as the formula gives.)
fn input_chars(size: Option<&[u32]>) -> u32 {
    size.and_then(non_negative_integer)
        .map_or(20, |n| u32::try_from(n).unwrap_or(u32::MAX))
}

/// What `input` element with type attribute `ty` is sized as
/// (`#attr-input-type`'s states).
fn input(ty: Option<&[u32]>, size: Option<&[u32]>) -> Input {
    let is = |k: &str| ty.is_some_and(|t| keyword(t, k));
    if is("submit") || is("reset") || is("button") || is("image") {
        Input::Button
    } else if is("checkbox") || is("radio") {
        Input::Check
    } else if [
        "date",
        "month",
        "week",
        "time",
        "datetime-local",
        "number",
        "range",
        "color",
        "file",
    ]
    .iter()
    .any(|k| is(k))
    {
        Input::Other
    } else {
        // The Text, Search, Telephone, URL, Email and Password states, and
        // the invalid and missing value defaults (the Text state).
        Input::Text {
            chars: input_chars(size),
        }
    }
}

/// Whether element `x` of `arena` is replaced in this phase, and if so what
/// it is (§15.4, §15.5; the module's modelling choices).
pub fn replaced(arena: &Arena, x: usize) -> Option<Replaced> {
    let (name, attributes) = html_element(arena, x)?;
    let named = |k: &str| name.iter().copied().eq(k.chars().map(u32::from));
    if named("img") {
        Some(Replaced::Image)
    } else if named("input") {
        Some(Replaced::Input(input(
            attribute(attributes, "type"),
            attribute(attributes, "size"),
        )))
    } else if named("textarea") {
        Some(Replaced::TextArea {
            cols: positive_or(attribute(attributes, "cols"), 20),
            rows: positive_or(attribute(attributes, "rows"), 2),
        })
    } else if named("select") {
        let options = select_options(arena, x);
        let chars = options
            .iter()
            .map(|&o| option_label(arena, o).chars().count())
            .max()
            .unwrap_or(0)
            .max(1);
        Some(Replaced::Select {
            rows: select_rows(attributes, options.len()),
            chars: u32::try_from(chars).unwrap_or(u32::MAX),
        })
    } else if named("iframe") {
        Some(Replaced::Iframe {
            src: attribute(attributes, "src").map(string),
        })
    } else {
        None
    }
}
