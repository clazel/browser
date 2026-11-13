//! "Tests needing JavaScript, images or features outside the subset are
//! counted as not run, by reason" (phase-5.md item 5.25).
//!
//! A test (or its reference) is not run when, in this order:
//!
//! 1. it is a print reftest (`-print` before the extension, or a `print`
//!    directory): paged media is not in the subset;
//! 2. it is XHTML (`.xht`, `.xhtml`: WPT serves them as
//!    `application/xhtml+xml`): the renderer draws a notice for any type but
//!    HTML and plain text, so a screenshot shows the notice and not the page.
//!    Decided by the path alone, so a reference that is not vendored can be
//!    judged too ([`xhtml`]);
//! 3. it needs script: a `script` element, or `class="reftest-wait"` on the
//!    root (which only script ends);
//! 4. it needs an image or another embedded document: `img`, `picture`,
//!    `video`, `canvas`, `object`, `embed`, `iframe`, `svg`, an `input` of
//!    type `image`, or `url(` in its CSS;
//! 5. its CSS uses a feature outside the subset: a property `clazel-style`
//!    does not know, one it parses with no effect (`transform`,
//!    `text-overflow`, the background images and their positions, sizes,
//!    repeats, attachments, origins and clips, `font-variant-caps`,
//!    `font-stretch`, `text-decoration-thickness`, `resize`), a value its
//!    grammar for the property refuses, or an at-rule it ignores
//!    (`@font-face`, `@supports`, `@import`, …). Custom properties count as
//!    outside too (`var()` is not in the subset).
//!
//! A value the subset refuses is also what a test of error handling writes
//! on purpose, so 5 may count some tests as not run that would pass; it
//! never counts as run a test that needs what we lack.

use clazel_style::sources::{StyleSheet, sheet};
use clazel_style::values::{parse_items, property};

use super::meta::{elements, parse};

/// Whether WPT's server serves `path` as XHTML, `application/xhtml+xml`
/// (by its extension, `.xht` or `.xhtml`).
pub fn xhtml(path: &str) -> bool {
    path.ends_with(".xht") || path.ends_with(".xhtml")
}

/// Why a test is not run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NotRun {
    /// Paged media.
    Print,
    /// XHTML, which the renderer does not take (2).
    Xhtml,
    /// Script.
    Script,
    /// An image or an embedded document (the element or `url(`).
    Images(String),
    /// A CSS feature outside the subset (the property, value or at-rule).
    OutsideSubset(String),
}

/// The properties `clazel-style` parses with no effect that change what is
/// drawn (`cursor` and `pointer-events` change nothing in a screenshot).
const NO_EFFECT: &[&str] = &[
    "transform",
    "text-overflow",
    "background-image",
    "background-position",
    "background-size",
    "background-repeat",
    "background-attachment",
    "background-origin",
    "background-clip",
    "font-variant-caps",
    "font-stretch",
    "text-decoration-thickness",
    "resize",
];

fn text(s: &[u32]) -> String {
    s.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// The reason a declaration is outside the subset, if it is.
fn declaration(d: &sheet::Declaration) -> Option<NotRun> {
    let name = text(&d.name).to_ascii_lowercase();
    if NO_EFFECT.contains(&name.as_str()) {
        return Some(NotRun::OutsideSubset(name));
    }
    let Some(p) = property(&d.name) else {
        return Some(NotRun::OutsideSubset(name));
    };
    if parse_items(p, d.value.src(), false).is_none() {
        return Some(NotRun::OutsideSubset(format!("{name}: a value")));
    }
    None
}

/// The first reason the page at `path` with `bytes` is not run, if any.
pub fn classify(path: &str, bytes: &[u8]) -> Option<NotRun> {
    let file = path.rsplit('/').next().unwrap_or(path);
    let stem = file.split('.').next().unwrap_or(file);
    if stem.ends_with("-print") || path.split('/').any(|d| d == "print") {
        return Some(NotRun::Print);
    }
    if xhtml(path) {
        return Some(NotRun::Xhtml);
    }
    let arena = parse(bytes);
    let els = elements(&arena);
    let attr = |attributes: &[clazel_dom::exec::ExecAttr], name: &str| {
        attributes
            .iter()
            .find(|a| a.namespace.is_none() && text(&a.local_name) == name)
            .map(|a| text(&a.value))
    };
    for (name, attributes) in &els {
        if name == "script" {
            return Some(NotRun::Script);
        }
        if name == "html"
            && attr(attributes, "class")
                .is_some_and(|c| c.split_ascii_whitespace().any(|t| t == "reftest-wait"))
        {
            return Some(NotRun::Script);
        }
    }
    for (name, attributes) in &els {
        let image_input = name == "input"
            && attr(attributes, "type").is_some_and(|t| t.eq_ignore_ascii_case("image"));
        if image_input
            || [
                "img", "picture", "video", "canvas", "object", "embed", "iframe", "svg",
            ]
            .contains(&name.as_str())
        {
            return Some(NotRun::Images(name.clone()));
        }
    }
    // Every `style` element's sheet, then every `style` attribute.
    for id in 0..arena.len() {
        let clazel_dom::exec::ExecKind::Element {
            local_name,
            attributes,
            ..
        } = arena.kind(id)
        else {
            continue;
        };
        if text(local_name) == "style" {
            let css: Vec<u32> = arena
                .children(id)
                .iter()
                .filter_map(|&c| match arena.kind(c) {
                    clazel_dom::exec::ExecKind::Text { data } => Some(data.clone()),
                    _ => None,
                })
                .flatten()
                .collect();
            let lower = text(&css).to_ascii_lowercase();
            if lower.contains("url(") {
                return Some(NotRun::Images("url( in a style sheet".to_owned()));
            }
            let s = StyleSheet::parse(&css);
            if let Some(i) = s.ignored.first() {
                return Some(NotRun::OutsideSubset(format!("{i:?}")));
            }
            if lower.contains("@font-face")
                || lower.contains("@supports")
                || lower.contains("@import")
            {
                return Some(NotRun::OutsideSubset("an at-rule".to_owned()));
            }
            for rule in &s.rules {
                if let Some(r) = rule.declarations.iter().find_map(declaration) {
                    return Some(r);
                }
            }
        }
        if let Some(v) = attr(attributes, "style") {
            if v.to_ascii_lowercase().contains("url(") {
                return Some(NotRun::Images("url( in a style attribute".to_owned()));
            }
            let value: Vec<u32> = v.chars().map(u32::from).collect();
            if let Some(r) = sheet::style_attribute(&value).iter().find_map(declaration) {
                return Some(r);
            }
        }
    }
    None
}
