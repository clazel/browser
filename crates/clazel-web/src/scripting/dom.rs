//! The few reads of the document the script steps make: attributes, child
//! text content, connectedness and the document base URL, over the
//! parser's `clazel-dom` arena. Every walk is iterative and bounded by the
//! arena's size, and every id is checked against it before it is read.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;

/// `s` as code points.
pub(crate) fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// Code points as a string, a lone surrogate or a non-character value as
/// U+FFFD.
pub(crate) fn text(v: &[u32]) -> String {
    v.iter()
        .map(|c| char::from_u32(*c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// ASCII lowercase of one code point.
fn lower(c: u32) -> u32 {
    if (0x41..=0x5A).contains(&c) {
        c.saturating_add(0x20)
    } else {
        c
    }
}

/// Infra's "ASCII case-insensitive" match of `a` with the ASCII string `b`.
pub(crate) fn eq_ignore_ascii_case(a: &[u32], b: &str) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b.chars())
            .all(|(x, y)| lower(*x) == lower(u32::from(y)))
}

/// Infra's ASCII whitespace: TAB, LF, FF, CR and SPACE.
fn is_ascii_whitespace(c: u32) -> bool {
    matches!(c, 0x09 | 0x0A | 0x0C | 0x0D | 0x20)
}

/// Infra's "strip leading and trailing ASCII whitespace".
pub(crate) fn strip(v: &[u32]) -> &[u32] {
    let start = v
        .iter()
        .position(|c| !is_ascii_whitespace(*c))
        .unwrap_or(v.len());
    let end = v
        .iter()
        .rposition(|c| !is_ascii_whitespace(*c))
        .map_or(start, |i| i.saturating_add(1));
    v.get(start..end).unwrap_or(&[])
}

/// Whether `n` names a node of the arena.
pub(crate) fn exists(arena: &Arena, n: usize) -> bool {
    n < arena.len()
}

/// The attributes of `n` if it is an HTML element whose local name is
/// `name`.
pub(crate) fn html_element<'a>(arena: &'a Arena, n: usize, name: &str) -> Option<&'a [ExecAttr]> {
    if !exists(arena, n) {
        return None;
    }
    match arena.kind(n) {
        ExecKind::Element {
            namespace: Some(Namespace::Html),
            local_name,
            attributes,
            ..
        } if local_name.iter().copied().eq(name.chars().map(u32::from)) => Some(attributes),
        _ => None,
    }
}

/// The value of the attribute `name` in no namespace, if there is one.
pub(crate) fn attribute<'a>(attributes: &'a [ExecAttr], name: &str) -> Option<&'a [u32]> {
    attributes
        .iter()
        .find(|a| {
            a.namespace.is_none() && a.local_name.iter().copied().eq(name.chars().map(u32::from))
        })
        .map(|a| a.value.as_slice())
}

/// DOM §4.2.? "child text content": the concatenation of the data of the
/// node's `Text` children, in tree order.
pub(crate) fn child_text_content(arena: &Arena, n: usize) -> Vec<u32> {
    let mut out = Vec::new();
    if !exists(arena, n) {
        return out;
    }
    for &c in arena.children(n) {
        if exists(arena, c)
            && let ExecKind::Text { data } = arena.kind(c)
        {
            out.extend_from_slice(data);
        }
    }
    out
}

/// DOM "connected": the node's shadow-including root is a document. There
/// are no shadow roots here, so its root is followed up the parents; the
/// document is node 0. A template's contents are not connected (their root
/// is the fragment).
pub(crate) fn is_connected(arena: &Arena, n: usize) -> bool {
    let mut node = n;
    // A parent chain is at most the arena's size long.
    for _ in 0..=arena.len() {
        if !exists(arena, node) {
            return false;
        }
        match arena.parent(node) {
            Some(p) => node = p,
            None => return node == 0 && matches!(arena.kind(0), ExecKind::Document { .. }),
        }
    }
    false
}

/// The document's URL (node 0's), as code points.
pub(crate) fn document_url(arena: &Arena) -> Vec<u32> {
    if exists(arena, 0)
        && let ExecKind::Document { url, .. } = arena.kind(0)
    {
        return url.clone();
    }
    Vec::new()
}

/// URL §4.4 the basic URL parser over `input` with `base`: `None` on
/// failure, or for input with a surrogate (the parser takes scalar values).
pub(crate) fn parse_url(input: &[u32], base: Option<&ParsedUrl>) -> Option<ParsedUrl> {
    if input.iter().any(|c| char::from_u32(*c).is_none()) {
        return None;
    }
    basic_url_parser(input, base)
}

/// HTML §2.4.1† "document base URL": the frozen base URL of the first
/// `base` element with an `href` in tree order (its value parsed against
/// the document's URL, the fallback base URL here; that URL if the parse
/// fails), else the document's URL. As the renderer's pipeline computes it.
pub(crate) fn document_base_url(arena: &Arena) -> Option<ParsedUrl> {
    let fallback = parse_url(&document_url(arena), None);
    let mut stack: Vec<usize> = vec![0];
    let mut budget = arena.len();
    while let Some(id) = stack.pop() {
        if !exists(arena, id) || budget == 0 {
            continue;
        }
        budget = budget.saturating_sub(1);
        if let Some(attributes) = html_element(arena, id, "base")
            && let Some(href) = attribute(attributes, "href")
        {
            return parse_url(href, fallback.as_ref()).or(fallback);
        }
        stack.extend(arena.children(id).iter().rev());
    }
    fallback
}

/// A URL serialized (URL §4.5, with its fragment), as a string.
pub(crate) fn serialize(url: &ParsedUrl) -> String {
    text(&url.serialize(false))
}
