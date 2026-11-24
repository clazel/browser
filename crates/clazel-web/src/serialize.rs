//! HTML §13.3 "Serializing HTML fragments", the algorithm behind
//! `innerHTML` and `outerHTML`, over a `clazel-dom` arena.
//!
//! <https://html.spec.whatwg.org/multipage/parsing.html#serialising-html-fragments>
//! (the section numbers here carry the mark † of phase-7.md: they were
//! written from memory, not read at a pinned commit, and the algorithm's
//! text is not vendored, so the standard's current wording must be checked
//! before a spec header pins it).
//!
//! Tier 0, not proven: this is the serializer's own crate (`clazel-web`)
//! and not `clazel-treebuilder` or `clazel-dom` (tier 2), so that no tier
//! 2 crate holds code that is only tested. The walk is iterative (a work
//! list), so a deep tree does not overflow the stack.
//!
//! Modelling choices:
//! - The algorithm's string `s` is a `Vec<u32>` of code points, as every
//!   string of the arena is.
//! - Step 2's "let the node instead be the template element's template
//!   contents" and step 3's recursion are one work list: an element's
//!   close tag is queued first, then its children (or its template
//!   contents' children) after it, so they pop first and in tree order.
//! - "Scripting is enabled for the node" (step 3.2, text nodes) is the
//!   caller's `scripting` flag. The node's document's browsing context is
//!   not modelled.
//! - Shadow roots are not modelled (`clazel-dom` has none), so the
//!   `serializableShadowRoots` and `shadowRoots` parameters are absent, as
//!   is the `is` value of a custom element (none is stored).
//! - The `outerHTML` getter's "fake parent" is [`serialize_outer`]: the
//!   node is serialized as the only child of a parent that is not an
//!   element, so its text is escaped in the ordinary way.
//! - A node id that is not in the arena serializes as the empty string.
//!
//! Two points where this follows one reading of the standard and the
//! pinned text must settle it (both †, from memory):
//! - Escaping replaces `<` and `>` in attribute mode too, as the 2025
//!   change to the standard did, not only in text.
//! - "If current node is a `pre`, `textarea` or `listing` element and its
//!   first child is a text node starting with a line feed, append a line
//!   feed": the standard's earlier text had this step, and it is kept
//!   because the parser drops one line feed after those start tags, so
//!   without it serializing then parsing a `pre` that starts with a blank
//!   line loses the line (`tests/conformance_round_trip.rs` checks the round trip).
//!   Whether the current text still has this step is what to check.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;

/// Append the characters of `s` as code points.
fn push_str(out: &mut Vec<u32>, s: &str) {
    out.extend(s.chars().map(u32::from));
}

/// Whether the code points `v` spell the ASCII string `s`.
fn is(v: &[u32], s: &str) -> bool {
    v.len() == s.len() && v.iter().copied().eq(s.chars().map(u32::from))
}

/// Whether the code points `v` spell one of `names`.
fn is_one_of(v: &[u32], names: &[&str]) -> bool {
    names.iter().any(|n| is(v, n))
}

/// §13.3: "An element serializes as void if its element type is a void
/// element (§13.1.2: `area`, `base`, `br`, `col`, `embed`, `hr`, `img`,
/// `input`, `link`, `meta`, `source`, `track`, `wbr`), or is `basefont`,
/// `bgsound`, `frame`, `keygen`, or `param`."
fn serializes_as_void(name: &[u32]) -> bool {
    is_one_of(
        name,
        &[
            "area", "base", "basefont", "bgsound", "br", "col", "embed", "frame", "hr", "img",
            "input", "keygen", "link", "meta", "param", "source", "track", "wbr",
        ],
    )
}

/// "Escaping a string": 1. "Replace any occurrence of the `&` character by
/// the string `&amp;`." 2. "Replace any occurrences of the U+00A0
/// NO-BREAK SPACE character by the string `&nbsp;`." 3. "If the algorithm
/// was invoked in the attribute mode, replace any occurrences of the `"`
/// character by the string `&quot;`." 4. "Replace any occurrences of the `<`
/// character by the string `&lt;`, and any occurrences of the `>`
/// character by the string `&gt;`." (In the standard before 2025, step 4
/// applied only when not in attribute mode.)
fn escape(out: &mut Vec<u32>, data: &[u32], attribute_mode: bool) {
    for &c in data {
        match c {
            0x26 => push_str(out, "&amp;"),
            0xA0 => push_str(out, "&nbsp;"),
            0x22 if attribute_mode => push_str(out, "&quot;"),
            0x3C => push_str(out, "&lt;"),
            0x3E => push_str(out, "&gt;"),
            _ => out.push(c),
        }
    }
}

/// Append the qualified name: "the prefix, a colon and the local name, or
/// the local name if there is no prefix" (DOM §4.9 "qualified name").
fn push_qualified(out: &mut Vec<u32>, prefix: Option<&[u32]>, local: &[u32]) {
    if let Some(p) = prefix {
        out.extend_from_slice(p);
        out.push(0x3A);
    }
    out.extend_from_slice(local);
}

/// Step 3.2, element, "an attribute's serialized name": no namespace: the
/// local name; XML namespace: `xml:` and the local name; XMLNS namespace:
/// `xmlns` if the local name is `xmlns`, else `xmlns:` and the local name;
/// XLink namespace: `xlink:` and the local name; otherwise the qualified
/// name.
fn push_attribute_name(out: &mut Vec<u32>, a: &ExecAttr) {
    match a.namespace {
        None => out.extend_from_slice(&a.local_name),
        Some(Namespace::Xml) => {
            push_str(out, "xml:");
            out.extend_from_slice(&a.local_name);
        }
        Some(Namespace::Xmlns) => {
            if is(&a.local_name, "xmlns") {
                push_str(out, "xmlns");
            } else {
                push_str(out, "xmlns:");
                out.extend_from_slice(&a.local_name);
            }
        }
        Some(Namespace::XLink) => {
            push_str(out, "xlink:");
            out.extend_from_slice(&a.local_name);
        }
        Some(_) => push_qualified(out, a.prefix.as_deref(), &a.local_name),
    }
}

/// An item of the work list.
enum Work {
    /// Serialize this node. The flag says its parent is a `style`,
    /// `script`, `xmp`, `iframe`, `noembed`, `noframes` or `plaintext`
    /// element, or a `noscript` element with scripting enabled (step 3.2,
    /// text node): a text node's data is then appended literally.
    Node(usize, bool),
    /// An element's end tag: `</`, the tag name, `>`.
    Close(Vec<u32>),
}

/// Whether the children of an element of the given namespace and local
/// name are raw text for the serializer (step 3.2, text node).
fn raw_text_children(ns: &Option<Namespace>, name: &[u32], scripting: bool) -> bool {
    matches!(ns, Some(Namespace::Html))
        && (is_one_of(
            name,
            &[
                "style",
                "script",
                "xmp",
                "iframe",
                "noembed",
                "noframes",
                "plaintext",
            ],
        ) || (scripting && is(name, "noscript")))
}

/// Queue the children of `parent`, so that they are handled in tree order
/// before whatever is already queued. Step 2: "If the node is a `template`
/// element, then let the node instead be the template element's template
/// contents (a DocumentFragment node)."
fn queue_children(arena: &Arena, parent: usize, scripting: bool, work: &mut Vec<Work>) {
    if parent >= arena.len() {
        return;
    }
    let (container, raw) = match arena.kind(parent) {
        ExecKind::Element {
            namespace,
            local_name,
            template_contents: Some(contents),
            ..
        } if matches!(namespace, Some(Namespace::Html)) && is(local_name, "template") => {
            // The template contents is a fragment: not an element, so the
            // text in it is not raw.
            (*contents, false)
        }
        ExecKind::Element {
            namespace,
            local_name,
            ..
        } => (parent, raw_text_children(namespace, local_name, scripting)),
        _ => (parent, false),
    };
    if container >= arena.len() {
        return;
    }
    for &child in arena.children(container).iter().rev() {
        work.push(Work::Node(child, raw));
    }
}

/// Whether the first child of the element `e` is a text node whose data
/// starts with a line feed.
fn first_child_starts_with_lf(arena: &Arena, e: usize) -> bool {
    match arena.children(e).first() {
        Some(&c) => match arena.kind(c) {
            ExecKind::Text { data } => data.first() == Some(&0x0A),
            _ => false,
        },
        None => false,
    }
}

/// Step 3: serialize `node` (one child of the algorithm's node) into `out`,
/// queueing its children and end tag.
fn serialize_node(
    arena: &Arena,
    node: usize,
    parent_raw: bool,
    scripting: bool,
    out: &mut Vec<u32>,
    work: &mut Vec<Work>,
) {
    if node >= arena.len() {
        return;
    }
    match arena.kind(node) {
        // 3.2. "If current node is an Element"
        ExecKind::Element {
            namespace,
            prefix,
            local_name,
            attributes,
            ..
        } => {
            // "If current node is an element in the HTML namespace, the
            // MathML namespace, or the SVG namespace, then let tagname be
            // current node's local name. Otherwise, let tagname be current
            // node's qualified name."
            let mut tagname: Vec<u32> = Vec::new();
            match namespace {
                Some(Namespace::Html | Namespace::MathMl | Namespace::Svg) => {
                    tagname.extend_from_slice(local_name);
                }
                _ => push_qualified(&mut tagname, prefix.as_deref(), local_name),
            }
            // "Append a U+003C LESS-THAN SIGN character (<), followed by
            // tagname."
            out.push(0x3C);
            out.extend_from_slice(&tagname);
            // "For each attribute that the element has, append a U+0020
            // SPACE character, the attribute's serialized name, a U+003D
            // EQUALS SIGN character (=), a U+0022 QUOTATION MARK character
            // ("), the attribute's value, escaped in attribute mode, and a
            // second U+0022 QUOTATION MARK character (")."
            for a in attributes {
                out.push(0x20);
                push_attribute_name(out, a);
                out.push(0x3D);
                out.push(0x22);
                escape(out, &a.value, true);
                out.push(0x22);
            }
            // "Append a U+003E GREATER-THAN SIGN character (>)."
            out.push(0x3E);
            let html = matches!(namespace, Some(Namespace::Html));
            // "If current node serializes as void, then continue on to the
            // next child node at this point."
            if html && serializes_as_void(local_name) {
                return;
            }
            // Older text of the standard: a `pre`, `textarea` or `listing`
            // whose first child is a text node starting with a line feed
            // gets another line feed here (see the module comment).
            if html
                && is_one_of(local_name, &["pre", "textarea", "listing"])
                && first_child_starts_with_lf(arena, node)
            {
                out.push(0x0A);
            }
            // "Append the value of running the HTML fragment serialization
            // algorithm with current node … (thus recursing into this
            // algorithm) to s", then "</", tagname and ">": the end tag is
            // queued first so that it follows the children.
            work.push(Work::Close(tagname));
            queue_children(arena, node, scripting, work);
        }
        // 3.2. "If current node is a Text node": "If the parent of current
        // node is a style, script, xmp, iframe, noembed, noframes, or
        // plaintext element, or if the parent of current node is a
        // noscript element and scripting is enabled for the node, then
        // append the value of current node's data IDL attribute literally.
        // Otherwise, append the value of current node's data IDL attribute,
        // escaped as described below."
        ExecKind::Text { data } => {
            if parent_raw {
                out.extend_from_slice(data);
            } else {
                escape(out, data, false);
            }
        }
        // 3.2. "If current node is a Comment node": "<!--", data, "-->".
        ExecKind::Comment { data } => {
            push_str(out, "<!--");
            out.extend_from_slice(data);
            push_str(out, "-->");
        }
        // 3.2. "If current node is a ProcessingInstruction node": "<?",
        // target, a space, data and ">".
        ExecKind::ProcessingInstruction { target, data } => {
            push_str(out, "<?");
            out.extend_from_slice(target);
            out.push(0x20);
            out.extend_from_slice(data);
            out.push(0x3E);
        }
        // 3.2. "If current node is a DocumentType node": "<!DOCTYPE", a
        // space, the name and ">".
        ExecKind::DocumentType { name, .. } => {
            push_str(out, "<!DOCTYPE ");
            out.extend_from_slice(name);
            out.push(0x3E);
        }
        // A Document or DocumentFragment is not a child of anything the
        // algorithm walks; nothing is appended for one (the standard's list
        // has no entry for them).
        ExecKind::Document { .. } | ExecKind::DocumentFragment { .. } => {}
    }
}

/// Run the work list to its end.
fn run(arena: &Arena, mut work: Vec<Work>, scripting: bool) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    while let Some(item) = work.pop() {
        match item {
            Work::Node(n, raw) => serialize_node(arena, n, raw, scripting, &mut out, &mut work),
            Work::Close(tagname) => {
                push_str(&mut out, "</");
                out.extend_from_slice(&tagname);
                out.push(0x3E);
            }
        }
    }
    out
}

/// §13.3 "The HTML fragment serialization algorithm" for `node`: the
/// serialization of its children (of its template contents' children if
/// it is a `template` element), which is the `innerHTML` getter's value.
/// `scripting` is "scripting is enabled for the node".
pub fn serialize_fragment(arena: &Arena, node: usize, scripting: bool) -> Vec<u32> {
    let mut work: Vec<Work> = Vec::new();
    queue_children(arena, node, scripting, &mut work);
    run(arena, work, scripting)
}

/// The `outerHTML` getter: the serialization of `node` itself, as the only
/// child of a fake parent that is not an element (DOM Parsing and
/// Serialization §2.2†: "let fragment be a fake parent … whose only child
/// is this").
pub fn serialize_outer(arena: &Arena, node: usize, scripting: bool) -> Vec<u32> {
    run(arena, vec![Work::Node(node, false)], scripting)
}
