//! HTML §13.4† "the HTML fragment parsing algorithm" into the page's arena,
//! for `innerHTML`, `outerHTML`, `insertAdjacentHTML` and
//! `Range.createContextualFragment`.
//!
//! The parsing is `clazel-treebuilder`'s (`parse_fragment_real`, proven
//! against its spec in tier 2); it builds its own arena, so this module only
//! supplies the context (the context element's namespace, name, attributes,
//! the document's mode, and whether the context is in a form) and then
//! copies the parsed nodes into the page's arena.
//!
//! Modelling choices:
//! - **Scripting is enabled** (the flag is true): the parser's `noscript`
//!   handling is the one a scripted page has, as the serializer's.
//! - **The copy** makes each node fresh in the page's arena and links it
//!   with the proven "pre-insert" (so a failure to link is impossible: the
//!   parent is a fresh element or fragment); a template's contents get
//!   `create_template_contents` and are filled the same way. A form owner is
//!   not copied (`form_owner` is `None`): the page's forms are not wired to
//!   script yet (Phase 6's form submission reads the parser's own owner).
//! - **The node limit:** if the arena cannot hold the copy, the result is
//!   `None` and the caller throws `NotSupportedError`; the nodes already
//!   made stay in the arena, unreachable from the tree.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_treebuilder::exec::driver::parse_fragment_real;
use clazel_treebuilder::exec::step::ExecContext;
use clazel_treebuilder::exec::types::EncFnsExec;

struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

pub(crate) fn copy_ns(ns: &Namespace) -> Namespace {
    match ns {
        Namespace::Html => Namespace::Html,
        Namespace::MathMl => Namespace::MathMl,
        Namespace::Svg => Namespace::Svg,
        Namespace::XLink => Namespace::XLink,
        Namespace::Xml => Namespace::Xml,
        Namespace::Xmlns => Namespace::Xmlns,
    }
}

fn copy_mode(m: &DocumentMode) -> DocumentMode {
    match m {
        DocumentMode::NoQuirks => DocumentMode::NoQuirks,
        DocumentMode::Quirks => DocumentMode::Quirks,
        DocumentMode::LimitedQuirks => DocumentMode::LimitedQuirks,
    }
}

pub(crate) fn copy_attr(a: &ExecAttr) -> ExecAttr {
    ExecAttr {
        namespace: a.namespace.as_ref().map(copy_ns),
        prefix: a.prefix.clone(),
        local_name: a.local_name.clone(),
        value: a.value.clone(),
    }
}

fn is_html_form(arena: &Arena, n: usize) -> bool {
    matches!(
        arena.kind(n),
        ExecKind::Element {
            namespace: Some(Namespace::Html),
            local_name,
            ..
        } if local_name.iter().copied().eq("form".chars().map(u32::from))
    )
}

/// The fragment parsing algorithm's context for element `context` of
/// `arena`: HTML §13.4† step 4 (the document's mode) and "the context
/// element ... is a form element or has a form element ancestor".
fn context_of(arena: &Arena, context: usize) -> Option<ExecContext> {
    let ExecKind::Element {
        namespace,
        local_name,
        attributes,
        ..
    } = arena.kind(context)
    else {
        return None;
    };
    let mode = match arena.kind(0) {
        ExecKind::Document { mode, .. } => copy_mode(mode),
        _ => DocumentMode::NoQuirks,
    };
    let mut in_form = false;
    let mut cur = Some(context);
    while let Some(n) = cur {
        if is_html_form(arena, n) {
            in_form = true;
            break;
        }
        cur = arena.parent(n);
    }
    Some(ExecContext {
        ns: namespace.as_ref().map_or(Namespace::Html, copy_ns),
        name: local_name.clone(),
        attrs: attributes.iter().map(copy_attr).collect(),
        mode,
        in_form,
    })
}

/// Copies the node `src` of `from` into `to` (detached), with its
/// descendants and template contents. `None` at the node limit.
fn import_node(to: &mut Arena, from: &Arena, src: usize) -> Option<usize> {
    let mut stack: Vec<(usize, usize)> = Vec::new();
    let top = make_node(to, from, src, &mut stack)?;
    while let Some((s, d)) = stack.pop() {
        // `s` is a source container (an element's children, a template's
        // contents) and `d` the new node that gets copies of its children.
        for &c in from.children(s) {
            let n = make_node(to, from, c, &mut stack)?;
            if to.pre_insert(n, d, None).is_some() {
                return None;
            }
        }
    }
    Some(top)
}

/// Makes the copy of the single node `src` (no children) and queues the
/// containers whose children are to follow.
fn make_node(
    to: &mut Arena,
    from: &Arena,
    src: usize,
    stack: &mut Vec<(usize, usize)>,
) -> Option<usize> {
    let (kind, template) = match from.kind(src) {
        ExecKind::Element {
            namespace,
            prefix,
            local_name,
            attributes,
            template_contents,
            ..
        } => (
            ExecKind::Element {
                namespace: namespace.as_ref().map(copy_ns),
                prefix: prefix.clone(),
                local_name: local_name.clone(),
                attributes: attributes.iter().map(copy_attr).collect(),
                template_contents: None,
                form_owner: None,
            },
            *template_contents,
        ),
        ExecKind::Text { data } => (ExecKind::Text { data: data.clone() }, None),
        ExecKind::Comment { data } => (ExecKind::Comment { data: data.clone() }, None),
        ExecKind::ProcessingInstruction { target, data } => (
            ExecKind::ProcessingInstruction {
                target: target.clone(),
                data: data.clone(),
            },
            None,
        ),
        ExecKind::DocumentFragment { .. } => (ExecKind::DocumentFragment { host: None }, None),
        // A parse result has no other node kinds below its root.
        ExecKind::Document { .. } | ExecKind::DocumentType { .. } => return None,
    };
    let n = to.create(kind)?;
    stack.push((src, n));
    if let Some(t) = template {
        let c = to.create_template_contents(n)?;
        stack.push((t, c));
    }
    Some(n)
}

/// HTML §13.4† "the HTML fragment parsing algorithm" for `html` with the
/// element `context` of `arena` as the context: a new `DocumentFragment` of
/// `arena` holding the parsed nodes (step 23, "Return the child nodes of
/// root"). `None` if `context` is not an element or the node limit is hit.
pub(crate) fn parse_fragment(arena: &mut Arena, context: usize, html: &[u32]) -> Option<usize> {
    let ctx = context_of(arena, context)?;
    let (parsed, root, _) = parse_fragment_real(&NoEnc, html, ctx, true);
    let fragment = arena.create(ExecKind::DocumentFragment { host: None })?;
    let from = &parsed.arena;
    for &c in from.children(root) {
        let n = import_node(arena, from, c)?;
        if arena.pre_insert(n, fragment, None).is_some() {
            return None;
        }
    }
    Some(fragment)
}
