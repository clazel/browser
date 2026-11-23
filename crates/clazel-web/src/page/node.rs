//! The node interfaces (DOM §4†): `Node`, `Document`, `DocumentType`,
//! `DocumentFragment`, `CharacterData`, `Text`, `Comment`, `Element`, the
//! HTML element interfaces the bindings expose, `NodeList`, `HTMLCollection`
//! and `DOMTokenList`, over `clazel-dom`'s arena.
//!
//! <https://dom.spec.whatwg.org/#nodes>
//!
//! Each method cites the algorithm it implements. The tree mutations are
//! `clazel-dom`'s proven operations (`pre_insert`, `replace`, `replace_all`,
//! `remove`, `clone_node`, `clone_deep`, the attribute changes, `set_data`);
//! this file checks their preconditions first, so a call that would break
//! one throws instead.
//!
//! The mutations go through [`super::mutation`] (the one place the arena is
//! changed: records for mutation observers and the live ranges' updates run
//! around `clazel-dom`'s operations); `innerHTML`, `outerHTML` and
//! `insertAdjacent*` parse with [`super::fragment`]; `Attr` and
//! `NamedNodeMap` are [`super::attr`]; `Range` is [`super::range`].
//!
//! Not implemented (the generated defaults throw `NotSupportedError`):
//! `moveBefore`, `createEvent`, `setHTML*`, `getHTML` and the other sanitizer
//! members, `createElementNS` and `setAttributeNS` for a namespace outside
//! Infra §8's six (the arena's `Namespace` has no other), the
//! `ProcessingInstruction` pseudo-attributes of the curated IDL, the
//! `Document.forms`, `images`, `links` and the like, and the HTML elements'
//! attributes other than `[Reflect]` ones, `HTMLTitleElement.text` and
//! `dataset`. `Document.implementation` and `new Document()` need a second
//! document, which the single arena cannot hold.

use super::NsFilter;
use super::fragment::parse_fragment;
use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, DomError, Namespace};
use clazel_js::{Result, Scope};
use clazel_webidl::convert::DomString;
use clazel_webidl::exception::DomErrorName;
use clazel_webidl::generated::bindings::*;
use clazel_webidl::platform::ObjectKey;

use super::{
    Collection, Object, Page, WINDOW, dom_error, page, points_to_units, str_points, str_units,
    type_error, units_to_points,
};

// ---------------------------------------------------------------------------
// Reading the arena

const HTML_NS: &str = "http://www.w3.org/1999/xhtml";
const SVG_NS: &str = "http://www.w3.org/2000/svg";
const MATHML_NS: &str = "http://www.w3.org/1998/Math/MathML";

/// The node a key names, or a `TypeError`.
pub(crate) fn node_of(scope: &mut Scope<'_>, key: ObjectKey) -> Result<usize> {
    match page(scope)?.key_node(key) {
        Some(n) => Ok(n),
        None => Err(type_error(scope, "not a node")),
    }
}

/// The element a key names, or a `TypeError`.
pub(crate) fn element_of(scope: &mut Scope<'_>, key: ObjectKey) -> Result<usize> {
    let n = node_of(scope, key)?;
    if is_element(&page(scope)?.arena, n) {
        Ok(n)
    } else {
        Err(type_error(scope, "not an element"))
    }
}

fn key(n: usize) -> ObjectKey {
    Page::node_key(n)
}

pub(crate) fn is_element(arena: &Arena, n: usize) -> bool {
    n < arena.len() && matches!(arena.kind(n), ExecKind::Element { .. })
}

fn is_html_element(arena: &Arena, n: usize) -> bool {
    n < arena.len()
        && matches!(
            arena.kind(n),
            ExecKind::Element {
                namespace: Some(Namespace::Html),
                ..
            }
        )
}

fn local_name_of(arena: &Arena, n: usize) -> Option<&[u32]> {
    match arena.kind(n) {
        ExecKind::Element { local_name, .. } => Some(local_name.as_slice()),
        _ => None,
    }
}

fn attributes_of(arena: &Arena, n: usize) -> &[ExecAttr] {
    match arena.kind(n) {
        ExecKind::Element { attributes, .. } => attributes.as_slice(),
        _ => &[],
    }
}

fn eq_str(points: &[u32], s: &str) -> bool {
    points.iter().copied().eq(s.chars().map(u32::from))
}

fn ascii_lower(points: &[u32]) -> Vec<u32> {
    points
        .iter()
        .map(|&c| {
            if (0x41..=0x5A).contains(&c) {
                c | 0x20
            } else {
                c
            }
        })
        .collect()
}

fn ascii_upper(points: &[u32]) -> Vec<u32> {
    points
        .iter()
        .map(|&c| {
            if (0x61..=0x7A).contains(&c) {
                c & !0x20
            } else {
                c
            }
        })
        .collect()
}

fn is_ascii_whitespace(c: u32) -> bool {
    matches!(c, 0x09 | 0x0A | 0x0C | 0x0D | 0x20)
}

/// An attribute's qualified name (DOM §4.9.2†: "its namespace prefix,
/// followed by ':', followed by its local name, if its namespace prefix is
/// non-null; otherwise its local name").
fn qualified(a: &ExecAttr) -> Vec<u32> {
    match &a.prefix {
        Some(p) => {
            let mut q = p.clone();
            q.push(u32::from(':'));
            q.extend_from_slice(&a.local_name);
            q
        }
        None => a.local_name.clone(),
    }
}

/// DOM §4.9† "get an attribute by name": "If element is in the HTML
/// namespace and its node document is an HTML document, then set
/// qualifiedName to qualifiedName in ASCII lowercase. Return the first
/// attribute in element's attribute list whose qualified name is
/// qualifiedName." (The document is an HTML document.)
fn attribute_index(arena: &Arena, e: usize, name: &[u32]) -> Option<usize> {
    let name = if is_html_element(arena, e) {
        ascii_lower(name)
    } else {
        name.to_vec()
    };
    attributes_of(arena, e)
        .iter()
        .position(|a| qualified(a) == name)
}

/// The value of the attribute named `name`, if there is one.
pub(crate) fn attribute_value(arena: &Arena, e: usize, name: &[u32]) -> Option<Vec<u32>> {
    let i = attribute_index(arena, e, name)?;
    attributes_of(arena, e).get(i).map(|a| a.value.clone())
}

/// DOM §4.9† `setAttribute` steps 3 to 5: "Let attribute be the first
/// attribute ... If attribute is null, create an attribute whose local name
/// is qualifiedName, value is value, and node document is this's node
/// document, then append this attribute to this, and then return. Change
/// attribute to value." (Step 2's lowercasing is in [`attribute_index`].)
pub(crate) fn set_attribute_value(page: &mut Page, e: usize, name: &[u32], value: Vec<u32>) {
    match attribute_index(&page.arena, e, name) {
        Some(i) => page.attr_change(e, i, value),
        None => {
            let local_name = if is_html_element(&page.arena, e) {
                ascii_lower(name)
            } else {
                name.to_vec()
            };
            page.attr_append(
                e,
                ExecAttr {
                    namespace: None,
                    prefix: None,
                    local_name,
                    value,
                },
            );
        }
    }
}

/// DOM §4.9† "remove an attribute by name".
pub(crate) fn remove_attribute_named(page: &mut Page, e: usize, name: &[u32]) {
    if let Some(i) = attribute_index(&page.arena, e, name) {
        page.attr_remove(e, i);
    }
}

/// The attribute list of element `e` (empty for another node).
pub(crate) fn attributes_of_element(arena: &Arena, e: usize) -> &[ExecAttr] {
    attributes_of(arena, e)
}

/// Whether `n` is an HTML element.
pub(crate) fn is_html_element_node(arena: &Arena, n: usize) -> bool {
    is_html_element(arena, n)
}

/// Whether `n` is an HTML element with local name `name`.
pub(crate) fn is_html_named(arena: &Arena, n: usize, name: &str) -> bool {
    is_html_element(arena, n) && local_name_of(arena, n).is_some_and(|l| eq_str(l, name))
}

/// A node's data, if it is character data.
pub(crate) fn data_of_node(arena: &Arena, n: usize) -> Option<&[u32]> {
    data_of(arena, n)
}

/// A namespace's URI as code points.
pub(crate) fn namespace_uri_points(ns: &Namespace) -> Vec<u32> {
    str_points(match ns {
        Namespace::Html => HTML_NS,
        Namespace::Svg => SVG_NS,
        Namespace::MathMl => MATHML_NS,
        Namespace::XLink => "http://www.w3.org/1999/xlink",
        Namespace::Xml => "http://www.w3.org/XML/1998/namespace",
        Namespace::Xmlns => "http://www.w3.org/2000/xmlns/",
    })
}

/// The namespace with URI `uri`, if it is one of Infra §8's six.
pub(crate) fn namespace_from_uri(uri: &[u32]) -> Option<Namespace> {
    [
        Namespace::Html,
        Namespace::Svg,
        Namespace::MathMl,
        Namespace::XLink,
        Namespace::Xml,
        Namespace::Xmlns,
    ]
    .into_iter()
    .find(|n| namespace_uri_points(n) == uri)
}

/// The interface a node's wrapper has (see the module's modelling choices
/// in `super`).
pub(crate) fn interface_of_node(arena: &Arena, n: usize) -> InterfaceId {
    match arena.kind(n) {
        ExecKind::Document { .. } => InterfaceId::Document,
        ExecKind::DocumentType { .. } => InterfaceId::DocumentType,
        ExecKind::Text { .. } => InterfaceId::Text,
        ExecKind::Comment { .. } => InterfaceId::Comment,
        ExecKind::ProcessingInstruction { .. } => InterfaceId::ProcessingInstruction,
        ExecKind::DocumentFragment { .. } => InterfaceId::DocumentFragment,
        ExecKind::Element {
            namespace: Some(Namespace::Html),
            local_name,
            ..
        } => {
            let table: &[(&str, InterfaceId)] = &[
                ("html", InterfaceId::HTMLHtmlElement),
                ("head", InterfaceId::HTMLHeadElement),
                ("title", InterfaceId::HTMLTitleElement),
                ("body", InterfaceId::HTMLBodyElement),
                ("div", InterfaceId::HTMLDivElement),
                ("span", InterfaceId::HTMLSpanElement),
                ("p", InterfaceId::HTMLParagraphElement),
                ("a", InterfaceId::HTMLAnchorElement),
                // HTML §3.2.2† "element interfaces": the obsolete and
                // unknown names that HTMLUnknownElement is for.
                ("applet", InterfaceId::HTMLUnknownElement),
                ("bgsound", InterfaceId::HTMLUnknownElement),
                ("blink", InterfaceId::HTMLUnknownElement),
                ("isindex", InterfaceId::HTMLUnknownElement),
                ("keygen", InterfaceId::HTMLUnknownElement),
                ("multicol", InterfaceId::HTMLUnknownElement),
                ("nextid", InterfaceId::HTMLUnknownElement),
                ("spacer", InterfaceId::HTMLUnknownElement),
            ];
            table
                .iter()
                .find(|(name, _)| eq_str(local_name, name))
                .map_or(InterfaceId::HTMLElement, |(_, i)| *i)
        }
        ExecKind::Element { .. } => InterfaceId::Element,
    }
}

fn parent(arena: &Arena, n: usize) -> Option<usize> {
    arena.parent(n)
}

fn children(arena: &Arena, n: usize) -> Vec<usize> {
    arena.children(n).to_vec()
}

fn element_children(arena: &Arena, n: usize) -> Vec<usize> {
    arena
        .children(n)
        .iter()
        .copied()
        .filter(|&c| is_element(arena, c))
        .collect()
}

/// The descendants of `root` in tree order (not `root`), iteratively.
fn descendants(arena: &Arena, root: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut stack: Vec<usize> = arena.children(root).iter().rev().copied().collect();
    while let Some(n) = stack.pop() {
        out.push(n);
        stack.extend(arena.children(n).iter().rev().copied());
    }
    out
}

/// DOM §4.4† "descendant text content": the data of the Text descendants,
/// in tree order.
fn descendant_text(arena: &Arena, n: usize) -> Vec<u32> {
    let mut out = Vec::new();
    for d in descendants(arena, n) {
        if let ExecKind::Text { data } = arena.kind(d) {
            out.extend_from_slice(data);
        }
    }
    out
}

fn data_of(arena: &Arena, n: usize) -> Option<&[u32]> {
    match arena.kind(n) {
        ExecKind::Text { data }
        | ExecKind::Comment { data }
        | ExecKind::ProcessingInstruction { data, .. } => Some(data.as_slice()),
        _ => None,
    }
}

pub(crate) fn dom_error_of(scope: &mut Scope<'_>, e: DomError) -> clazel_js::Error {
    match e {
        DomError::HierarchyRequest => dom_error(
            scope,
            DomErrorName::HierarchyRequestError,
            "The operation would yield an incorrect node tree.",
        ),
        DomError::NotFound => dom_error(
            scope,
            DomErrorName::NotFoundError,
            "The node is not a child of this node.",
        ),
    }
}

/// A new node, or a `NotSupportedError` at the arena's node limit.
fn create(scope: &mut Scope<'_>, kind: ExecKind) -> Result<usize> {
    match page(scope)?.arena.create(kind) {
        Some(n) => Ok(n),
        None => Err(dom_error(
            scope,
            DomErrorName::NotSupportedError,
            "the document has too many nodes",
        )),
    }
}

// ---------------------------------------------------------------------------
// Tree mutation

/// DOM §4.2.3† "pre-insert" node into parent before child.
fn pre_insert(
    scope: &mut Scope<'_>,
    node: usize,
    parent: usize,
    child: Option<usize>,
) -> Result<()> {
    match page(scope)?.insert_node(node, parent, child) {
        Some(e) => Err(dom_error_of(scope, e)),
        None => Ok(()),
    }
}

/// DOM §4.2.4† "converting nodes into a node": "Let node be null. Replace
/// each string in nodes with a new Text node whose data is the string and
/// node document is document. If nodes contains one node, then set node to
/// nodes[0]. Otherwise, set node to a new DocumentFragment node whose node
/// document is document, and then append each node in nodes, if any, to
/// it."
fn convert_nodes(scope: &mut Scope<'_>, nodes: Vec<NodeOrDOMString>) -> Result<usize> {
    let mut list = Vec::new();
    for n in nodes {
        match n {
            NodeOrDOMString::Node(k) => list.push(node_of(scope, k)?),
            NodeOrDOMString::DOMString(s) => {
                let t = create(
                    scope,
                    ExecKind::Text {
                        data: units_to_points(&s),
                    },
                )?;
                list.push(t);
            }
        }
    }
    if let [only] = list.as_slice() {
        return Ok(*only);
    }
    let f = create(scope, ExecKind::DocumentFragment { host: None })?;
    for n in list {
        pre_insert(scope, n, f, None)?;
    }
    Ok(f)
}

fn node_keys(scope: &[NodeOrDOMString]) -> Vec<ObjectKey> {
    scope
        .iter()
        .filter_map(|n| match n {
            NodeOrDOMString::Node(k) => Some(*k),
            NodeOrDOMString::DOMString(_) => None,
        })
        .collect()
}

/// `ParentNode.prepend(nodes)` (DOM §4.2.6†): "Let node be the result of
/// converting nodes into a node given nodes and this's node document.
/// Pre-insert node into this before this's first child."
fn prepend(scope: &mut Scope<'_>, this: ObjectKey, nodes: Vec<NodeOrDOMString>) -> Result<()> {
    let p = node_of(scope, this)?;
    let n = convert_nodes(scope, nodes)?;
    let first = page(scope)?.arena.children(p).first().copied();
    pre_insert(scope, n, p, first)
}

/// `ParentNode.append(nodes)`: "... Append node to this." (pre-insert
/// before null).
fn append(scope: &mut Scope<'_>, this: ObjectKey, nodes: Vec<NodeOrDOMString>) -> Result<()> {
    let p = node_of(scope, this)?;
    let n = convert_nodes(scope, nodes)?;
    pre_insert(scope, n, p, None)
}

/// `ParentNode.replaceChildren(nodes)`: "Let node be the result of
/// converting nodes into a node. Ensure pre-insertion validity of node into
/// this before null. Replace all with node within this."
fn replace_children(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    nodes: Vec<NodeOrDOMString>,
) -> Result<()> {
    let p = node_of(scope, this)?;
    let n = convert_nodes(scope, nodes)?;
    if let Some(e) = page(scope)?.arena.ensure_pre_insertion_validity(n, p, None) {
        return Err(dom_error_of(scope, e));
    }
    page(scope)?.replace_all_with(Some(n), p);
    Ok(())
}

/// `ChildNode.before(nodes)` (DOM §4.2.8†): "1. Let parent be this's parent.
/// 2. If parent is null, then return. 3. Let viablePreviousSibling be this's
/// first preceding sibling not in nodes; otherwise null. 4. Let node be the
/// result of converting nodes into a node. 5. If viablePreviousSibling is
/// null, then set it to parent's first child; otherwise to
/// viablePreviousSibling's next sibling. 6. Pre-insert node into parent
/// before viablePreviousSibling."
fn before(scope: &mut Scope<'_>, this: ObjectKey, nodes: Vec<NodeOrDOMString>) -> Result<()> {
    let me = node_of(scope, this)?;
    let Some(p) = parent(&page(scope)?.arena, me) else {
        return Ok(());
    };
    let excluded: Vec<usize> = node_keys(&nodes)
        .into_iter()
        .filter_map(|k| page_key_node(scope, k))
        .collect();
    let viable = {
        let arena = &page(scope)?.arena;
        let mut cur = arena.previous_sibling(me);
        while let Some(s) = cur {
            if !excluded.contains(&s) {
                break;
            }
            cur = arena.previous_sibling(s);
        }
        cur
    };
    let node = convert_nodes(scope, nodes)?;
    let arena = &page(scope)?.arena;
    let reference = match viable {
        None => arena.children(p).first().copied(),
        Some(v) => arena.next_sibling(v),
    };
    pre_insert(scope, node, p, reference)
}

fn page_key_node(scope: &mut Scope<'_>, k: ObjectKey) -> Option<usize> {
    page(scope).ok()?.key_node(k)
}

fn viable_next_sibling(
    scope: &mut Scope<'_>,
    me: usize,
    nodes: &[NodeOrDOMString],
) -> Result<Option<usize>> {
    let excluded: Vec<usize> = node_keys(nodes)
        .into_iter()
        .filter_map(|k| page_key_node(scope, k))
        .collect();
    let arena = &page(scope)?.arena;
    let mut cur = arena.next_sibling(me);
    while let Some(s) = cur {
        if !excluded.contains(&s) {
            break;
        }
        cur = arena.next_sibling(s);
    }
    Ok(cur)
}

/// `ChildNode.after(nodes)`: "3. Let viableNextSibling be this's first
/// following sibling not in nodes; otherwise null. 4. Let node be the result
/// of converting nodes into a node. 5. Pre-insert node into parent before
/// viableNextSibling."
fn after(scope: &mut Scope<'_>, this: ObjectKey, nodes: Vec<NodeOrDOMString>) -> Result<()> {
    let me = node_of(scope, this)?;
    let Some(p) = parent(&page(scope)?.arena, me) else {
        return Ok(());
    };
    let viable = viable_next_sibling(scope, me, &nodes)?;
    let node = convert_nodes(scope, nodes)?;
    pre_insert(scope, node, p, viable)
}

/// `ChildNode.replaceWith(nodes)`: "... 5. If this's parent is parent,
/// replace this with node within parent. (This could have been inserted
/// into node.) 6. Otherwise, pre-insert node into parent before
/// viableNextSibling."
fn replace_with(scope: &mut Scope<'_>, this: ObjectKey, nodes: Vec<NodeOrDOMString>) -> Result<()> {
    let me = node_of(scope, this)?;
    let Some(p) = parent(&page(scope)?.arena, me) else {
        return Ok(());
    };
    let viable = viable_next_sibling(scope, me, &nodes)?;
    let node = convert_nodes(scope, nodes)?;
    if parent(&page(scope)?.arena, me) == Some(p) {
        match page(scope)?.replace_node(me, node, p) {
            Some(e) => Err(dom_error_of(scope, e)),
            None => Ok(()),
        }
    } else {
        pre_insert(scope, node, p, viable)
    }
}

/// `ChildNode.remove()`: "If this's parent is null, then return. Remove
/// this."
fn remove(scope: &mut Scope<'_>, this: ObjectKey) -> Result<()> {
    let me = node_of(scope, this)?;
    page(scope)?.remove_node(me);
    Ok(())
}

// ---------------------------------------------------------------------------
// Collections

fn new_collection(scope: &mut Scope<'_>, html: bool, c: Collection) -> Result<ObjectKey> {
    let page = page(scope)?;
    Ok(page.add_object(if html {
        Object::HtmlCollection(c)
    } else {
        Object::NodeList(c)
    }))
}

/// DOM §4.4† "the list of elements with qualified name qualifiedName":
/// "*" is every element descendant; otherwise HTML elements whose qualified
/// name is qualifiedName in ASCII lowercase, and other elements whose
/// qualified name is qualifiedName.
fn matches_tag(arena: &Arena, e: usize, name: &[u32]) -> bool {
    if eq_str(name, "*") {
        return true;
    }
    let Some(local) = local_name_of(arena, e) else {
        return false;
    };
    let qualified = match arena.kind(e) {
        ExecKind::Element {
            prefix: Some(p), ..
        } => {
            let mut q = p.clone();
            q.push(u32::from(':'));
            q.extend_from_slice(local);
            q
        }
        _ => local.to_vec(),
    };
    if is_html_element(arena, e) {
        qualified == ascii_lower(name)
    } else {
        qualified == name
    }
}

/// DOM §4.4† "the list of elements with namespace namespace and local name
/// localName": "If both namespace and localName are "*", match all
/// descendant elements. If namespace is "*", match elements whose local
/// name is localName. If localName is "*", match elements whose namespace is
/// namespace. Otherwise, match elements whose namespace is namespace and
/// local name is localName."
fn matches_tag_ns(arena: &Arena, e: usize, ns: &NsFilter, local: &[u32]) -> bool {
    let ExecKind::Element {
        namespace,
        local_name,
        ..
    } = arena.kind(e)
    else {
        return false;
    };
    let ns_ok = match ns {
        NsFilter::Any => true,
        NsFilter::Null => namespace.is_none(),
        NsFilter::Uri(u) => namespace
            .as_ref()
            .is_some_and(|n| namespace_uri_points(n) == *u),
    };
    ns_ok && (eq_str(local, "*") || local_name.as_slice() == local)
}

/// DOM §4.4† "the list of elements with class names": the elements whose
/// classes include every class of the ordered set (compared exactly: the
/// document is never in quirks mode for this, a deviation for quirks-mode
/// documents, which compare ASCII case-insensitively).
fn has_classes(arena: &Arena, e: usize, classes: &[Vec<u32>]) -> bool {
    if classes.is_empty() {
        return false;
    }
    let mine = attribute_value(arena, e, &str_points("class"))
        .map(|v| split_tokens(&v))
        .unwrap_or_default();
    classes.iter().all(|c| mine.contains(c))
}

/// The nodes a collection holds now.
pub(crate) fn collection_items(arena: &Arena, c: &Collection) -> Vec<usize> {
    match c {
        Collection::ChildNodes(n) => children(arena, *n),
        Collection::Children(n) => element_children(arena, *n),
        Collection::ByTagName(root, name) => descendants(arena, *root)
            .into_iter()
            .filter(|&d| is_element(arena, d) && matches_tag(arena, d, name))
            .collect(),
        Collection::ByTagNameNs(root, filter, local) => descendants(arena, *root)
            .into_iter()
            .filter(|&d| is_element(arena, d) && matches_tag_ns(arena, d, filter, local))
            .collect(),
        Collection::ByClassName(root, classes) => descendants(arena, *root)
            .into_iter()
            .filter(|&d| is_element(arena, d) && has_classes(arena, d, classes))
            .collect(),
        Collection::Static(items) => items.clone(),
    }
}

fn items_of(scope: &mut Scope<'_>, this: ObjectKey) -> Result<Vec<usize>> {
    let page = page(scope)?;
    let items = match page.object(this) {
        Some(Object::NodeList(c) | Object::HtmlCollection(c)) => collection_items(&page.arena, c),
        _ => return Err(type_error(scope, "not a collection")),
    };
    Ok(items)
}

/// The ordered set parser (DOM §2.? "ordered set parser"): split on ASCII
/// whitespace, dropping duplicates.
fn split_tokens(s: &[u32]) -> Vec<Vec<u32>> {
    let mut out: Vec<Vec<u32>> = Vec::new();
    for t in s.split(|&c| is_ascii_whitespace(c)) {
        if !t.is_empty() && !out.iter().any(|o| o == t) {
            out.push(t.to_vec());
        }
    }
    out
}

fn by_tag(scope: &mut Scope<'_>, this: ObjectKey, name: DomString) -> Result<ObjectKey> {
    let root = node_of(scope, this)?;
    new_collection(
        scope,
        true,
        Collection::ByTagName(root, units_to_points(&name)),
    )
}

fn by_tag_ns(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    namespace: Option<DomString>,
    local_name: DomString,
) -> Result<ObjectKey> {
    let root = node_of(scope, this)?;
    let filter = match namespace {
        None => NsFilter::Null,
        Some(n) if n.is_empty() => NsFilter::Null,
        Some(n) if n == [u16::from(b'*')] => NsFilter::Any,
        Some(n) => NsFilter::Uri(units_to_points(&n)),
    };
    new_collection(
        scope,
        true,
        Collection::ByTagNameNs(root, filter, units_to_points(&local_name)),
    )
}

fn by_class(scope: &mut Scope<'_>, this: ObjectKey, names: DomString) -> Result<ObjectKey> {
    let root = node_of(scope, this)?;
    let classes = split_tokens(&units_to_points(&names));
    new_collection(scope, true, Collection::ByClassName(root, classes))
}

fn first_element_child(scope: &mut Scope<'_>, this: ObjectKey) -> Result<Option<ObjectKey>> {
    let n = node_of(scope, this)?;
    Ok(element_children(&page(scope)?.arena, n)
        .first()
        .map(|&c| key(c)))
}

fn last_element_child(scope: &mut Scope<'_>, this: ObjectKey) -> Result<Option<ObjectKey>> {
    let n = node_of(scope, this)?;
    Ok(element_children(&page(scope)?.arena, n)
        .last()
        .map(|&c| key(c)))
}

fn child_element_count(scope: &mut Scope<'_>, this: ObjectKey) -> Result<u32> {
    let n = node_of(scope, this)?;
    Ok(u32::try_from(element_children(&page(scope)?.arena, n).len()).unwrap_or(u32::MAX))
}

fn children_collection(scope: &mut Scope<'_>, this: ObjectKey) -> Result<ObjectKey> {
    let n = node_of(scope, this)?;
    new_collection(scope, true, Collection::Children(n))
}

fn previous_element_sibling(scope: &mut Scope<'_>, this: ObjectKey) -> Result<Option<ObjectKey>> {
    let n = node_of(scope, this)?;
    let arena = &page(scope)?.arena;
    let mut cur = arena.previous_sibling(n);
    while let Some(s) = cur {
        if is_element(arena, s) {
            return Ok(Some(key(s)));
        }
        cur = arena.previous_sibling(s);
    }
    Ok(None)
}

fn next_element_sibling(scope: &mut Scope<'_>, this: ObjectKey) -> Result<Option<ObjectKey>> {
    let n = node_of(scope, this)?;
    let arena = &page(scope)?.arena;
    let mut cur = arena.next_sibling(n);
    while let Some(s) = cur {
        if is_element(arena, s) {
            return Ok(Some(key(s)));
        }
        cur = arena.next_sibling(s);
    }
    Ok(None)
}

/// `querySelector` (DOM §4.2.6†): "Return the first result of running scope-
/// match a selectors string selectors against this, if the result is not an
/// empty list; otherwise null." A parse failure is a `SyntaxError`.
fn query_selector(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    selectors: DomString,
) -> Result<Option<ObjectKey>> {
    let n = node_of(scope, this)?;
    let r = crate::selectors::query_selector(&page(scope)?.arena, n, &units_to_points(&selectors));
    match r {
        Ok(found) => Ok(found.map(key)),
        Err(_) => Err(dom_error(
            scope,
            DomErrorName::SyntaxError,
            "not a valid selector",
        )),
    }
}

/// `querySelectorAll`: "Return the static result of running scope-match a
/// selectors string selectors against this."
fn query_selector_all(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    selectors: DomString,
) -> Result<ObjectKey> {
    let n = node_of(scope, this)?;
    let r =
        crate::selectors::query_selector_all(&page(scope)?.arena, n, &units_to_points(&selectors));
    match r {
        Ok(found) => new_collection(scope, false, Collection::Static(found)),
        Err(_) => Err(dom_error(
            scope,
            DomErrorName::SyntaxError,
            "not a valid selector",
        )),
    }
}

/// `getElementById` (DOM §4.2.4† `NonElementParentNode`): "the first
/// element, in tree order, within this's descendants, whose ID is
/// elementId; otherwise null."
fn get_element_by_id(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    id: DomString,
) -> Result<Option<ObjectKey>> {
    let n = node_of(scope, this)?;
    let id = units_to_points(&id);
    let arena = &page(scope)?.arena;
    if id.is_empty() {
        return Ok(None);
    }
    Ok(descendants(arena, n)
        .into_iter()
        .find(|&d| {
            is_element(arena, d)
                && attribute_value(arena, d, &str_points("id")).as_deref() == Some(id.as_slice())
        })
        .map(key))
}

// ---------------------------------------------------------------------------
// Node

/// Whether `key` names an `Attr` object.
fn is_attr_key(scope: &mut Scope<'_>, key: ObjectKey) -> Result<bool> {
    Ok(matches!(page(scope)?.object(key), Some(Object::Attr(_))))
}

/// The element an `Attr` object is on, if any.
fn attr_owner(scope: &mut Scope<'_>, key: ObjectKey) -> Result<Option<usize>> {
    let p = page(scope)?;
    Ok(match p.object(key) {
        Some(Object::Attr(s)) => s.owner,
        _ => None,
    })
}

/// The document element: the document's first element child.
fn document_element(arena: &Arena) -> Option<usize> {
    arena
        .children(0)
        .iter()
        .copied()
        .find(|&c| is_element(arena, c))
}

/// The single-node part of "A equals B" (DOM §4.4†): the same kind, the
/// same type-specific fields, and for an element the same attributes in any
/// order.
fn nodes_equal_shallow(arena: &Arena, a: usize, b: usize) -> bool {
    use super::attr::namespace_code as code;
    match (arena.kind(a), arena.kind(b)) {
        (ExecKind::Document { .. }, ExecKind::Document { .. })
        | (ExecKind::DocumentFragment { .. }, ExecKind::DocumentFragment { .. }) => true,
        (
            ExecKind::DocumentType {
                name: n1,
                public_id: p1,
                system_id: s1,
            },
            ExecKind::DocumentType {
                name: n2,
                public_id: p2,
                system_id: s2,
            },
        ) => n1 == n2 && p1 == p2 && s1 == s2,
        (
            ExecKind::Element {
                namespace: ns1,
                prefix: pf1,
                local_name: l1,
                attributes: at1,
                ..
            },
            ExecKind::Element {
                namespace: ns2,
                prefix: pf2,
                local_name: l2,
                attributes: at2,
                ..
            },
        ) => {
            code(ns1.as_ref()) == code(ns2.as_ref())
                && pf1 == pf2
                && l1 == l2
                && at1.len() == at2.len()
                && at1.iter().all(|x| {
                    at2.iter().any(|y| {
                        code(x.namespace.as_ref()) == code(y.namespace.as_ref())
                            && x.local_name == y.local_name
                            && x.value == y.value
                    })
                })
        }
        (ExecKind::Text { data: d1 }, ExecKind::Text { data: d2 })
        | (ExecKind::Comment { data: d1 }, ExecKind::Comment { data: d2 }) => d1 == d2,
        (
            ExecKind::ProcessingInstruction {
                target: t1,
                data: d1,
            },
            ExecKind::ProcessingInstruction {
                target: t2,
                data: d2,
            },
        ) => t1 == t2 && d1 == d2,
        _ => false,
    }
}

/// DOM §4.4† "locate a namespace" for element `e` and `prefix`: "1. If
/// element's namespace is non-null and its namespace prefix is prefix, then
/// return namespace. 2. If element has an attribute whose namespace is the
/// XMLNS namespace, namespace prefix is "xmlns", and local name is prefix,
/// or if prefix is null and element has an attribute whose namespace is the
/// XMLNS namespace, namespace prefix is null, and local name is "xmlns",
/// then return its value if it is not the empty string, and null otherwise.
/// 3. If its parent element is null, then return null. 4. Return the result
/// of running locate a namespace on its parent element using prefix."
fn locate_namespace(arena: &Arena, e: usize, prefix: Option<&[u32]>) -> Option<Vec<u32>> {
    let mut cur = Some(e);
    while let Some(el) = cur {
        if let ExecKind::Element {
            namespace: Some(ns),
            prefix: p,
            ..
        } = arena.kind(el)
            && p.as_deref() == prefix
        {
            return Some(namespace_uri_points(ns));
        }
        for a in attributes_of(arena, el) {
            if matches!(a.namespace, Some(Namespace::Xmlns)) {
                let hit = match prefix {
                    Some(pfx) => {
                        a.prefix.as_deref().is_some_and(|x| eq_str(x, "xmlns"))
                            && a.local_name == pfx
                    }
                    None => a.prefix.is_none() && eq_str(&a.local_name, "xmlns"),
                };
                if hit {
                    return (!a.value.is_empty()).then(|| a.value.clone());
                }
            }
        }
        cur = arena.parent(el).filter(|&p| is_element(arena, p));
    }
    None
}

/// DOM §4.4† "locate a namespace prefix" for element `e` and `namespace`:
/// "1. If element's namespace is namespace and its namespace prefix is
/// non-null, then return its namespace prefix. 2. If element has an
/// attribute whose namespace prefix is "xmlns" and value is namespace, then
/// return element's first such attribute's local name. 3. If element's
/// parent element is not null, then return the result of running locate a
/// namespace prefix on that element using namespace. 4. Return null."
fn locate_prefix(arena: &Arena, e: usize, namespace: &[u32]) -> Option<Vec<u32>> {
    let mut cur = Some(e);
    while let Some(el) = cur {
        if let ExecKind::Element {
            namespace: Some(ns),
            prefix: Some(p),
            ..
        } = arena.kind(el)
            && namespace_uri_points(ns) == namespace
        {
            return Some(p.clone());
        }
        if let Some(a) = attributes_of(arena, el).iter().find(|a| {
            a.prefix.as_deref().is_some_and(|x| eq_str(x, "xmlns")) && a.value == namespace
        }) {
            return Some(a.local_name.clone());
        }
        cur = arena.parent(el).filter(|&p| is_element(arena, p));
    }
    None
}

/// DOM §4.4† "locate a namespace" for a node: "Element: (above). Document:
/// If its document element is null, then return null; otherwise, return the
/// result of running locate a namespace on its document element using
/// prefix. DocumentType, DocumentFragment: Return null. Attr: If its element
/// is null, then return null; otherwise, return the result of running locate
/// a namespace on its element using prefix. Any other node: If its parent
/// element is null, then return null. Otherwise, return the result of
/// running locate a namespace on its parent element using prefix."
fn located_namespace(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    prefix: Option<&[u32]>,
) -> Result<Option<Vec<u32>>> {
    if is_attr_key(scope, this)? {
        let owner = attr_owner(scope, this)?;
        let arena = &page(scope)?.arena;
        return Ok(owner.and_then(|e| locate_namespace(arena, e, prefix)));
    }
    let n = node_of(scope, this)?;
    let arena = &page(scope)?.arena;
    let start = match arena.kind(n) {
        ExecKind::Element { .. } => Some(n),
        ExecKind::Document { .. } => document_element(arena),
        ExecKind::DocumentType { .. } | ExecKind::DocumentFragment { .. } => None,
        _ => arena.parent(n).filter(|&p| is_element(arena, p)),
    };
    Ok(start.and_then(|e| locate_namespace(arena, e, prefix)))
}

/// HTML §13.4† "the HTML fragment parsing algorithm" with element `context`:
/// the new fragment, or a `NotSupportedError` at the arena's node limit.
fn parse_in(scope: &mut Scope<'_>, context: usize, html: &[u32]) -> Result<usize> {
    match parse_fragment(&mut page(scope)?.arena, context, html) {
        Some(f) => Ok(f),
        None => Err(dom_error(
            scope,
            DomErrorName::NotSupportedError,
            "the document has too many nodes",
        )),
    }
}

/// The `where` argument of `insertAdjacent*`, ASCII-lowercased: 0 for
/// "beforebegin", 1 "afterbegin", 2 "beforeend", 3 "afterend"; else a
/// `SyntaxError`.
fn adjacent_position(scope: &mut Scope<'_>, w: &[u16]) -> Result<u8> {
    let lower = ascii_lower(&units_to_points(w));
    for (i, name) in ["beforebegin", "afterbegin", "beforeend", "afterend"]
        .iter()
        .enumerate()
    {
        if eq_str(&lower, name) {
            return Ok(u8::try_from(i).unwrap_or(0));
        }
    }
    Err(dom_error(
        scope,
        DomErrorName::SyntaxError,
        "not one of beforebegin, afterbegin, beforeend and afterend",
    ))
}

/// DOM §4.9† "insert adjacent" `node` at `w` of `e`: "beforebegin: If
/// element's parent is null, return null. Return the result of pre-inserting
/// node into element's parent before element. afterbegin: Return the result
/// of pre-inserting node into element before element's first child.
/// beforeend: Return the result of pre-inserting node into element before
/// null. afterend: If element's parent is null, return null. Return the
/// result of pre-inserting node into element's parent before element's next
/// sibling." Whether the node was inserted.
fn insert_adjacent(scope: &mut Scope<'_>, e: usize, w: u8, node: usize) -> Result<bool> {
    let arena = &page(scope)?.arena;
    let (parent, before) = match w {
        0 => (arena.parent(e), Some(e)),
        1 => (Some(e), arena.children(e).first().copied()),
        2 => (Some(e), None),
        _ => (arena.parent(e), arena.next_sibling(e)),
    };
    let Some(parent) = parent else {
        return Ok(false);
    };
    pre_insert(scope, node, parent, before)?;
    Ok(true)
}

/// A new, unattached HTML `body` element: the context DOM Parsing's
/// "fragment parsing algorithm steps" uses when the context element is
/// absent or the `html` element.
pub(crate) fn new_body_element(scope: &mut Scope<'_>) -> Result<usize> {
    create(
        scope,
        ExecKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: str_points("body"),
            attributes: Vec::new(),
            template_contents: None,
            form_owner: None,
        },
    )
}

/// DOM §4.11† "split" a Text node `node` with `offset`: "1. Let length be
/// node's length. 2. If offset is greater than length, then throw an
/// IndexSizeError DOMException. 3. Let count be length minus offset. 4. Let
/// new data be the result of substringing data with node node, offset
/// offset, and count count. 5. Let new node be a new Text node, with the
/// same node document as node. Set new node's data to new data. 6. Let
/// parent be node's parent. 7. If parent is not null: 1. Insert new node
/// into parent before node's next sibling. 2. to 5. (the live ranges) 8.
/// Replace data with node node, offset offset, count count, and data the
/// empty string. 9. Return new node."
pub(crate) fn split_text(scope: &mut Scope<'_>, node: usize, offset: usize) -> Result<usize> {
    let units = match data_of(&page(scope)?.arena, node) {
        Some(d) => points_to_units(d),
        None => return Err(type_error(scope, "not character data")),
    };
    if offset > units.len() {
        return Err(dom_error(
            scope,
            DomErrorName::IndexSizeError,
            "offset is past the end of the data",
        ));
    }
    let count = units.len().saturating_sub(offset);
    let new = create(
        scope,
        ExecKind::Text {
            data: units_to_points(units.get(offset..).unwrap_or(&[])),
        },
    )?;
    let p = page(scope)?;
    if let Some(parent) = p.arena.parent(node) {
        let next = p.arena.next_sibling(node);
        if let Some(e) = p.insert_node(new, parent, next) {
            return Err(dom_error_of(scope, e));
        }
        let p = page(scope)?;
        let index = p
            .arena
            .children(parent)
            .iter()
            .position(|&c| c == node)
            .unwrap_or(0);
        p.ranges_split_text(node, new, offset, Some(parent), index);
    }
    page(scope)?.replace_data_units(node, offset, count, &[]);
    Ok(new)
}

impl NodeImpl for Page {
    /// DOM §4.4† `nodeType`.
    fn node_type<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u16> {
        if is_attr_key(scope, this)? {
            return Ok(2);
        }
        let n = node_of(scope, this)?;
        Ok(match page(scope)?.arena.kind(n) {
            ExecKind::Element { .. } => 1,
            ExecKind::Text { .. } => 3,
            ExecKind::ProcessingInstruction { .. } => 7,
            ExecKind::Comment { .. } => 8,
            ExecKind::Document { .. } => 9,
            ExecKind::DocumentType { .. } => 10,
            ExecKind::DocumentFragment { .. } => 11,
        })
    }

    /// DOM §4.4† `nodeName`: an element's HTML-uppercased qualified name, a
    /// doctype's name, a processing instruction's target, else "#text",
    /// "#comment", "#document" or "#document-fragment".
    fn node_name<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        if is_attr_key(scope, this)? {
            return Ok(page(scope)?
                .attr_qualified_name(this)
                .map(|q| points_to_units(&q))
                .unwrap_or_default());
        }
        let n = node_of(scope, this)?;
        let arena = &page(scope)?.arena;
        Ok(match arena.kind(n) {
            ExecKind::Element { .. } => points_to_units(&html_uppercased_qualified_name(arena, n)),
            ExecKind::Text { .. } => str_units("#text"),
            ExecKind::Comment { .. } => str_units("#comment"),
            ExecKind::Document { .. } => str_units("#document"),
            ExecKind::DocumentFragment { .. } => str_units("#document-fragment"),
            ExecKind::DocumentType { name, .. } => points_to_units(name),
            ExecKind::ProcessingInstruction { target, .. } => points_to_units(target),
        })
    }

    /// DOM §4.4† `isConnected`: "its shadow-including root is a document".
    fn is_connected<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        if is_attr_key(scope, this)? {
            return Ok(false);
        }
        let n = node_of(scope, this)?;
        Ok(page(scope)?.arena.is_inclusive_ancestor(0, n))
    }

    /// DOM §4.4† `ownerDocument`: "null, if this is a document; otherwise
    /// this's node document" (the one document).
    fn owner_document<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        if is_attr_key(scope, this)? {
            return Ok(Some(key(0)));
        }
        let n = node_of(scope, this)?;
        Ok((n != 0).then(|| key(0)))
    }

    fn parent_node<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        if is_attr_key(scope, this)? {
            return Ok(None);
        }
        let n = node_of(scope, this)?;
        Ok(page(scope)?.arena.parent(n).map(key))
    }

    /// DOM §4.4† `parentElement`: "this's parent element".
    fn parent_element<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        let n = node_of(scope, this)?;
        let arena = &page(scope)?.arena;
        Ok(arena.parent(n).filter(|&p| is_element(arena, p)).map(key))
    }

    /// DOM §4.4† `childNodes`: "a NodeList rooted at this matching only
    /// children" ([SameObject] is the bindings').
    fn child_nodes<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        let n = node_of(scope, this)?;
        new_collection(scope, false, Collection::ChildNodes(n))
    }

    fn first_child<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        let n = node_of(scope, this)?;
        Ok(page(scope)?.arena.children(n).first().map(|&c| key(c)))
    }

    fn last_child<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        let n = node_of(scope, this)?;
        Ok(page(scope)?.arena.last_child(n).map(key))
    }

    fn previous_sibling<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        let n = node_of(scope, this)?;
        Ok(page(scope)?.arena.previous_sibling(n).map(key))
    }

    fn next_sibling<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        let n = node_of(scope, this)?;
        Ok(page(scope)?.arena.next_sibling(n).map(key))
    }

    /// DOM §4.4† `nodeValue` getter: an Attr's value (no Attr nodes here),
    /// a CharacterData node's data, otherwise null.
    fn node_value<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<DomString>> {
        if is_attr_key(scope, this)? {
            return Ok(page(scope)?.attr_value(this).map(|v| points_to_units(&v)));
        }
        let n = node_of(scope, this)?;
        Ok(data_of(&page(scope)?.arena, n).map(points_to_units))
    }

    /// DOM §4.4† `nodeValue` setter: "If the given value is null, act as if
    /// it was the empty string instead ... CharacterData: Replace data with
    /// node this, offset 0, count this's length, and data the given value.
    /// Otherwise: Do nothing."
    fn set_node_value<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        value: Option<DomString>,
    ) -> Result<()> {
        if is_attr_key(scope, this)? {
            return <Page as AttrImpl>::set_value(scope, this, value.unwrap_or_default());
        }
        let n = node_of(scope, this)?;
        let page = page(scope)?;
        if data_of(&page.arena, n).is_some() {
            page.set_node_data(n, &units_to_points(&value.unwrap_or_default()));
        }
        Ok(())
    }

    /// DOM §4.4† `textContent` getter ("get text content"): a
    /// DocumentFragment or Element's descendant text content, a
    /// CharacterData node's data, otherwise null.
    fn text_content<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<DomString>> {
        if is_attr_key(scope, this)? {
            return Ok(page(scope)?.attr_value(this).map(|v| points_to_units(&v)));
        }
        let n = node_of(scope, this)?;
        let arena = &page(scope)?.arena;
        Ok(match arena.kind(n) {
            ExecKind::Element { .. } | ExecKind::DocumentFragment { .. } => {
                Some(points_to_units(&descendant_text(arena, n)))
            }
            ExecKind::Text { data }
            | ExecKind::Comment { data }
            | ExecKind::ProcessingInstruction { data, .. } => Some(points_to_units(data)),
            _ => None,
        })
    }

    /// DOM §4.4† `textContent` setter ("set text content"): null is the
    /// empty string; a DocumentFragment or Element gets "string replace
    /// all" ("Let node be null. If string is not the empty string, then set
    /// node to a new Text node whose data is string. Replace all with node
    /// within parent."); a CharacterData node "replace data" of all its
    /// data; otherwise nothing.
    fn set_text_content<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        value: Option<DomString>,
    ) -> Result<()> {
        if is_attr_key(scope, this)? {
            return <Page as AttrImpl>::set_value(scope, this, value.unwrap_or_default());
        }
        let n = node_of(scope, this)?;
        let value = units_to_points(&value.unwrap_or_default());
        let kind_is_parent = matches!(
            page(scope)?.arena.kind(n),
            ExecKind::Element { .. } | ExecKind::DocumentFragment { .. }
        );
        if kind_is_parent {
            let node = if value.is_empty() {
                None
            } else {
                Some(create(scope, ExecKind::Text { data: value })?)
            };
            page(scope)?.replace_all_with(node, n);
        } else if data_of(&page(scope)?.arena, n).is_some() {
            page(scope)?.set_node_data(n, &value);
        }
        Ok(())
    }

    /// DOM §4.4† `getRootNode`: "this's shadow-including root if options
    /// ["composed"] is true; otherwise this's root" (no shadow trees: the
    /// root).
    fn get_root_node<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        _options: GetRootNodeOptions,
    ) -> Result<ObjectKey> {
        let mut n = node_of(scope, this)?;
        let arena = &page(scope)?.arena;
        while let Some(p) = arena.parent(n) {
            n = p;
        }
        Ok(key(n))
    }

    fn has_child_nodes<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        if is_attr_key(scope, this)? {
            return Ok(false);
        }
        let n = node_of(scope, this)?;
        Ok(!page(scope)?.arena.children(n).is_empty())
    }

    /// DOM §4.4† `cloneNode(subtree)`: "1. If this is a shadow root, then
    /// throw. 2. Return the result of cloning a node given this with
    /// subtree set to subtree." Cloning a document is not implemented
    /// (`clazel-dom`'s clone does not copy documents).
    fn clone_node<'s>(scope: &mut Scope<'s>, this: ObjectKey, subtree: bool) -> Result<ObjectKey> {
        let n = node_of(scope, this)?;
        if n == 0 {
            return Err(dom_error(
                scope,
                DomErrorName::NotSupportedError,
                "cloning a document is not implemented",
            ));
        }
        let arena = &mut page(scope)?.arena;
        let r = if subtree {
            arena.clone_deep(n)
        } else {
            arena.clone_node(n)
        };
        match r {
            Some(c) => Ok(key(c)),
            None => Err(dom_error(
                scope,
                DomErrorName::NotSupportedError,
                "the document has too many nodes",
            )),
        }
    }

    fn is_same_node<'s>(
        _scope: &mut Scope<'s>,
        this: ObjectKey,
        other: Option<ObjectKey>,
    ) -> Result<bool> {
        Ok(other == Some(this))
    }

    /// DOM §4.4† `contains(other)`: "true if other is an inclusive
    /// descendant of this; otherwise false (including when other is null)".
    fn contains<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        other: Option<ObjectKey>,
    ) -> Result<bool> {
        let n = node_of(scope, this)?;
        let Some(o) = other else {
            return Ok(false);
        };
        let o = node_of(scope, o)?;
        Ok(page(scope)?.arena.is_inclusive_ancestor(n, o))
    }

    /// DOM §4.4† `insertBefore(node, child)`: "return the result of
    /// pre-inserting node into this before child."
    fn insert_before<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        node: ObjectKey,
        child: Option<ObjectKey>,
    ) -> Result<ObjectKey> {
        let p = node_of(scope, this)?;
        let n = node_of(scope, node)?;
        let c = match child {
            Some(c) => Some(node_of(scope, c)?),
            None => None,
        };
        pre_insert(scope, n, p, c)?;
        Ok(node)
    }

    /// DOM §4.4† `appendChild(node)`: "return the result of appending node
    /// to this" (pre-insert before null).
    fn append_child<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        node: ObjectKey,
    ) -> Result<ObjectKey> {
        let p = node_of(scope, this)?;
        let n = node_of(scope, node)?;
        pre_insert(scope, n, p, None)?;
        Ok(node)
    }

    /// DOM §4.4† `replaceChild(node, child)`: "return the result of replacing
    /// child with node within this."
    fn replace_child<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        node: ObjectKey,
        child: ObjectKey,
    ) -> Result<ObjectKey> {
        let p = node_of(scope, this)?;
        let n = node_of(scope, node)?;
        let c = node_of(scope, child)?;
        match page(scope)?.replace_node(c, n, p) {
            Some(e) => Err(dom_error_of(scope, e)),
            None => Ok(child),
        }
    }

    /// DOM §4.4† `baseURI`: "this's node document's document base URL,
    /// serialized".
    fn base_uri<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        let arena = &page(scope)?.arena;
        Ok(match arena.kind(0) {
            ExecKind::Document { base_url, .. } => super::points_to_string(base_url),
            _ => String::new(),
        })
    }

    /// DOM §4.4† `normalize()`: "1. For each descendant exclusive Text node
    /// node of this: 1. Let length be node's length. 2. If length is zero,
    /// then remove node and continue. 3. Let data be the concatenation of
    /// the data of node's contiguous exclusive Text nodes (excluding
    /// itself), in tree order. 4. Replace data with node node, offset
    /// length, count 0, and data data. 5. Let currentNode be node's next
    /// sibling. 6. While currentNode is an exclusive Text node: 1. For each
    /// live range whose start node is currentNode, add length to its start
    /// offset and set its start node to node. 2. ... end node ... 3. For
    /// each live range whose start node is currentNode's parent and start
    /// offset is currentNode's index, set its start node to node and its
    /// start offset to length. 4. ... end ... 5. Add currentNode's length to
    /// length. 6. Set currentNode to its next sibling. 7. Remove node's
    /// contiguous exclusive Text nodes (excluding itself), in tree order."
    fn normalize<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        let n = node_of(scope, this)?;
        let texts: Vec<usize> = {
            let arena = &page(scope)?.arena;
            descendants(arena, n)
                .into_iter()
                .filter(|&d| matches!(arena.kind(d), ExecKind::Text { .. }))
                .collect()
        };
        for t in texts {
            let p = page(scope)?;
            if p.arena.parent(t).is_none() {
                continue;
            }
            let length = data_of(&p.arena, t).map_or(0, |d| points_to_units(d).len());
            if length == 0 {
                p.remove_node(t);
                continue;
            }
            let mut run = Vec::new();
            let mut next = p.arena.next_sibling(t);
            while let Some(x) = next {
                if !matches!(p.arena.kind(x), ExecKind::Text { .. }) {
                    break;
                }
                run.push(x);
                next = p.arena.next_sibling(x);
            }
            let mut data: Vec<u16> = Vec::new();
            for &x in &run {
                data.extend(
                    data_of(&p.arena, x)
                        .map(points_to_units)
                        .unwrap_or_default(),
                );
            }
            p.replace_data_units(t, length, 0, &data);
            let parent = p.arena.parent(t);
            let mut offset = length;
            for &x in &run {
                let index = parent.map_or(0, |pp| {
                    p.arena
                        .children(pp)
                        .iter()
                        .position(|&c| c == x)
                        .unwrap_or(0)
                });
                let off = offset;
                p.update_range_points(|_, b| {
                    if b.0 == x {
                        *b = (t, b.1.saturating_add(off));
                    } else if Some(b.0) == parent && b.1 == index {
                        *b = (t, off);
                    }
                });
                offset = offset
                    .saturating_add(data_of(&p.arena, x).map_or(0, |d| points_to_units(d).len()));
            }
            for x in run {
                p.remove_node(x);
            }
        }
        Ok(())
    }

    /// DOM §4.4† `isEqualNode(otherNode)`: "Return true if otherNode is
    /// non-null and this equals otherNode; otherwise false." "A node A
    /// equals a node B if all of the following conditions are true: A and B
    /// implement the same interfaces. The following are equal, switching on
    /// the interface A implements: DocumentType: its name, public ID,
    /// system ID. Element: its namespace, namespace prefix, local name, and
    /// its attribute list's size. Attr: its namespace, local name, and
    /// value. ProcessingInstruction: its target and data. Text or Comment:
    /// its data. If A is an element, each attribute in its attribute list
    /// has an attribute that equals an attribute in B's attribute list. A
    /// and B have the same number of children. Each child of A equals the
    /// child of B at the identical index."
    fn is_equal_node<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        other_node: Option<ObjectKey>,
    ) -> Result<bool> {
        let Some(other) = other_node else {
            return Ok(false);
        };
        if is_attr_key(scope, this)? || is_attr_key(scope, other)? {
            let p = page(scope)?;
            let both = matches!(
                (p.object(this), p.object(other)),
                (Some(Object::Attr(a)), Some(Object::Attr(b)))
                    if a.attr.local_name == b.attr.local_name
                        && super::attr::namespace_code(a.attr.namespace.as_ref())
                            == super::attr::namespace_code(b.attr.namespace.as_ref())
            );
            return Ok(both && p.attr_value(this) == p.attr_value(other));
        }
        let a = node_of(scope, this)?;
        let b = node_of(scope, other)?;
        let arena = &page(scope)?.arena;
        let mut stack = vec![(a, b)];
        while let Some((a, b)) = stack.pop() {
            if !nodes_equal_shallow(arena, a, b) {
                return Ok(false);
            }
            let (ca, cb) = (arena.children(a), arena.children(b));
            if ca.len() != cb.len() {
                return Ok(false);
            }
            stack.extend(ca.iter().copied().zip(cb.iter().copied()));
        }
        Ok(true)
    }

    /// DOM §4.4† `compareDocumentPosition(other)`: "1. If this is other,
    /// then return zero. 2. Let node1 be other and node2 be this. ... 5. If
    /// node1 or node2 is null, or node1's root is not node2's root, then
    /// return the result of adding DOCUMENT_POSITION_DISCONNECTED,
    /// DOCUMENT_POSITION_IMPLEMENTATION_SPECIFIC, and either
    /// DOCUMENT_POSITION_PRECEDING or DOCUMENT_POSITION_FOLLOWING, with the
    /// constraint that this is to be consistent, together. 6. If node1 is an
    /// ancestor of node2 and attr1 is null, or node1 is node2 and attr2 is
    /// non-null, then return the result of adding
    /// DOCUMENT_POSITION_CONTAINS to DOCUMENT_POSITION_PRECEDING. 7. If node1
    /// is a descendant of node2 and attr2 is null, or node1 is node2 and
    /// attr1 is non-null, then return the result of adding
    /// DOCUMENT_POSITION_CONTAINED_BY to DOCUMENT_POSITION_FOLLOWING. 8. If
    /// node1 is preceding node2, then return DOCUMENT_POSITION_PRECEDING. 9.
    /// Return DOCUMENT_POSITION_FOLLOWING." (An Attr is compared as a node
    /// of no tree: disconnected.)
    fn compare_document_position<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        other: ObjectKey,
    ) -> Result<u16> {
        if this == other {
            return Ok(0);
        }
        let disconnected = |a: ObjectKey, b: ObjectKey| 1 | 32 | if a.0 < b.0 { 4 } else { 2 };
        if is_attr_key(scope, this)? || is_attr_key(scope, other)? {
            return Ok(disconnected(this, other));
        }
        let me = node_of(scope, this)?;
        let o = node_of(scope, other)?;
        let arena = &page(scope)?.arena;
        let root = |mut n: usize| {
            while let Some(p) = arena.parent(n) {
                n = p;
            }
            n
        };
        if root(me) != root(o) {
            return Ok(disconnected(this, other));
        }
        if arena.is_inclusive_ancestor(o, me) {
            return Ok(8 | 2);
        }
        if arena.is_inclusive_ancestor(me, o) {
            return Ok(16 | 4);
        }
        Ok(
            if super::range::tree_cmp(arena, o, me) == core::cmp::Ordering::Less {
                2
            } else {
                4
            },
        )
    }

    /// DOM §4.4† `lookupPrefix(namespace)`: "1. If namespace is null or the
    /// empty string, then return null. 2. Switch on the interface this
    /// implements: Element: Return the result of locating a namespace
    /// prefix for it using namespace. Document: Return the result of
    /// locating a namespace prefix for its document element, if its
    /// document element is non-null; otherwise null. DocumentType,
    /// DocumentFragment: null. Attr: its element, if non-null. Any other
    /// node: Return the result of locating a namespace prefix for its
    /// parent element, or if that is null, null."
    fn lookup_prefix<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
    ) -> Result<Option<DomString>> {
        let Some(ns) = namespace.filter(|n| !n.is_empty()) else {
            return Ok(None);
        };
        let ns = units_to_points(&ns);
        if is_attr_key(scope, this)? {
            let owner = attr_owner(scope, this)?;
            let arena = &page(scope)?.arena;
            return Ok(owner
                .and_then(|e| locate_prefix(arena, e, &ns))
                .map(|p| points_to_units(&p)));
        }
        let n = node_of(scope, this)?;
        let arena = &page(scope)?.arena;
        let start = match arena.kind(n) {
            ExecKind::Element { .. } => Some(n),
            ExecKind::Document { .. } => document_element(arena),
            ExecKind::DocumentType { .. } | ExecKind::DocumentFragment { .. } => None,
            _ => arena.parent(n).filter(|&p| is_element(arena, p)),
        };
        Ok(start
            .and_then(|e| locate_prefix(arena, e, &ns))
            .map(|p| points_to_units(&p)))
    }

    /// DOM §4.4† `lookupNamespaceURI(prefix)`: "1. If prefix is the empty
    /// string, then set it to null. 2. Return the result of running locate a
    /// namespace for this using prefix."
    fn lookup_namespace_uri<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        prefix: Option<DomString>,
    ) -> Result<Option<DomString>> {
        let prefix = prefix
            .filter(|p| !p.is_empty())
            .map(|p| units_to_points(&p));
        Ok(located_namespace(scope, this, prefix.as_deref())?.map(|n| points_to_units(&n)))
    }

    /// DOM §4.4† `isDefaultNamespace(namespace)`: "1. If namespace is the
    /// empty string, then set it to null. 2. Let defaultNamespace be the
    /// result of running locate a namespace for this using null. 3. Return
    /// true if defaultNamespace is the same as namespace; otherwise false."
    fn is_default_namespace<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
    ) -> Result<bool> {
        let namespace = namespace.filter(|n| !n.is_empty());
        let default = located_namespace(scope, this, None)?;
        Ok(default == namespace.map(|n| units_to_points(&n)))
    }

    /// DOM §4.2.3† "pre-remove": "1. If child's parent is not parent, then
    /// throw a NotFoundError DOMException. 2. Remove child. 3. Return child."
    fn remove_child<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        child: ObjectKey,
    ) -> Result<ObjectKey> {
        let p = node_of(scope, this)?;
        let c = node_of(scope, child)?;
        if page(scope)?.arena.parent(c) != Some(p) {
            return Err(dom_error_of(scope, DomError::NotFound));
        }
        page(scope)?.remove_node(c);
        Ok(child)
    }
}

/// DOM §4.9† "HTML-uppercased qualified name": the qualified name, in ASCII
/// uppercase for an HTML element of an HTML document.
fn html_uppercased_qualified_name(arena: &Arena, e: usize) -> Vec<u32> {
    let (prefix, local) = match arena.kind(e) {
        ExecKind::Element {
            prefix, local_name, ..
        } => (prefix.clone(), local_name.clone()),
        _ => (None, Vec::new()),
    };
    let mut q = match prefix {
        Some(mut p) => {
            p.push(u32::from(':'));
            p.extend(local);
            p
        }
        None => local,
    };
    if is_html_element(arena, e) {
        q = ascii_upper(&q);
    }
    q
}

// ---------------------------------------------------------------------------
// Document

impl DocumentImpl for Page {
    /// DOM §4.5† `URL` and `documentURI`: "this's URL, serialized".
    fn url<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(page(scope)?.url())
    }

    fn document_uri<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(page(scope)?.url())
    }

    /// DOM §4.5† `compatMode`: "BackCompat" in quirks mode, else
    /// "CSS1Compat".
    fn compat_mode<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        let quirks = matches!(
            page(scope)?.arena.kind(0),
            ExecKind::Document {
                mode: DocumentMode::Quirks,
                ..
            }
        );
        Ok(str_units(if quirks { "BackCompat" } else { "CSS1Compat" }))
    }

    /// DOM §4.5† `characterSet`: the document's encoding's name. The arena
    /// does not keep the encoding the parser used, so this is "UTF-8" (a
    /// deviation for documents in other encodings).
    fn character_set<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units("UTF-8"))
    }

    fn charset<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units("UTF-8"))
    }

    fn input_encoding<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units("UTF-8"))
    }

    /// DOM §4.5† `contentType`: the page's documents are HTML documents.
    fn content_type<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units("text/html"))
    }

    /// DOM §4.5† `doctype`: "the child of this that is a doctype; otherwise
    /// null".
    fn doctype<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        let n = node_of(scope, this)?;
        let arena = &page(scope)?.arena;
        Ok(arena
            .children(n)
            .iter()
            .copied()
            .find(|&c| matches!(arena.kind(c), ExecKind::DocumentType { .. }))
            .map(key))
    }

    /// DOM §4.5† `documentElement`: "this's document element".
    fn document_element<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        first_element_child(scope, this)
    }

    /// HTML §7.2.? `Document.location`: "this's relevant global object's
    /// Location object, if this is fully active, and null otherwise".
    fn location<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(Some(super::window::location_key(scope)?))
    }

    /// HTML §3.1.? `document.title` getter: the first `title` element's
    /// child text content, with ASCII whitespace stripped and collapsed.
    fn title<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let n = node_of(scope, this)?;
        let arena = &page(scope)?.arena;
        let title = descendants(arena, n).into_iter().find(|&d| {
            is_element(arena, d) && local_name_of(arena, d).is_some_and(|l| eq_str(l, "title"))
        });
        let Some(t) = title else {
            return Ok(Vec::new());
        };
        let mut text = Vec::new();
        for &c in arena.children(t) {
            if let ExecKind::Text { data } = arena.kind(c) {
                text.extend_from_slice(data);
            }
        }
        let words: Vec<&[u32]> = text
            .split(|&c| is_ascii_whitespace(c))
            .filter(|w| !w.is_empty())
            .collect();
        Ok(points_to_units(&words.join(&u32::from(' '))))
    }

    /// HTML §3.1.? "the body element": the first `body` or `frameset` child
    /// of the `html` document element.
    fn body<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(html_child(&page(scope)?.arena, &["body", "frameset"]).map(key))
    }

    /// HTML §3.1.? "the head element": the first `head` child of the `html`
    /// document element.
    fn head<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(html_child(&page(scope)?.arena, &["head"]).map(key))
    }

    /// HTML §7.2.? `defaultView`: the document's browsing context's
    /// WindowProxy.
    fn default_view<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(Some(WINDOW))
    }

    fn children<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        children_collection(scope, this)
    }

    fn first_element_child<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        first_element_child(scope, this)
    }

    fn last_element_child<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        last_element_child(scope, this)
    }

    fn child_element_count<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        child_element_count(scope, this)
    }

    fn get_elements_by_tag_name<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
    ) -> Result<ObjectKey> {
        by_tag(scope, this, qualified_name)
    }

    /// DOM §4.4† `getElementsByTagNameNS(namespace, localName)`: "the list
    /// of elements with namespace namespace and local name localName for
    /// this".
    fn get_elements_by_tag_name_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
        local_name: DomString,
    ) -> Result<ObjectKey> {
        by_tag_ns(scope, this, namespace, local_name)
    }

    fn get_elements_by_class_name<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        class_names: DomString,
    ) -> Result<ObjectKey> {
        by_class(scope, this, class_names)
    }

    /// DOM §4.5† `createElement(localName, options)`: "1. If localName is
    /// not a valid element local name, then throw an InvalidCharacterError.
    /// 2. If this is an HTML document, then set localName to localName in
    /// ASCII lowercase. ... 5. Let namespace be the HTML namespace, if this
    /// is an HTML document or this's content type is "application/xhtml+xml";
    /// otherwise null. 6. Return the result of creating an element." The
    /// options' `is` is ignored (no custom elements). A `template` gets its
    /// template contents (HTML §4.12.3†).
    fn create_element<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        local_name: DomString,
        _options: DOMStringOrElementCreationOptions,
    ) -> Result<ObjectKey> {
        let name = units_to_points(&local_name);
        if !valid_element_local_name(&name) {
            return Err(dom_error(
                scope,
                DomErrorName::InvalidCharacterError,
                "not a valid element name",
            ));
        }
        let local_name = ascii_lower(&name);
        let template = eq_str(&local_name, "template");
        let e = create(
            scope,
            ExecKind::Element {
                namespace: Some(Namespace::Html),
                prefix: None,
                local_name,
                attributes: Vec::new(),
                template_contents: None,
                form_owner: None,
            },
        )?;
        if template && page(scope)?.arena.create_template_contents(e).is_none() {
            return Err(dom_error(
                scope,
                DomErrorName::NotSupportedError,
                "the document has too many nodes",
            ));
        }
        Ok(key(e))
    }

    /// DOM §4.5† `createElementNS(namespace, qualifiedName, options)`, for
    /// the HTML, SVG and MathML namespaces and no prefix ("validate and
    /// extract"; other namespaces are not representable in the arena and
    /// throw `NotSupportedError`).
    fn create_element_ns<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        namespace: Option<DomString>,
        qualified_name: DomString,
        _options: DOMStringOrElementCreationOptions,
    ) -> Result<ObjectKey> {
        let ns = namespace.map(|n| String::from_utf16_lossy(&n));
        let ns = match ns.as_deref() {
            Some(HTML_NS) => Namespace::Html,
            Some(SVG_NS) => Namespace::Svg,
            Some(MATHML_NS) => Namespace::MathMl,
            _ => {
                return Err(dom_error(
                    scope,
                    DomErrorName::NotSupportedError,
                    "only the HTML, SVG and MathML namespaces are implemented",
                ));
            }
        };
        let name = units_to_points(&qualified_name);
        if !valid_element_local_name(&name) || name.contains(&u32::from(':')) {
            return Err(dom_error(
                scope,
                DomErrorName::InvalidCharacterError,
                "not a valid element name",
            ));
        }
        let e = create(
            scope,
            ExecKind::Element {
                namespace: Some(ns),
                prefix: None,
                local_name: name,
                attributes: Vec::new(),
                template_contents: None,
                form_owner: None,
            },
        )?;
        Ok(key(e))
    }

    /// DOM §4.5† `importNode(node, options)`: "1. If node is a document or
    /// shadow root, then throw a NotSupportedError. 2. Let subtree be false.
    /// 3. Let registry be ... 4. If options is a boolean, then set subtree
    /// to options. 5. Otherwise, set subtree to the negation of options's
    /// selfOnly. 6. Return the result of cloning a node given node with
    /// document set to this and subtree set to subtree."
    fn import_node<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        node: ObjectKey,
        options: BooleanOrImportNodeOptions,
    ) -> Result<ObjectKey> {
        let n = node_of(scope, node)?;
        if n == 0 {
            return Err(dom_error(
                scope,
                DomErrorName::NotSupportedError,
                "a document cannot be imported",
            ));
        }
        let subtree = match options {
            BooleanOrImportNodeOptions::Boolean(b) => b,
            BooleanOrImportNodeOptions::ImportNodeOptions(o) => !o.self_only,
        };
        let arena = &mut page(scope)?.arena;
        let r = if subtree {
            arena.clone_deep(n)
        } else {
            arena.clone_node(n)
        };
        match r {
            Some(c) => Ok(key(c)),
            None => Err(dom_error(
                scope,
                DomErrorName::NotSupportedError,
                "the document has too many nodes",
            )),
        }
    }

    /// DOM §4.5† `adoptNode(node)`: "1. If node is a document, then throw a
    /// NotSupportedError. 2. If node is a shadow root, then throw a
    /// HierarchyRequestError. 3. If node is a DocumentFragment node whose
    /// host is non-null, then return. 4. Adopt node into this. 5. Return
    /// node." (There is one document, so adopting only removes the node
    /// from its parent.)
    fn adopt_node<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        node: ObjectKey,
    ) -> Result<ObjectKey> {
        let n = node_of(scope, node)?;
        let arena = &page(scope)?.arena;
        match arena.kind(n) {
            ExecKind::Document { .. } => {
                return Err(dom_error(
                    scope,
                    DomErrorName::NotSupportedError,
                    "a document cannot be adopted",
                ));
            }
            ExecKind::DocumentFragment { host: Some(_) } => return Ok(node),
            _ => {}
        }
        page(scope)?.remove_node(n);
        Ok(node)
    }

    /// DOM §4.5† `createProcessingInstruction(target, data)`.
    fn create_processing_instruction<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        target: DomString,
        data: DomString,
    ) -> Result<ObjectKey> {
        new_processing_instruction(scope, &target, &data)
    }

    /// DOM §4.5† `createAttribute(localName)`: "1. If localName does not
    /// match the Name production in XML, then throw an
    /// InvalidCharacterError. 2. If this is an HTML document, then set
    /// localName to localName in ASCII lowercase. 3. Return a new attribute
    /// whose local name is localName and node document is this."
    fn create_attribute<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        local_name: DomString,
    ) -> Result<ObjectKey> {
        let name = units_to_points(&local_name);
        if !valid_attribute_local_name(&name) {
            return Err(dom_error(
                scope,
                DomErrorName::InvalidCharacterError,
                "not a valid attribute name",
            ));
        }
        Ok(page(scope)?.new_attr(ExecAttr {
            namespace: None,
            prefix: None,
            local_name: ascii_lower(&name),
            value: Vec::new(),
        }))
    }

    /// DOM §4.5† `createAttributeNS(namespace, qualifiedName)`: "1. Let
    /// namespace, prefix, and localName be the result of passing namespace
    /// and qualifiedName to validate and extract. 2. Return a new attribute
    /// whose namespace is namespace, namespace prefix is prefix, local name
    /// is localName, and node document is this."
    fn create_attribute_ns<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        namespace: Option<DomString>,
        qualified_name: DomString,
    ) -> Result<ObjectKey> {
        let (ns, prefix, local) =
            super::attr::validate_and_extract(scope, &namespace, &qualified_name)?;
        Ok(page(scope)?.new_attr(ExecAttr {
            namespace: ns,
            prefix,
            local_name: local,
            value: Vec::new(),
        }))
    }

    /// DOM §5.5† `createRange()`: "Return a new live range with (this, 0)
    /// as its start and end."
    fn create_range<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        Ok(page(scope)?.new_range())
    }

    /// DOM §4.5† `createDocumentFragment()`: "a new DocumentFragment node".
    fn create_document_fragment<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        Ok(key(create(
            scope,
            ExecKind::DocumentFragment { host: None },
        )?))
    }

    /// DOM §4.5† `createTextNode(data)`.
    fn create_text_node<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        data: DomString,
    ) -> Result<ObjectKey> {
        Ok(key(create(
            scope,
            ExecKind::Text {
                data: units_to_points(&data),
            },
        )?))
    }

    /// DOM §4.5† `createComment(data)`.
    fn create_comment<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        data: DomString,
    ) -> Result<ObjectKey> {
        Ok(key(create(
            scope,
            ExecKind::Comment {
                data: units_to_points(&data),
            },
        )?))
    }

    fn get_element_by_id<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        element_id: DomString,
    ) -> Result<Option<ObjectKey>> {
        get_element_by_id(scope, this, element_id)
    }

    fn prepend<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        prepend(scope, this, nodes)
    }

    fn append<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        append(scope, this, nodes)
    }

    fn replace_children<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        replace_children(scope, this, nodes)
    }

    fn query_selector<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        selectors: DomString,
    ) -> Result<Option<ObjectKey>> {
        query_selector(scope, this, selectors)
    }

    fn query_selector_all<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        selectors: DomString,
    ) -> Result<ObjectKey> {
        query_selector_all(scope, this, selectors)
    }
}

/// The first child of the `html` document element named one of `names`.
fn html_child(arena: &Arena, names: &[&str]) -> Option<usize> {
    let html = element_children(arena, 0).into_iter().next()?;
    if !is_html_element(arena, html)
        || !local_name_of(arena, html).is_some_and(|l| eq_str(l, "html"))
    {
        return None;
    }
    arena.children(html).iter().copied().find(|&c| {
        is_html_element(arena, c)
            && local_name_of(arena, c).is_some_and(|l| names.iter().any(|n| eq_str(l, n)))
    })
}

/// DOM §1.? "valid element local name" (approximated): non-empty, starting
/// with an ASCII alpha, and with no ASCII whitespace, NULL, "/" or ">". The
/// full rule also accepts names starting with characters beyond ASCII.
fn valid_element_local_name(name: &[u32]) -> bool {
    let Some(&first) = name.first() else {
        return false;
    };
    let alpha = |c: u32| (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c);
    if !alpha(first) && first < 0x80 {
        return false;
    }
    !name
        .iter()
        .any(|&c| is_ascii_whitespace(c) || c == 0 || c == u32::from('/') || c == u32::from('>'))
}

/// DOM §1.? "valid attribute local name": non-empty, with no ASCII
/// whitespace, NULL, "/", "=" or ">".
pub(crate) fn valid_attribute_local_name(name: &[u32]) -> bool {
    !name.is_empty()
        && !name.iter().any(|&c| {
            is_ascii_whitespace(c)
                || c == 0
                || c == u32::from('/')
                || c == u32::from('=')
                || c == u32::from('>')
        })
}

/// DOM §1.? "valid namespace prefix" and "valid element local name"
/// together (approximated, as [`valid_element_local_name`] is): a qualified
/// name is one or two such names around a single ":".
pub(crate) fn valid_qualified_name(name: &[u32]) -> bool {
    let mut parts = name.split(|&c| c == u32::from(':'));
    let (Some(a), b, None) = (parts.next(), parts.next(), parts.next()) else {
        return false;
    };
    valid_attribute_local_name(a) && b.is_none_or(valid_attribute_local_name) && !a.is_empty()
}

// ---------------------------------------------------------------------------
// DocumentType, DocumentFragment, CharacterData, Text, Comment

impl DocumentTypeImpl for Page {
    fn name<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let n = node_of(scope, this)?;
        Ok(match page(scope)?.arena.kind(n) {
            ExecKind::DocumentType { name, .. } => points_to_units(name),
            _ => Vec::new(),
        })
    }

    fn public_id<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let n = node_of(scope, this)?;
        Ok(match page(scope)?.arena.kind(n) {
            ExecKind::DocumentType { public_id, .. } => points_to_units(public_id),
            _ => Vec::new(),
        })
    }

    fn system_id<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let n = node_of(scope, this)?;
        Ok(match page(scope)?.arena.kind(n) {
            ExecKind::DocumentType { system_id, .. } => points_to_units(system_id),
            _ => Vec::new(),
        })
    }

    fn before<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        before(scope, this, nodes)
    }

    fn after<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        after(scope, this, nodes)
    }

    fn replace_with<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        replace_with(scope, this, nodes)
    }

    fn remove<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        remove(scope, this)
    }
}

impl DocumentFragmentImpl for Page {
    fn children<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        children_collection(scope, this)
    }

    fn first_element_child<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        first_element_child(scope, this)
    }

    fn last_element_child<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        last_element_child(scope, this)
    }

    fn child_element_count<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        child_element_count(scope, this)
    }

    fn get_element_by_id<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        element_id: DomString,
    ) -> Result<Option<ObjectKey>> {
        get_element_by_id(scope, this, element_id)
    }

    fn prepend<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        prepend(scope, this, nodes)
    }

    fn append<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        append(scope, this, nodes)
    }

    fn replace_children<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        replace_children(scope, this, nodes)
    }

    fn query_selector<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        selectors: DomString,
    ) -> Result<Option<ObjectKey>> {
        query_selector(scope, this, selectors)
    }

    fn query_selector_all<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        selectors: DomString,
    ) -> Result<ObjectKey> {
        query_selector_all(scope, this, selectors)
    }

    /// DOM §4.7† `new DocumentFragment()`: "a new DocumentFragment node whose
    /// node document is current global object's associated Document".
    fn constructor<'s>(scope: &mut Scope<'s>) -> Result<ObjectKey> {
        Ok(key(create(
            scope,
            ExecKind::DocumentFragment { host: None },
        )?))
    }
}

fn data_units(scope: &mut Scope<'_>, this: ObjectKey) -> Result<Vec<u16>> {
    let n = node_of(scope, this)?;
    match data_of(&page(scope)?.arena, n) {
        Some(d) => Ok(points_to_units(d)),
        None => Err(type_error(scope, "not character data")),
    }
}

/// DOM §4.10† "replace data" of node with offset, count and data:
/// "1. Let length be node's length. 2. If offset is greater than length,
/// then throw an IndexSizeError DOMException. 3. If offset plus count is
/// greater than length, then set count to length minus offset. 5. Insert
/// data into node's data after offset code units. 6. Let delete offset be
/// offset + data's length. 7. Starting from delete offset code units,
/// remove count code units from node's data." (Live ranges, steps 8 to 11,
/// do not exist yet.)
fn replace_data(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    offset: u32,
    count: u32,
    data: &[u16],
) -> Result<()> {
    let n = node_of(scope, this)?;
    let units = data_units(scope, this)?;
    let offset = usize::try_from(offset).unwrap_or(usize::MAX);
    let length = units.len();
    if offset > length {
        return Err(dom_error(
            scope,
            DomErrorName::IndexSizeError,
            "offset is past the end of the data",
        ));
    }
    let count = usize::try_from(count)
        .unwrap_or(usize::MAX)
        .min(length.saturating_sub(offset));
    let end = offset.saturating_add(count);
    page(scope)?.replace_data_units(n, offset, end.saturating_sub(offset), data);
    Ok(())
}

impl CharacterDataImpl for Page {
    fn data<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        data_units(scope, this)
    }

    /// DOM §4.10† `data` setter: "replace data with node this, offset 0,
    /// count this's length, and data the given value".
    fn set_data<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: DomString) -> Result<()> {
        let n = node_of(scope, this)?;
        if data_of(&page(scope)?.arena, n).is_none() {
            return Err(type_error(scope, "not character data"));
        }
        page(scope)?.set_node_data(n, &units_to_points(&value));
        Ok(())
    }

    /// DOM §4.10† `length`: "this's length" (code units).
    fn length<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(u32::try_from(data_units(scope, this)?.len()).unwrap_or(u32::MAX))
    }

    fn previous_element_sibling<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        previous_element_sibling(scope, this)
    }

    fn next_element_sibling<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        next_element_sibling(scope, this)
    }

    /// DOM §4.10† "substring data": "2. If offset is greater than length,
    /// then throw an IndexSizeError. 3. If offset plus count is greater than
    /// length, return a string whose value is the code units from the
    /// offsetth code unit to the end of node's data, and then return. 4.
    /// Return a string whose value is the code units from the offsetth code
    /// unit to the offset+countth code unit in node's data."
    fn substring_data<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        offset: u32,
        count: u32,
    ) -> Result<DomString> {
        let units = data_units(scope, this)?;
        let offset = usize::try_from(offset).unwrap_or(usize::MAX);
        if offset > units.len() {
            return Err(dom_error(
                scope,
                DomErrorName::IndexSizeError,
                "offset is past the end of the data",
            ));
        }
        let count = usize::try_from(count).unwrap_or(usize::MAX);
        Ok(units.iter().skip(offset).take(count).copied().collect())
    }

    /// DOM §4.10† `appendData(data)`: "replace data with node this, offset
    /// this's length, count 0, and data data".
    fn append_data<'s>(scope: &mut Scope<'s>, this: ObjectKey, data: DomString) -> Result<()> {
        let len = u32::try_from(data_units(scope, this)?.len()).unwrap_or(u32::MAX);
        replace_data(scope, this, len, 0, &data)
    }

    /// DOM §4.10† `insertData(offset, data)`: "replace data with node this,
    /// offset offset, count 0, and data data".
    fn insert_data<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        offset: u32,
        data: DomString,
    ) -> Result<()> {
        replace_data(scope, this, offset, 0, &data)
    }

    /// DOM §4.10† `deleteData(offset, count)`: "replace data with node this,
    /// offset offset, count count, and data the empty string".
    fn delete_data<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        offset: u32,
        count: u32,
    ) -> Result<()> {
        replace_data(scope, this, offset, count, &[])
    }

    fn replace_data<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        offset: u32,
        count: u32,
        data: DomString,
    ) -> Result<()> {
        replace_data(scope, this, offset, count, &data)
    }

    fn before<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        before(scope, this, nodes)
    }

    fn after<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        after(scope, this, nodes)
    }

    fn replace_with<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        replace_with(scope, this, nodes)
    }

    fn remove<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        remove(scope, this)
    }
}

impl TextImpl for Page {
    /// DOM §4.11† `new Text(data)`: "a new Text node whose data is data".
    fn constructor<'s>(scope: &mut Scope<'s>, data: DomString) -> Result<ObjectKey> {
        Ok(key(create(
            scope,
            ExecKind::Text {
                data: units_to_points(&data),
            },
        )?))
    }

    /// DOM §4.11† `splitText(offset)`: "Split this with offset."
    fn split_text<'s>(scope: &mut Scope<'s>, this: ObjectKey, offset: u32) -> Result<ObjectKey> {
        let n = node_of(scope, this)?;
        let offset = usize::try_from(offset).unwrap_or(usize::MAX);
        Ok(key(split_text(scope, n, offset)?))
    }

    /// DOM §4.11† `wholeText`: "the concatenation of the data of the
    /// contiguous Text nodes of this, in tree order".
    fn whole_text<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let n = node_of(scope, this)?;
        let arena = &page(scope)?.arena;
        let is_text = |x: usize| matches!(arena.kind(x), ExecKind::Text { .. });
        let mut first = n;
        while let Some(p) = arena.previous_sibling(first) {
            if !is_text(p) {
                break;
            }
            first = p;
        }
        let mut out = Vec::new();
        let mut cur = Some(first);
        while let Some(x) = cur {
            if !is_text(x) {
                break;
            }
            out.extend(data_of(arena, x).map(points_to_units).unwrap_or_default());
            cur = arena.next_sibling(x);
        }
        Ok(out)
    }
}

/// DOM §4.5† "validate" a processing instruction: "1. If target does not
/// match the Name production, then throw an InvalidCharacterError. 2. If
/// data contains the string "?>", then throw an InvalidCharacterError."
fn new_processing_instruction(
    scope: &mut Scope<'_>,
    target: &[u16],
    data: &[u16],
) -> Result<ObjectKey> {
    let t = units_to_points(target);
    let d = units_to_points(data);
    let bad_data = d.windows(2).any(|w| w == [u32::from('?'), u32::from('>')]);
    if !valid_element_local_name(&t) || bad_data {
        return Err(dom_error(
            scope,
            DomErrorName::InvalidCharacterError,
            "not a valid processing instruction",
        ));
    }
    Ok(key(create(
        scope,
        ExecKind::ProcessingInstruction { target: t, data: d },
    )?))
}

impl ProcessingInstructionImpl for Page {
    /// DOM §4.13† `new ProcessingInstruction(target, data)` (the curated
    /// IDL's constructor).
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        target: DomString,
        data: DomString,
    ) -> Result<ObjectKey> {
        new_processing_instruction(scope, &target, &data)
    }

    /// DOM §4.13† `target`.
    fn target<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let n = node_of(scope, this)?;
        match page(scope)?.arena.kind(n) {
            ExecKind::ProcessingInstruction { target, .. } => Ok(points_to_units(target)),
            _ => Err(type_error(scope, "not a ProcessingInstruction")),
        }
    }
}

impl CommentImpl for Page {
    /// DOM §4.14† `new Comment(data)`.
    fn constructor<'s>(scope: &mut Scope<'s>, data: DomString) -> Result<ObjectKey> {
        Ok(key(create(
            scope,
            ExecKind::Comment {
                data: units_to_points(&data),
            },
        )?))
    }
}

// ---------------------------------------------------------------------------
// Element

fn attribute_get(scope: &mut Scope<'_>, this: ObjectKey, name: &str) -> Result<DomString> {
    let e = element_of(scope, this)?;
    Ok(attribute_value(&page(scope)?.arena, e, &str_points(name))
        .map(|v| points_to_units(&v))
        .unwrap_or_default())
}

fn attribute_set(scope: &mut Scope<'_>, this: ObjectKey, name: &str, value: &[u16]) -> Result<()> {
    let e = element_of(scope, this)?;
    set_attribute_value(page(scope)?, e, &str_points(name), units_to_points(value));
    Ok(())
}

impl ElementImpl for Page {
    /// DOM §4.9† `namespaceURI`.
    fn namespace_uri<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<DomString>> {
        let e = element_of(scope, this)?;
        Ok(match page(scope)?.arena.kind(e) {
            ExecKind::Element {
                namespace: Some(ns),
                ..
            } => Some(str_units(match ns {
                Namespace::Html => HTML_NS,
                Namespace::Svg => SVG_NS,
                Namespace::MathMl => MATHML_NS,
                Namespace::XLink => "http://www.w3.org/1999/xlink",
                Namespace::Xml => "http://www.w3.org/XML/1998/namespace",
                Namespace::Xmlns => "http://www.w3.org/2000/xmlns/",
            })),
            _ => None,
        })
    }

    fn prefix<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<DomString>> {
        let e = element_of(scope, this)?;
        Ok(match page(scope)?.arena.kind(e) {
            ExecKind::Element { prefix, .. } => prefix.as_ref().map(|p| points_to_units(p)),
            _ => None,
        })
    }

    fn local_name<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let e = element_of(scope, this)?;
        Ok(local_name_of(&page(scope)?.arena, e)
            .map(points_to_units)
            .unwrap_or_default())
    }

    /// DOM §4.9† `tagName`: "this's HTML-uppercased qualified name".
    fn tag_name<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let e = element_of(scope, this)?;
        Ok(points_to_units(&html_uppercased_qualified_name(
            &page(scope)?.arena,
            e,
        )))
    }

    /// DOM §4.9† `id` reflects the "id" content attribute.
    fn id<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        attribute_get(scope, this, "id")
    }

    fn set_id<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: DomString) -> Result<()> {
        attribute_set(scope, this, "id", &value)
    }

    /// DOM §4.9† `className` reflects the "class" content attribute.
    fn class_name<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        attribute_get(scope, this, "class")
    }

    fn set_class_name<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: DomString) -> Result<()> {
        attribute_set(scope, this, "class", &value)
    }

    /// DOM §4.9† `classList`: "a DOMTokenList object whose associated element
    /// is this and whose associated attribute's local name is class"
    /// ([SameObject] and [PutForwards=value] are the bindings').
    fn class_list<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        let e = element_of(scope, this)?;
        Ok(page(scope)?.add_object(Object::TokenList(e)))
    }

    fn slot<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        attribute_get(scope, this, "slot")
    }

    fn set_slot<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: DomString) -> Result<()> {
        attribute_set(scope, this, "slot", &value)
    }

    /// HTML §13.? `innerHTML` getter: "the result of running fragment
    /// serializing algorithm steps with this and true" (scripting enabled).
    fn inner_html<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let e = element_of(scope, this)?;
        Ok(points_to_units(&crate::serialize::serialize_fragment(
            &page(scope)?.arena,
            e,
            true,
        )))
    }

    /// `outerHTML` getter: the serialization of the element itself.
    fn outer_html<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let e = element_of(scope, this)?;
        Ok(points_to_units(&crate::serialize::serialize_outer(
            &page(scope)?.arena,
            e,
            true,
        )))
    }

    fn children<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        children_collection(scope, this)
    }

    fn first_element_child<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        first_element_child(scope, this)
    }

    fn last_element_child<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        last_element_child(scope, this)
    }

    fn child_element_count<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        child_element_count(scope, this)
    }

    fn previous_element_sibling<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        previous_element_sibling(scope, this)
    }

    fn next_element_sibling<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        next_element_sibling(scope, this)
    }

    /// DOM §4.9† `hasAttributes()`: "false if this's attribute list is
    /// empty; otherwise true".
    fn has_attributes<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        let e = element_of(scope, this)?;
        Ok(!attributes_of(&page(scope)?.arena, e).is_empty())
    }

    /// DOM §4.9† `getAttributeNames()`: "the qualified names of the
    /// attributes in this's attribute list, in order".
    fn get_attribute_names<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Vec<DomString>> {
        let e = element_of(scope, this)?;
        Ok(attributes_of(&page(scope)?.arena, e)
            .iter()
            .map(|a| points_to_units(&qualified(a)))
            .collect())
    }

    /// DOM §4.9† `getAttribute(qualifiedName)`: "1. Let attr be the result
    /// of getting an attribute given qualifiedName and this. 2. If attr is
    /// null, return null. 3. Return attr's value."
    fn get_attribute<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
    ) -> Result<Option<DomString>> {
        let e = element_of(scope, this)?;
        Ok(
            attribute_value(&page(scope)?.arena, e, &units_to_points(&qualified_name))
                .map(|v| points_to_units(&v)),
        )
    }

    /// DOM §4.9† `setAttribute(qualifiedName, value)`: "1. If qualifiedName
    /// is not a valid attribute local name, then throw an
    /// InvalidCharacterError." Then [`set_attribute_value`].
    fn set_attribute<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
        value: DomString,
    ) -> Result<()> {
        let e = element_of(scope, this)?;
        let name = units_to_points(&qualified_name);
        if !valid_attribute_local_name(&name) {
            return Err(dom_error(
                scope,
                DomErrorName::InvalidCharacterError,
                "not a valid attribute name",
            ));
        }
        set_attribute_value(page(scope)?, e, &name, units_to_points(&value));
        Ok(())
    }

    /// DOM §4.9† `removeAttribute(qualifiedName)`: "Remove an attribute
    /// given qualifiedName and this."
    fn remove_attribute<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
    ) -> Result<()> {
        let e = element_of(scope, this)?;
        remove_attribute_named(page(scope)?, e, &units_to_points(&qualified_name));
        Ok(())
    }

    /// DOM §4.9† `toggleAttribute(qualifiedName, force)`: "1. If
    /// qualifiedName is not a valid attribute local name, throw an
    /// InvalidCharacterError. 3. Let attribute be the first attribute ...
    /// 4. If attribute is null: if force is not given or is true, create an
    /// attribute whose value is the empty string, append it, and return
    /// true; otherwise return false. 5. Otherwise, if force is not given or
    /// is false, remove an attribute given qualifiedName and this, and then
    /// return false. 6. Return true."
    fn toggle_attribute<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
        force: Option<bool>,
    ) -> Result<bool> {
        let e = element_of(scope, this)?;
        let name = units_to_points(&qualified_name);
        if !valid_attribute_local_name(&name) {
            return Err(dom_error(
                scope,
                DomErrorName::InvalidCharacterError,
                "not a valid attribute name",
            ));
        }
        let page = page(scope)?;
        if attribute_index(&page.arena, e, &name).is_none() {
            if force != Some(false) {
                set_attribute_value(page, e, &name, Vec::new());
                return Ok(true);
            }
            return Ok(false);
        }
        if force != Some(true) {
            remove_attribute_named(page, e, &name);
            return Ok(false);
        }
        Ok(true)
    }

    fn has_attribute<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
    ) -> Result<bool> {
        let e = element_of(scope, this)?;
        Ok(attribute_index(&page(scope)?.arena, e, &units_to_points(&qualified_name)).is_some())
    }

    /// DOM §4.9† `attributes`: "a NamedNodeMap object whose associated
    /// element is this" ([SameObject] is the bindings').
    fn attributes<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        super::attr::attributes_map(scope, this)
    }

    /// DOM §4.9† `getAttributeNS(namespace, localName)`: "1. Let attr be the
    /// result of getting an attribute given namespace, localName, and this.
    /// 2. If attr is null, return null. 3. Return attr's value."
    fn get_attribute_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
        local_name: DomString,
    ) -> Result<Option<DomString>> {
        let e = element_of(scope, this)?;
        let arena = &page(scope)?.arena;
        Ok(
            super::attr::by_name_ns(arena, e, &namespace, &units_to_points(&local_name))
                .and_then(|i| attributes_of(arena, e).get(i))
                .map(|a| points_to_units(&a.value)),
        )
    }

    /// DOM §4.9† `setAttributeNS(namespace, qualifiedName, value)`: "1. Let
    /// namespace, prefix, and localName be the result of passing namespace
    /// and qualifiedName to validate and extract. 2. Set an attribute value
    /// for this using localName, value, and also prefix and namespace."
    fn set_attribute_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
        qualified_name: DomString,
        value: DomString,
    ) -> Result<()> {
        let e = element_of(scope, this)?;
        let (ns, prefix, local) =
            super::attr::validate_and_extract(scope, &namespace, &qualified_name)?;
        let value = units_to_points(&value);
        let p = page(scope)?;
        match super::attr::find_attribute(&p.arena, e, ns.as_ref(), &local) {
            Some(i) => p.attr_change(e, i, value),
            None => p.attr_append(
                e,
                ExecAttr {
                    namespace: ns,
                    prefix,
                    local_name: local,
                    value,
                },
            ),
        }
        Ok(())
    }

    /// DOM §4.9† `removeAttributeNS(namespace, localName)`: "Remove an
    /// attribute given namespace, localName, and this."
    fn remove_attribute_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
        local_name: DomString,
    ) -> Result<()> {
        let e = element_of(scope, this)?;
        let p = page(scope)?;
        if let Some(i) =
            super::attr::by_name_ns(&p.arena, e, &namespace, &units_to_points(&local_name))
        {
            p.attr_remove(e, i);
        }
        Ok(())
    }

    fn has_attribute_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
        local_name: DomString,
    ) -> Result<bool> {
        let e = element_of(scope, this)?;
        Ok(super::attr::by_name_ns(
            &page(scope)?.arena,
            e,
            &namespace,
            &units_to_points(&local_name),
        )
        .is_some())
    }

    fn get_attribute_node<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
    ) -> Result<Option<ObjectKey>> {
        super::attr::get_attribute_node(scope, this, &qualified_name)
    }

    fn get_attribute_node_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
        local_name: DomString,
    ) -> Result<Option<ObjectKey>> {
        super::attr::get_attribute_node_ns(scope, this, &namespace, &local_name)
    }

    fn set_attribute_node<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        attr: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        super::attr::set_attribute_node_of(scope, this, attr)
    }

    fn set_attribute_node_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        attr: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        super::attr::set_attribute_node_of(scope, this, attr)
    }

    fn remove_attribute_node<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        attr: ObjectKey,
    ) -> Result<ObjectKey> {
        super::attr::remove_attribute_node(scope, this, attr)
    }

    /// HTML §13.? `innerHTML` setter: "1. Let context be this. 2. Let
    /// fragment be the result of invoking the fragment parsing algorithm
    /// steps with context and the given value. 3. If context is a template
    /// element, then set context to the template element's template
    /// contents (a DocumentFragment). 4. Replace all with fragment within
    /// context."
    fn set_inner_html<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: DomString) -> Result<()> {
        let e = element_of(scope, this)?;
        let fragment = parse_in(scope, e, &units_to_points(&value))?;
        let arena = &page(scope)?.arena;
        let target = match arena.kind(e) {
            ExecKind::Element {
                template_contents: Some(c),
                ..
            } => *c,
            _ => e,
        };
        page(scope)?.replace_all_with(Some(fragment), target);
        Ok(())
    }

    /// DOM Parsing §? `outerHTML` setter: "1. Let parent be this's parent.
    /// 2. If parent is null, return. 3. If parent is a Document, throw a
    /// NoModificationAllowedError. 4. If parent is a DocumentFragment, set
    /// parent to the result of creating an element given this's node
    /// document, body, and the HTML namespace. 5. Let fragment be the result
    /// of invoking the fragment parsing algorithm steps given parent and the
    /// given value. 6. Replace this with fragment within this's parent."
    fn set_outer_html<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: DomString) -> Result<()> {
        let e = element_of(scope, this)?;
        let Some(parent) = page(scope)?.arena.parent(e) else {
            return Ok(());
        };
        let context = match page(scope)?.arena.kind(parent) {
            ExecKind::Document { .. } => {
                return Err(dom_error(
                    scope,
                    DomErrorName::NoModificationAllowedError,
                    "the element is a child of the document",
                ));
            }
            ExecKind::DocumentFragment { .. } => new_body_element(scope)?,
            _ => parent,
        };
        let fragment = parse_in(scope, context, &units_to_points(&value))?;
        match page(scope)?.replace_node(e, fragment, parent) {
            Some(err) => Err(dom_error_of(scope, err)),
            None => Ok(()),
        }
    }

    /// DOM §4.9† `insertAdjacentElement(where, element)`: "Return the result
    /// of running insert adjacent, given this, where, and element."
    fn insert_adjacent_element<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        where_: DomString,
        element: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        let e = element_of(scope, this)?;
        let w = adjacent_position(scope, &where_)?;
        let el = element_of(scope, element)?;
        Ok(insert_adjacent(scope, e, w, el)?.then_some(element))
    }

    /// DOM §4.9† `insertAdjacentText(where, data)`: "1. Let text be a new
    /// Text node whose data is data and node document is this's node
    /// document. 2. Run insert adjacent, given this, where, and text."
    fn insert_adjacent_text<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        where_: DomString,
        data: DomString,
    ) -> Result<()> {
        let e = element_of(scope, this)?;
        let w = adjacent_position(scope, &where_)?;
        let text = create(
            scope,
            ExecKind::Text {
                data: units_to_points(&data),
            },
        )?;
        insert_adjacent(scope, e, w, text)?;
        Ok(())
    }

    /// DOM Parsing §? `insertAdjacentHTML(position, string)`: "1. Let
    /// position be the position argument ASCII-lowercased. 2. Let context
    /// be null. 3. Use the first matching item from this list: If position
    /// is "beforebegin" or "afterend": Set context to this's parent. If
    /// context is null or a Document, throw a NoModificationAllowedError.
    /// If position is "afterbegin" or "beforeend": Set context to this. 4.
    /// If context is not an Element or the following are all true: context's
    /// node document is an HTML document, context's local name is "html",
    /// and context's namespace is the HTML namespace; then set context to
    /// the result of creating an element given this's node document, body,
    /// and the HTML namespace. 5. Let fragment be the result of invoking
    /// the fragment parsing algorithm steps given context and string. 6. Use
    /// the first matching item from this list: "beforebegin": Insert fragment
    /// into this's parent before this. "afterbegin": Insert fragment into
    /// this before its first child. "beforeend": Append fragment to this.
    /// "afterend": Insert fragment into this's parent before this's next
    /// sibling."
    fn insert_adjacent_html<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        position: DomString,
        string: DomString,
    ) -> Result<()> {
        let e = element_of(scope, this)?;
        let w = adjacent_position(scope, &position)?;
        let parent = page(scope)?.arena.parent(e);
        let context = if w == 0 || w == 3 {
            match parent {
                Some(p) if !matches!(page(scope)?.arena.kind(p), ExecKind::Document { .. }) => p,
                _ => {
                    return Err(dom_error(
                        scope,
                        DomErrorName::NoModificationAllowedError,
                        "the element has no parent to insert into",
                    ));
                }
            }
        } else {
            e
        };
        let arena = &page(scope)?.arena;
        let context = if is_element(arena, context) && !is_html_named(arena, context, "html") {
            context
        } else {
            new_body_element(scope)?
        };
        let fragment = parse_in(scope, context, &units_to_points(&string))?;
        insert_adjacent(scope, e, w, fragment)?;
        Ok(())
    }

    /// DOM §4.9† `closest(selectors)`.
    fn closest<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        selectors: DomString,
    ) -> Result<Option<ObjectKey>> {
        let e = element_of(scope, this)?;
        match crate::selectors::closest(&page(scope)?.arena, e, &units_to_points(&selectors)) {
            Ok(found) => Ok(found.map(key)),
            Err(_) => Err(dom_error(
                scope,
                DomErrorName::SyntaxError,
                "not a valid selector",
            )),
        }
    }

    /// DOM §4.9† `matches(selectors)` and `webkitMatchesSelector`.
    fn matches<'s>(scope: &mut Scope<'s>, this: ObjectKey, selectors: DomString) -> Result<bool> {
        let e = element_of(scope, this)?;
        match crate::selectors::matches(&page(scope)?.arena, e, &units_to_points(&selectors)) {
            Ok(m) => Ok(m),
            Err(_) => Err(dom_error(
                scope,
                DomErrorName::SyntaxError,
                "not a valid selector",
            )),
        }
    }

    fn webkit_matches_selector<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        selectors: DomString,
    ) -> Result<bool> {
        <Page as ElementImpl>::matches(scope, this, selectors)
    }

    fn get_elements_by_tag_name<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
    ) -> Result<ObjectKey> {
        by_tag(scope, this, qualified_name)
    }

    /// DOM §4.4† `getElementsByTagNameNS(namespace, localName)`: "the list
    /// of elements with namespace namespace and local name localName for
    /// this".
    fn get_elements_by_tag_name_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
        local_name: DomString,
    ) -> Result<ObjectKey> {
        by_tag_ns(scope, this, namespace, local_name)
    }

    fn get_elements_by_class_name<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        class_names: DomString,
    ) -> Result<ObjectKey> {
        by_class(scope, this, class_names)
    }

    fn prepend<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        prepend(scope, this, nodes)
    }

    fn append<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        append(scope, this, nodes)
    }

    fn replace_children<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        replace_children(scope, this, nodes)
    }

    fn query_selector<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        selectors: DomString,
    ) -> Result<Option<ObjectKey>> {
        query_selector(scope, this, selectors)
    }

    fn query_selector_all<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        selectors: DomString,
    ) -> Result<ObjectKey> {
        query_selector_all(scope, this, selectors)
    }

    fn before<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        before(scope, this, nodes)
    }

    fn after<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        after(scope, this, nodes)
    }

    fn replace_with<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        nodes: Vec<NodeOrDOMString>,
    ) -> Result<()> {
        replace_with(scope, this, nodes)
    }

    fn remove<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        remove(scope, this)
    }
}

// The HTML element interfaces: their `[Reflect]` attributes are the
// bindings'; the rest keep the generated defaults.
impl HTMLElementImpl for Page {
    /// HTML §3.2.6.6† `dataset`: "a DOMStringMap object whose associated
    /// element is this".
    fn dataset<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        super::attr::dataset_object(scope, this)
    }
}
impl HTMLUnknownElementImpl for Page {}
impl HTMLHtmlElementImpl for Page {}
impl HTMLHeadElementImpl for Page {}
impl HTMLBodyElementImpl for Page {}
impl HTMLDivElementImpl for Page {}
impl HTMLSpanElementImpl for Page {}
impl HTMLParagraphElementImpl for Page {}
impl HTMLAnchorElementImpl for Page {}

impl HTMLTitleElementImpl for Page {
    /// HTML §4.2.2† `text` getter: "the child text content of the title
    /// element".
    fn text<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let e = element_of(scope, this)?;
        let arena = &page(scope)?.arena;
        let mut out = Vec::new();
        for &c in arena.children(e) {
            if let ExecKind::Text { data } = arena.kind(c) {
                out.extend_from_slice(data);
            }
        }
        Ok(points_to_units(&out))
    }

    /// HTML §4.2.2† `text` setter: "string replace all with the given value
    /// within this title element".
    fn set_text<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: DomString) -> Result<()> {
        <Page as NodeImpl>::set_text_content(scope, this, Some(value))
    }
}

// ---------------------------------------------------------------------------
// NodeList, HTMLCollection

impl NodeListImpl for Page {
    /// DOM §4.2.10.1† `length`: "the number of nodes represented by the
    /// collection".
    fn length<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(u32::try_from(items_of(scope, this)?.len()).unwrap_or(u32::MAX))
    }

    /// `item(index)`: "the indexth node in the collection, or null".
    fn item<'s>(scope: &mut Scope<'s>, this: ObjectKey, index: u32) -> Result<Option<ObjectKey>> {
        let items = items_of(scope, this)?;
        Ok(usize::try_from(index)
            .ok()
            .and_then(|i| items.get(i))
            .map(|&n| key(n)))
    }
}

impl HTMLCollectionImpl for Page {
    fn length<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(u32::try_from(items_of(scope, this)?.len()).unwrap_or(u32::MAX))
    }

    fn item<'s>(scope: &mut Scope<'s>, this: ObjectKey, index: u32) -> Result<Option<ObjectKey>> {
        let items = items_of(scope, this)?;
        Ok(usize::try_from(index)
            .ok()
            .and_then(|i| items.get(i))
            .map(|&n| key(n)))
    }

    /// DOM §4.2.10.2† `namedItem(key)`: "1. If key is the empty string,
    /// return null. 2. Return the first element in the collection for which
    /// ... it has an ID which is key; or it is in the HTML namespace and has
    /// a name attribute whose value is key; or null."
    fn named_item<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        name: DomString,
    ) -> Result<Option<ObjectKey>> {
        let name = units_to_points(&name);
        if name.is_empty() {
            return Ok(None);
        }
        let items = items_of(scope, this)?;
        let arena = &page(scope)?.arena;
        Ok(items
            .into_iter()
            .find(|&e| {
                attribute_value(arena, e, &str_points("id")).as_deref() == Some(name.as_slice())
                    || (is_html_element(arena, e)
                        && attribute_value(arena, e, &str_points("name")).as_deref()
                            == Some(name.as_slice()))
            })
            .map(key))
    }
}

// ---------------------------------------------------------------------------
// DOMTokenList (DOM §7.1†), for `classList`

fn token_element(scope: &mut Scope<'_>, this: ObjectKey) -> Result<usize> {
    match page(scope)?.object(this) {
        Some(Object::TokenList(e)) => Ok(*e),
        _ => Err(type_error(scope, "not a DOMTokenList")),
    }
}

/// The token set: the ordered set parser on the attribute's value.
fn tokens(scope: &mut Scope<'_>, this: ObjectKey) -> Result<(usize, Vec<Vec<u32>>)> {
    let e = token_element(scope, this)?;
    let v = attribute_value(&page(scope)?.arena, e, &str_points("class")).unwrap_or_default();
    Ok((e, split_tokens(&v)))
}

/// DOM §7.1† "update steps": "1. If the associated element does not have an
/// associated attribute and token set is empty, then return. 2. Set an
/// attribute value for the associated element using associated attribute's
/// local name and the result of running the ordered set serializer for
/// token set."
fn update(scope: &mut Scope<'_>, e: usize, set: &[Vec<u32>]) -> Result<()> {
    let page = page(scope)?;
    let name = str_points("class");
    if attribute_index(&page.arena, e, &name).is_none() && set.is_empty() {
        return Ok(());
    }
    set_attribute_value(page, e, &name, set.join(&u32::from(' ')));
    Ok(())
}

/// The token checks of `add`, `remove`, `toggle` and `replace`: "If token
/// is the empty string, then throw a SyntaxError. If token contains any
/// ASCII whitespace, then throw an InvalidCharacterError."
fn check_token(scope: &mut Scope<'_>, t: &[u32]) -> Result<()> {
    if t.is_empty() {
        return Err(dom_error(
            scope,
            DomErrorName::SyntaxError,
            "the token is empty",
        ));
    }
    if t.iter().any(|&c| is_ascii_whitespace(c)) {
        return Err(dom_error(
            scope,
            DomErrorName::InvalidCharacterError,
            "the token contains whitespace",
        ));
    }
    Ok(())
}

impl DOMTokenListImpl for Page {
    fn length<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(u32::try_from(tokens(scope, this)?.1.len()).unwrap_or(u32::MAX))
    }

    /// DOM §7.1† `value`: the associated attribute's value.
    fn value<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let e = token_element(scope, this)?;
        Ok(
            attribute_value(&page(scope)?.arena, e, &str_points("class"))
                .map(|v| points_to_units(&v))
                .unwrap_or_default(),
        )
    }

    fn set_value<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: DomString) -> Result<()> {
        let e = token_element(scope, this)?;
        set_attribute_value(
            page(scope)?,
            e,
            &str_points("class"),
            units_to_points(&value),
        );
        Ok(())
    }

    fn item<'s>(scope: &mut Scope<'s>, this: ObjectKey, index: u32) -> Result<Option<DomString>> {
        let (_, set) = tokens(scope, this)?;
        Ok(usize::try_from(index)
            .ok()
            .and_then(|i| set.get(i))
            .map(|t| points_to_units(t)))
    }

    fn contains<'s>(scope: &mut Scope<'s>, this: ObjectKey, token: DomString) -> Result<bool> {
        let (_, set) = tokens(scope, this)?;
        Ok(set.contains(&units_to_points(&token)))
    }

    /// DOM §7.1† `add(tokens...)`: check each token, append those not in
    /// the token set, run the update steps.
    fn add<'s>(scope: &mut Scope<'s>, this: ObjectKey, tokens_: Vec<DomString>) -> Result<()> {
        let new: Vec<Vec<u32>> = tokens_.iter().map(|t| units_to_points(t)).collect();
        for t in &new {
            check_token(scope, t)?;
        }
        let (e, mut set) = tokens(scope, this)?;
        for t in new {
            if !set.contains(&t) {
                set.push(t);
            }
        }
        update(scope, e, &set)
    }

    /// DOM §7.1† `remove(tokens...)`.
    fn remove<'s>(scope: &mut Scope<'s>, this: ObjectKey, tokens_: Vec<DomString>) -> Result<()> {
        let gone: Vec<Vec<u32>> = tokens_.iter().map(|t| units_to_points(t)).collect();
        for t in &gone {
            check_token(scope, t)?;
        }
        let (e, mut set) = tokens(scope, this)?;
        set.retain(|t| !gone.contains(t));
        update(scope, e, &set)
    }

    /// DOM §7.1† `toggle(token, force)`: "3. If this's token set[token]
    /// exists: if force is either not given or is false, remove token, run
    /// the update steps and return false; return true. 4. Otherwise, if
    /// force not given or is true, append token, run the update steps, and
    /// return true. 5. Return false."
    fn toggle<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        token: DomString,
        force: Option<bool>,
    ) -> Result<bool> {
        let t = units_to_points(&token);
        check_token(scope, &t)?;
        let (e, mut set) = tokens(scope, this)?;
        if set.contains(&t) {
            if force != Some(true) {
                set.retain(|x| *x != t);
                update(scope, e, &set)?;
                return Ok(false);
            }
            return Ok(true);
        }
        if force != Some(false) {
            set.push(t);
            update(scope, e, &set)?;
            return Ok(true);
        }
        Ok(false)
    }

    /// DOM §7.1† `replace(token, newToken)`: "4. If this's token set does not
    /// contain token, then return false. 5. Replace token in this's token set
    /// with newToken. 6. Run the update steps. 7. Return true."
    fn replace<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        token: DomString,
        new_token: DomString,
    ) -> Result<bool> {
        let t = units_to_points(&token);
        let n = units_to_points(&new_token);
        check_token(scope, &t)?;
        check_token(scope, &n)?;
        let (e, set) = tokens(scope, this)?;
        if !set.contains(&t) {
            return Ok(false);
        }
        // Infra "replace": the first of token and newToken takes the place,
        // and the other occurrences go.
        let mut out: Vec<Vec<u32>> = Vec::new();
        for x in set {
            let y = if x == t { n.clone() } else { x };
            if !out.contains(&y) {
                out.push(y);
            }
        }
        update(scope, e, &out)?;
        Ok(true)
    }

    /// DOM §7.1† `supports(token)`: "the associated attribute's local name
    /// does not define supported tokens, throw a TypeError" (`class` does
    /// not).
    fn supports<'s>(scope: &mut Scope<'s>, _this: ObjectKey, _token: DomString) -> Result<bool> {
        Err(type_error(scope, "classList has no supported tokens"))
    }
}
