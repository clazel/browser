//! HTML §13.2.6.1 "Creating and inserting nodes", §13.2.6.2 "Parsing
//! elements that contain only text", §13.2.6.3 "Closing elements that have
//! implied end tags", and §13.2.4.3's "reconstruct the active formatting
//! elements" (which inserts). The modelling choices are listed in
//! [`super`].

#[allow(unused_imports)]
use super::state::*;
#[allow(unused_imports)]
use super::tags::*;
use clazel_dom::spec as dom;
use clazel_dom::spec::{Attr, Document, Namespace, NodeId, NodeKind};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Guarded DOM calls

/// The checks of DOM's "ensure pre-insert validity" that `clazel-dom`'s
/// `insert` takes as its precondition (`dom::insert_requires` without `wf`,
/// which the parser keeps: `theorem_doc_wf`).
pub open spec fn insert_valid(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    &&& dom::valid(doc, node)
    &&& dom::valid(doc, parent)
    &&& !(doc.nodes[node as int].kind is Document)
    &&& !(doc.nodes[node as int].kind is DocumentFragment)
    &&& dom::may_have_children(doc.nodes[parent as int].kind)
    &&& !dom::is_inclusive_ancestor(doc, node, parent)
    &&& match child {
        None => true,
        Some(c) => dom::valid(doc, c) && c != node && doc.nodes[c as int].parent == Some(parent),
    }
}

/// DOM "insert" `node` into `parent` before `child`, as the parser calls
/// it. The call is made only when [`insert_valid`] holds; the parser's calls
/// always satisfy it (DOM: "Assert: ensure pre-insert validity … does not
/// throw", §13.2.6.1 "insert an element at the adjusted insertion location"
/// step 4), so the guard only makes that assertion explicit.
pub open spec fn dom_insert(p: Parser, node: NodeId, parent: NodeId, child: Option<NodeId>) -> Parser {
    if p.stopped || !insert_valid(p.doc, node, parent, child) {
        p
    } else {
        Parser { doc: dom::insert(p.doc, node, parent, child), ..p }
    }
}

/// DOM "remove" `node` from its parent, as the parser calls it (only when it
/// has one: "if node's parent is non-null, remove it").
pub open spec fn dom_remove(p: Parser, node: NodeId) -> Parser {
    if p.stopped || !dom::valid(p.doc, node) || p.doc.nodes[node as int].parent is None {
        p
    } else {
        Parser { doc: dom::remove(p.doc, node), ..p }
    }
}

/// §13.2.7 "stop parsing", the steps that touch the parse state: "4. Pop
/// all the nodes off the stack of open elements." Steps 1 to 3 and 5
/// onward (the speculative parser, the insertion point, document
/// readiness, scripts, events) are the driver's and Phase 7's; the step
/// returns [`Action::StopParsing`] for them.
pub open spec fn stop_parsing(p: Parser) -> Parser {
    if p.stopped {
        p
    } else {
        Parser { open: seq![], stopped: true, actions: p.actions.push(Action::StopParsing), ..p }
    }
}

/// Create a node, or stop parsing at the node limit
/// (`clazel_dom::spec::max_nodes`): the new parser and the node's id.
pub open spec fn create(p: Parser, k: NodeKind) -> (Parser, NodeId) {
    if p.stopped {
        (p, 0)
    } else if !dom::can_create(p.doc, 1) {
        (stop_parsing(p), 0)
    } else {
        let (d, id) = dom::create_node(p.doc, k);
        (Parser { doc: d, ..p }, id)
    }
}

// ---------------------------------------------------------------------
// The appropriate place for inserting a node

/// The element is a table, tbody, tfoot, thead or tr element.
pub open spec fn is_table_like(e: Elem) -> bool {
    is_html(e, Tag::Table) || is_html(e, Tag::Tbody) || is_html(e, Tag::Tfoot) || is_html(e, Tag::Thead) || is_html(e, Tag::Tr)
}

/// The node is an HTML `template` element.
pub open spec fn node_is_template(doc: Document, n: NodeId) -> bool {
    dom::valid(doc, n) && match doc.nodes[n as int].kind {
        NodeKind::Element { namespace, local_name, .. } => namespace == Some(Namespace::Html) && tag_of(local_name) == Tag::Template,
        _ => false,
    }
}

/// A template element's template contents (DOM: its `template_contents`).
pub open spec fn template_contents(doc: Document, n: NodeId) -> NodeId {
    doc.nodes[n as int].kind->Element_template_contents->Some_0
}

/// §13.2.6.1 "appropriate place for inserting a node", given an optional
/// overrideTarget.
pub open spec fn appropriate_place(p: Parser, override_target: Option<Elem>) -> Location {
    // 1. "Let targetParent be overrideTarget if it is not null; otherwise the
    // current node."
    let target = match override_target {
        Some(e) => e,
        None => current_node(p),
    };
    // 2. "Let referenceChild be null."
    // 3. "If foster parenting is enabled and targetParent is a table, tbody,
    // tfoot, thead, or tr element:"
    let (tp, rc, tp_is_template) = if p.foster && is_table_like(target) {
        // 3.1 "Let lastTemplateOrTable be the last template or table element
        // in the stack of open elements if there is one; otherwise null."
        let i = last_index_where(p.open, p.open.len() as int, |e: Elem| is_html(e, Tag::Template) || is_html(e, Tag::Table));
        if i < 0 {
            // 3.2 "If lastTemplateOrTable is null, then return (the first
            // element in the stack of open elements (the html element),
            // null)." (Step 4 returns it, since it is not a template.)
            (p.open[0].id, None::<NodeId>, false)
        } else if is_html(p.open[i], Tag::Template) {
            // 3.3 "set targetParent to lastTemplateOrTable"
            (p.open[i].id, None, true)
        } else {
            let t = p.open[i].id;
            match p.doc.nodes[t as int].parent {
                // 3.4 "Otherwise, if lastTemplateOrTable's parent is not
                // null, then set targetParent to lastTemplateOrTable's parent
                // and set referenceChild to lastTemplateOrTable."
                Some(par) => (par, Some(t), node_is_template(p.doc, par)),
                // 3.5 "Otherwise, set targetParent to the element immediately
                // above lastTemplateOrTable in the stack of open elements."
                None => (p.open[i - 1].id, None, is_html(p.open[i - 1], Tag::Template)),
            }
        }
    } else {
        (target.id, None, is_html(target, Tag::Template))
    };
    if !tp_is_template {
        // 4. "If targetParent is not a template element, then return
        // (targetParent, referenceChild)."
        Location { parent: tp, child: rc }
    } else {
        // 5. "Let patchInsertionTarget be targetParent's insertion target."
        // Always null: content patching is not modelled (see [`super`]).
        // 6. "If patchInsertionTarget is null, then return (targetParent's
        // template contents, null)." Steps 7 and 8 never apply.
        Location { parent: template_contents(p.doc, tp), child: None }
    }
}

/// §13.2.6.1 "adjusted insertion location" with an optional insertion
/// location.
pub open spec fn adjusted_location(p: Parser, loc: Option<Location>) -> Location {
    // 1. "Let location be insertionLocation if insertionLocation is non-null;
    // otherwise the appropriate place for inserting a node."
    let location = match loc {
        Some(l) => l,
        None => appropriate_place(p, None),
    };
    // 2. "Let (targetParent, refChild) be location."
    match p.redirect {
        // 5. "Return the parser's insertion target redirection
        // map[targetParent]." (4. "Assert: refChild is null.")
        Some((key, frag)) if key == location.parent => Location { parent: frag, child: None },
        // 3. "If the parser's insertion target redirection map[targetParent]
        // does not exist, then return location."
        _ => location,
    }
}

// ---------------------------------------------------------------------
// Creating an element for a token

/// HTML §4.10.17 "form-associated elements": button, fieldset, input,
/// object, output, select, textarea, img (form-associated custom elements
/// need scripting).
pub open spec fn is_form_associated(ns: Namespace, t: Tag) -> bool {
    ns == Namespace::Html && match t {
        Tag::Button | Tag::Fieldset | Tag::Input | Tag::Object | Tag::Output | Tag::Select | Tag::Textarea | Tag::Img => true,
        _ => false,
    }
}

/// HTML §4.10.17 "listed elements": button, fieldset, input, object,
/// output, select, textarea.
pub open spec fn is_listed(ns: Namespace, t: Tag) -> bool {
    ns == Namespace::Html && match t {
        Tag::Button | Tag::Fieldset | Tag::Input | Tag::Object | Tag::Output | Tag::Select | Tag::Textarea => true,
        _ => false,
    }
}

/// The root of `n` within `fuel` steps up (DOM §4.2 "root": "the object
/// itself, if its parent is null, or else it is the root of its parent").
pub open spec fn root_within(doc: Document, n: NodeId, fuel: nat) -> NodeId
    decreases fuel,
{
    if fuel == 0 {
        n
    } else {
        match doc.nodes[n as int].parent {
            None => n,
            Some(par) => root_within(doc, par, (fuel - 1) as nat),
        }
    }
}

/// DOM §4.2 "in the same tree": the two nodes have the same root.
pub open spec fn same_tree(doc: Document, a: NodeId, b: NodeId) -> bool {
    root_within(doc, a, doc.nodes.len()) == root_within(doc, b, doc.nodes.len())
}

/// The token's `encoding` attribute marks an `annotation-xml` element as an
/// HTML integration point (§13.2.6).
pub open spec fn annotation_html(ns: Namespace, t: TagTok) -> bool {
    ns == Namespace::MathMl && t.tag == Tag::AnnotationXml && match attr_value(t.attrs, seq![0x65u32, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67]) {
        // "encoding"
        Some(v) => ascii_ci_eq(v, seq![0x74u32, 0x65, 0x78, 0x74, 0x2f, 0x68, 0x74, 0x6d, 0x6c]) // "text/html"
            || ascii_ci_eq(v, seq![0x61u32, 0x70, 0x70, 0x6c, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x2f, 0x78, 0x68, 0x74, 0x6d, 0x6c, 0x2b, 0x78, 0x6d, 0x6c]), // "application/xhtml+xml"
        None => false,
    }
}

/// "form" (the `form` content attribute's name).
pub open spec fn name_form() -> Seq<u32> {
    seq![0x66u32, 0x6f, 0x72, 0x6d]
}

/// §13.2.6.1 "create an element for a token", given a token, a namespace
/// and an intendedParent (the prefix is always null in the parser's calls).
/// Returns the parser (with the new node, and its template contents if it
/// is a template) and the element.
pub open spec fn create_element_for_token(p: Parser, t: TagTok, ns: Namespace, intended_parent: NodeId) -> (Parser, Elem) {
    // 1., 2.: no speculative parser (not modelled).
    // 3. "Let document be intendedParent's node document." (The arena.)
    // 4. "Let localName be token's tag name."
    // 5. to 7.: the sanitizer configuration is null; sanitizerAction is
    // "Keep".
    // 8. to 14.: "is" and custom element definitions need scripting; the
    // definition is null and willExecuteScript is false (see [`super`]).
    // 21. The form owner (computed from the state before the element
    // exists; nothing in steps 15 to 20 changes it).
    let owner = if is_form_associated(ns, t.tag) && p.form is Some && !parsing_template_contents(p) && p.context is None
        && (!is_listed(ns, t.tag) || !has_attr(t, name_form())) && same_tree(p.doc, intended_parent, p.form->Some_0) {
        // "associate element with the form element pointed to by the form
        // element pointer" (the redirection map has no entry for a form: its
        // only key is the fragment case's root, and the context is null).
        p.form
    } else {
        None
    };
    // 15. "Let element be the result of creating an element given document,
    // localName, namespace, prefix, …" and 17. "For each attribute of
    // token's attributes: … 17.2 Append attribute to element." (The
    // attributes are appended in order to the new element's empty list,
    // which is that list.)
    let (p1, id) = create(
        p,
        NodeKind::Element {
            namespace: Some(ns),
            prefix: None,
            local_name: t.name,
            attributes: t.attrs,
            template_contents: None,
            form_owner: owner,
        },
    );
    // HTML §4.12.3: "When a template element is created, the user agent must
    // … establish the template contents" (`clazel_dom::spec::
    // create_template_contents`).
    let p2 = if ns == Namespace::Html && t.tag == Tag::Template && !p1.stopped {
        if !dom::can_create(p1.doc, 1) {
            stop_parsing(p1)
        } else {
            Parser { doc: dom::create_template_contents(p1.doc, id).0, ..p1 }
        }
    } else {
        p1
    };
    // 16., 18.: custom elements (not modelled). 19.: a parse error. 20.
    // "invoke its reset algorithm": a resettable element's value and
    // checkedness are not part of the DOM model (Phase 6).
    // 22. "Return element."
    (p2, Elem { id, ns, tag: t.tag, name: t.name, annotation_html: annotation_html(ns, t) })
}

/// §13.2.6.1 "insert an element at the adjusted insertion location" with an
/// element and an optional overrideLocation (alreadySanitized is moot: the
/// sanitizer is null).
pub open spec fn insert_element_at(p: Parser, el: NodeId, override_loc: Option<Location>) -> Parser {
    // 1. "Let (targetParent, referenceChild) be the adjusted insertion
    // location given overrideLocation."
    let loc = adjusted_location(p, override_loc);
    let doc = p.doc;
    // 2. "If any of the following are true: element's parent is non-null;
    // element is a host-including inclusive ancestor of targetParent; or
    // targetParent is a Document node that already has an element child,
    // then return."
    if p.stopped || doc.nodes[el as int].parent is Some || dom::is_inclusive_ancestor(doc, el, loc.parent) || (
    doc.nodes[loc.parent as int].kind is Document && has_element_child(doc, loc.parent)) {
        p
    } else {
        // 3.: the sanitizer is null. 4. The assertion ([`dom_insert`]). 5.,
        // 7.: custom element reactions (not modelled).
        // 6. "Insert element into targetParent before referenceChild."
        dom_insert(p, el, loc.parent, loc.child)
    }
}

/// The node has a child that is an element.
pub open spec fn has_element_child(doc: Document, n: NodeId) -> bool {
    exists|i: int| 0 <= i < doc.nodes[n as int].children.len() && dom::valid(doc, #[trigger] doc.nodes[n as int].children[i])
        && doc.nodes[doc.nodes[n as int].children[i] as int].kind is Element
}

/// §13.2.6.1 "insert a foreign element", given a token and a namespace.
/// Returns the parser and the element.
pub open spec fn insert_foreign_element(p: Parser, t: TagTok, ns: Namespace) -> (Parser, Elem) {
    // 1. "Let element be the result of creating an element for the token
    // given token, namespace, and the target parent of the appropriate place
    // for inserting a node."
    let (p1, e) = create_element_for_token(p, t, ns, appropriate_place(p, None).parent);
    // 2. "Insert an element at the adjusted insertion location with
    // element."
    let p2 = insert_element_at(p1, e.id, None);
    // 3. "Push element onto the stack of open elements so that it is the new
    // current node." 4. "Return element."
    (push(p2, e), e)
}

/// §13.2.6.1 "insert an HTML element given a token token: insert a foreign
/// element given token and the HTML namespace."
pub open spec fn insert_html_element(p: Parser, t: TagTok) -> (Parser, Elem) {
    insert_foreign_element(p, t, Namespace::Html)
}

// ---------------------------------------------------------------------
// Attribute adjustments (§13.2.6.1)

/// "definitionurl"
pub open spec fn name_definitionurl() -> Seq<u32> {
    seq![0x64u32, 0x65, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x69, 0x6f, 0x6e, 0x75, 0x72, 0x6c]
}

/// "definitionURL"
pub open spec fn name_definition_url() -> Seq<u32> {
    seq![0x64u32, 0x65, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x69, 0x6f, 0x6e, 0x55, 0x52, 0x4c]
}

/// "adjust MathML attributes for a token": "if the token has an attribute
/// named definitionurl, change its name to definitionURL".
pub open spec fn adjust_mathml_attributes(t: TagTok) -> TagTok {
    TagTok {
        attrs: t.attrs.map_values(
            |a: Attr|
                if a.namespace is None && a.local_name == name_definitionurl() {
                    Attr { local_name: name_definition_url(), ..a }
                } else {
                    a
                },
        ),
        ..t
    }
}

/// "adjust SVG attributes for a token": "for each attribute on the token
/// whose attribute name is one of the ones in the first column of the
/// following table, change the attribute's name to the name given in the
/// corresponding cell in the second column."
pub open spec fn adjust_svg_attributes(t: TagTok) -> TagTok {
    TagTok {
        attrs: t.attrs.map_values(
            |a: Attr|
                if a.namespace is None {
                    Attr { local_name: super::tables::svg_attribute_name(a.local_name), ..a }
                } else {
                    a
                },
        ),
        ..t
    }
}

/// "adjust foreign attributes for a token": "if any of the attributes on
/// the token match the strings given in the first column of the following
/// table, let the attribute be a namespaced attribute, with the prefix …,
/// the local name … and the namespace … given in the corresponding cells".
pub open spec fn adjust_foreign_attributes(t: TagTok) -> TagTok {
    TagTok {
        attrs: t.attrs.map_values(
            |a: Attr|
                if a.namespace is None {
                    match super::tables::foreign_attribute(a.local_name) {
                        Some((prefix, local, ns)) => Attr { namespace: Some(ns), prefix, local_name: local, value: a.value },
                        None => a,
                    }
                } else {
                    a
                },
        ),
        ..t
    }
}

// ---------------------------------------------------------------------
// Inserting characters, comments and processing instructions

/// §13.2.6.1 "insert a character" with the characters `data`.
pub open spec fn insert_characters(p: Parser, data: Seq<u32>) -> Parser {
    // 1. "Let data be the characters passed to the algorithm …"
    // 2. "Let (targetParent, referenceChild) be the adjusted insertion
    // location."
    let loc = adjusted_location(p, None);
    let doc = p.doc;
    if p.stopped || doc.nodes[loc.parent as int].kind is Document {
        // 3. "If targetParent is a Document node, then return."
        p
    } else {
        // 4. "Let previousSibling be referenceChild's previous sibling if
        // referenceChild is non-null; otherwise targetParent's last child."
        let prev = match loc.child {
            Some(c) => dom::previous_sibling(doc, c),
            None => dom::last_child(doc, loc.parent),
        };
        match prev {
            // 5. "If previousSibling is a Text node, then append data to
            // previousSibling's data."
            Some(s) if dom::valid(doc, s) && doc.nodes[s as int].kind is Text => Parser { doc: dom::append_data(doc, s, data), ..p },
            // "Otherwise, let text be the result of creating a text node given
            // targetParent's node document and data, and insert text into
            // targetParent before referenceChild."
            _ => {
                let (p1, text) = create(p, NodeKind::Text { data });
                dom_insert(p1, text, loc.parent, loc.child)
            },
        }
    }
}

/// "insert a character" for one character.
pub open spec fn insert_char(p: Parser, c: u32) -> Parser {
    insert_characters(p, seq![c])
}

/// §13.2.6.1 "insert a comment" with `data` and an optional insertion
/// location.
pub open spec fn insert_comment(p: Parser, data: Seq<u32>, loc: Option<Location>) -> Parser {
    // 1. The sanitizer is null.
    // 2. "Let data be the data given in the comment token being processed."
    // 3. "Let (targetParent, referenceChild) be the adjusted insertion
    // location given insertionLocation."
    let l = adjusted_location(p, loc);
    // 4. "Let comment be the result of creating a comment node given
    // targetParent's node document and data."
    let (p1, c) = create(p, NodeKind::Comment { data });
    // 5. "Insert comment into targetParent before referenceChild."
    dom_insert(p1, c, l.parent, l.child)
}

/// §13.2.6.1 "insert a processing instruction" with target, data and an
/// optional insertion location.
pub open spec fn insert_pi(p: Parser, target: Seq<u32>, data: Seq<u32>, loc: Option<Location>) -> Parser {
    // 1. "Let piTarget be the target given in the processing instruction
    // token being processed." 2. The sanitizer is null. 3. "Let data be the
    // data …"
    // 4. "Let (targetParent, referenceChild) be the adjusted insertion
    // location given insertionLocation."
    let l = adjusted_location(p, loc);
    // 5. "Let pi be the result of creating a processing instruction node
    // given targetParent's node document, piTarget, and data."
    let (p1, n) = create(p, NodeKind::ProcessingInstruction { target, data });
    // 6. "Insert pi into targetParent before referenceChild."
    dom_insert(p1, n, l.parent, l.child)
}

/// The insertion location (the Document object, null).
pub open spec fn document_location() -> Location {
    Location { parent: 0, child: None }
}

// ---------------------------------------------------------------------
// §13.2.6.2 Parsing elements that contain only text

/// §13.2.6.2 "generic raw text element parsing algorithm" (`rawtext`) or
/// "generic RCDATA element parsing algorithm" (`!rawtext`).
pub open spec fn generic_text_parsing(p: Parser, t: TagTok, rawtext: bool) -> Parser {
    // 1. "Insert an HTML element for the token."
    let p1 = insert_html_element(p, t).0;
    // 2. "… switch the tokenizer to the RAWTEXT state; otherwise … to the
    // RCDATA state."
    let st = if rawtext {
        TokenizerState::Rawtext
    } else {
        TokenizerState::Rcdata
    };
    // 3. "Set the original insertion mode to the current insertion mode."
    // 4. "Then, switch the insertion mode to "text"."
    Parser { tokenizer: Some(st), original_mode: p1.mode, mode: Mode::Text, ..p1 }
}

// ---------------------------------------------------------------------
// §13.2.6.3 Closing elements that have implied end tags

/// An element generate implied end tags pops: "a dd element, a dt element,
/// an li element, an optgroup element, an option element, a p element, an
/// rb element, an rp element, an rt element, or an rtc element".
pub open spec fn implied_end_tag(e: Elem) -> bool {
    e.ns == Namespace::Html && match e.tag {
        Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb | Tag::Rp | Tag::Rt | Tag::Rtc => true,
        _ => false,
    }
}

/// "generate implied end tags", excluding HTML elements named `except` if
/// given: "while the current node is [one of them], the UA must pop the
/// current node off the stack of open elements."
pub open spec fn generate_implied_end_tags(p: Parser, except: Option<Tag>) -> Parser {
    pop_while(p, |e: Elem| implied_end_tag(e) && !(except is Some && e.tag == except->Some_0))
}

/// "generate all implied end tags thoroughly": "while the current node is a
/// caption element, a colgroup element, a dd element, a dt element, an li
/// element, an optgroup element, an option element, a p element, an rb
/// element, an rp element, an rt element, an rtc element, a tbody element, a
/// td element, a tfoot element, a th element, a thead element, or a tr
/// element, the UA must pop the current node".
pub open spec fn generate_all_implied_end_tags_thoroughly(p: Parser) -> Parser {
    pop_while(
        p,
        |e: Elem|
            e.ns == Namespace::Html && match e.tag {
                Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb
                | Tag::Rp | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => true,
                _ => false,
            },
    )
}

// ---------------------------------------------------------------------
// §13.2.4.3 reconstruct the active formatting elements

/// Steps 7 to 10 ("Advance", "Create", replace, loop) from the entry at
/// index `i` (the entry step 7 advances to).
pub open spec fn reconstruct_create(p: Parser, i: int) -> Parser
    decreases p.formatting.len() - i,
{
    if i < 0 || i >= p.formatting.len() || p.stopped || !(p.formatting[i] is Entry) {
        p
    } else {
        // 8. "Create: Insert an HTML element for the token for which the
        // element entry was created, to obtain new element."
        let token = p.formatting[i]->Entry_token;
        let (p1, new_element) = insert_html_element(p, token);
        // 9. "Replace the entry for entry in the list with an entry for new
        // element."
        let p2 = if p1.stopped {
            p1
        } else {
            Parser { formatting: p1.formatting.update(i, Fmt::Entry { elem: new_element, token }), ..p1 }
        };
        // 10. "If the entry for new element in the list of active formatting
        // elements is not the last entry in the list, return to the step
        // labeled advance." 7. "Advance: Let entry be the element one later
        // than entry in the list of active formatting elements."
        if i + 1 < p2.formatting.len() && p2.formatting.len() == p.formatting.len() {
            reconstruct_create(p2, i + 1)
        } else {
            p2
        }
    }
}

/// Steps 4 to 6 ("Rewind") from entry index `i`: the index of the first
/// entry to create.
pub open spec fn reconstruct_rewind(p: Parser, i: int) -> int
    decreases i,
{
    if i <= 0 {
        // 4. "Rewind: If there are no entries before entry in the list of
        // active formatting elements, then jump to the step labeled create."
        0
    } else {
        // 5. "Let entry be the entry one earlier than entry in the list of
        // active formatting elements."
        let e = p.formatting[i - 1];
        if !(e is Marker) && !fmt_on_stack(p, e) {
            // 6. "If entry is neither a marker nor an element that is also in
            // the stack of open elements, go to the step labeled rewind."
            reconstruct_rewind(p, i - 1)
        } else {
            // 7. "Advance: Let entry be the element one later than entry".
            i
        }
    }
}

/// §13.2.4.3 "reconstruct the active formatting elements".
pub open spec fn reconstruct_formatting(p: Parser) -> Parser {
    let n = p.formatting.len();
    if n == 0 {
        // 1. "If there are no entries in the list of active formatting
        // elements, then there is nothing to reconstruct; stop this
        // algorithm."
        p
    } else if p.formatting[n - 1] is Marker || fmt_on_stack(p, p.formatting[n - 1]) {
        // 2. "If the last (most recently added) entry … is a marker, or if it
        // is an element that is in the stack of open elements, then there is
        // nothing to reconstruct; stop this algorithm."
        p
    } else {
        // 3. "Let entry be the last (most recently added) element in the
        // list of active formatting elements."
        reconstruct_create(p, reconstruct_rewind(p, n - 1))
    }
}

} // verus!
