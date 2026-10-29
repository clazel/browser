//! W3C HTML 5.2 §8.2.5.4.7: the "in body" insertion mode, with "close a p
//! element" and the adoption agency algorithm. Source and modelling
//! choices: [`super`]. Specific to this section:
//! - The entries for start tags, end tags and the other tokens are disjoint,
//!   so each kind is its own function ([`w3c_in_body_start`],
//!   [`w3c_in_body_end`]), with its entries in the W3C's order; an entry
//!   naming both a start and an end tag (the `template` one) appears in
//!   both.
//! - "An HTML element with the same tag name as the token" is read as the
//!   same [`Tag`] for the entries that list their tag names (as in
//!   [`super::tables`]), and as the same name in "any other end tag", whose
//!   token may have a name with no [`Tag`] of its own (`Tag::Other`).
//! - "Has the tag name subject" (the adoption agency algorithm, step 6) is
//!   the same [`Tag`]: the subject is one of the formatting tags.
//! - "A start tag whose tag name is "select"": the W3C switches to "in
//!   select" or "in select in table", which `Mode` does not have (see
//!   [`super`]). The steps before the switch are transcribed; the insertion
//!   mode is left as it is, and the equivalence lemma excludes the token.
//! - The adoption agency algorithm's "bookmark" is an index of the list of
//!   active formatting elements: the place before the entry now at that
//!   index. Removing an entry before it moves it down by one; it starts at
//!   formatting element's index (the place formatting element occupies, so
//!   that removing formatting element leaves it between the same two
//!   neighbours), and step 14.8 puts it after the new element.
//! - Its "node" is tracked by its index on the stack of open elements: the
//!   element "immediately above node" is at the index below it whether node
//!   is still on the stack (step 14.7 replaces the entry in place) or was
//!   removed (step 14.6).
//! - Once the parser has stopped (the node limit), the remaining steps
//!   change nothing (see [`super`]): the adoption agency algorithm's loops
//!   end there, and the `form` and `a` start tag entries neither set the
//!   form element pointer nor remove the old `a` element.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Names

/// "p"
pub open spec fn w3c_name_p() -> Seq<u32> {
    seq![0x70u32]
}

/// "img"
pub open spec fn w3c_name_img() -> Seq<u32> {
    seq![0x69u32, 0x6d, 0x67]
}

/// "br"
pub open spec fn w3c_name_br() -> Seq<u32> {
    seq![0x62u32, 0x72]
}

/// "type"
pub open spec fn w3c_name_type() -> Seq<u32> {
    seq![0x74u32, 0x79, 0x70, 0x65]
}

/// "hidden"
pub open spec fn w3c_hidden() -> Seq<u32> {
    seq![0x68u32, 0x69, 0x64, 0x64, 0x65, 0x6e]
}

// ---------------------------------------------------------------------
// Shared steps

/// "Close a p element": "Generate implied end tags, except for p elements.
/// If the current node is not a p element, then this is a parse error. Pop
/// elements from the stack of open elements until a p element has been
/// popped from the stack."
pub open spec fn w3c_close_p(p: Parser) -> Parser {
    pop_until_popped(generate_implied_end_tags(p, Some(Tag::P)), Tag::P)
}

/// "If the stack of open elements has a p element in button scope, then
/// close a p element."
pub open spec fn w3c_close_p_in_button_scope(p: Parser) -> Parser {
    if has_in_scope(p, Tag::P, Scope::Button) {
        w3c_close_p(p)
    } else {
        p
    }
}

/// "Set the frameset-ok flag to "not ok"."
pub open spec fn w3c_frameset_not_ok(p: Parser) -> Parser {
    Parser { frameset_ok: false, ..p }
}

/// "Insert an HTML element for the token. Immediately pop the current node
/// off the stack of open elements. Acknowledge the token's self-closing
/// flag, if it is set."
pub open spec fn w3c_insert_and_pop(p: Parser, tt: TagTok) -> Parser {
    pop(insert_html_element(p, tt).0)
}

/// "Insert an HTML element for the token. Push onto the list of active
/// formatting elements that element."
pub open spec fn w3c_insert_formatting(p: Parser, tt: TagTok) -> Parser {
    let (q, e) = insert_html_element(p, tt);
    push_formatting(q, e, tt)
}

/// "For each attribute on the token, check to see if the attribute is
/// already present on" the element `el`; "if it is not, add the attribute
/// and its corresponding value to that element": from the token's
/// attribute `i` on.
pub open spec fn w3c_add_missing_attributes(p: Parser, el: NodeId, attrs: Seq<Attr>, i: int) -> Parser
    decreases attrs.len() - i,
{
    if i < 0 || i >= attrs.len() {
        p
    } else {
        let present = match p.doc.nodes[el as int].kind {
            NodeKind::Element { attributes, .. } => attr_value(attributes, attrs[i].local_name) is Some,
            _ => true,
        };
        let q = if p.stopped || !dom::valid(p.doc, el) || present {
            p
        } else {
            Parser { doc: dom::append_attribute(p.doc, el, attrs[i]), ..p }
        };
        w3c_add_missing_attributes(q, el, attrs, i + 1)
    }
}

/// "Pop all the nodes from the bottom of the stack of open elements, from
/// the current node up to, but not including, the root html element."
pub open spec fn w3c_pop_to_root(p: Parser) -> Parser
    decreases p.open.len(),
{
    if p.open.len() <= 1 {
        p
    } else {
        w3c_pop_to_root(pop(p))
    }
}

/// The element is "an address, div, or p element".
pub open spec fn w3c_address_div_p(e: Elem) -> bool {
    is_html(e, Tag::Address) || is_html(e, Tag::Div) || is_html(e, Tag::P)
}

/// The "li" entry's steps 3 to 5 ("Loop" … "Otherwise, set node to the
/// previous entry in the stack of open elements and return to the step
/// labeled Loop"), with node the entry at index `i`: the parser at the step
/// labeled "Done".
pub open spec fn w3c_li_loop(p: Parser, i: int) -> Parser
    decreases i + 1,
{
    if i < 0 || i >= p.open.len() {
        // Never: the loop ends at the html element, which is special.
        p
    } else if is_html(p.open[i], Tag::Li) {
        // 3. "Loop: If node is an li element, then run these substeps:
        // Generate implied end tags, except for li elements. If the current
        // node is not an li element, then this is a parse error. Pop
        // elements from the stack of open elements until an li element has
        // been popped from the stack. Jump to the step labeled Done below."
        pop_until_popped(generate_implied_end_tags(p, Some(Tag::Li)), Tag::Li)
    } else if is_special(p.open[i]) && !w3c_address_div_p(p.open[i]) {
        // 4. "If node is in the special category, but is not an address,
        // div, or p element, then jump to the step labeled Done below."
        p
    } else {
        // 5. "Otherwise, set node to the previous entry in the stack of open
        // elements and return to the step labeled Loop."
        w3c_li_loop(p, i - 1)
    }
}

/// The "dd", "dt" entry's steps 3 to 6, with node the entry at index `i`:
/// the parser at the step labeled "Done".
pub open spec fn w3c_dd_dt_loop(p: Parser, i: int) -> Parser
    decreases i + 1,
{
    if i < 0 || i >= p.open.len() {
        // Never: the loop ends at the html element, which is special.
        p
    } else if is_html(p.open[i], Tag::Dd) {
        // 3. "Loop: If node is a dd element, then run these substeps:
        // Generate implied end tags, except for dd elements. If the current
        // node is not a dd element, then this is a parse error. Pop elements
        // from the stack of open elements until a dd element has been popped
        // from the stack. Jump to the step labeled Done below."
        pop_until_popped(generate_implied_end_tags(p, Some(Tag::Dd)), Tag::Dd)
    } else if is_html(p.open[i], Tag::Dt) {
        // 4. "If node is a dt element, then run these substeps: …" (as for
        // dd)
        pop_until_popped(generate_implied_end_tags(p, Some(Tag::Dt)), Tag::Dt)
    } else if is_special(p.open[i]) && !w3c_address_div_p(p.open[i]) {
        // 5. "If node is in the special category, but is not an address,
        // div, or p element, then jump to the step labeled Done below."
        p
    } else {
        // 6. "Otherwise, set node to the previous entry in the stack of open
        // elements and return to the step labeled Loop."
        w3c_dd_dt_loop(p, i - 1)
    }
}

/// "Any other end tag", steps 2 to 4 with node the entry at index `i`.
pub open spec fn w3c_any_other_end_tag_loop(p: Parser, tt: TagTok, i: int) -> Parser
    decreases i + 1,
{
    if i < 0 || i >= p.open.len() {
        // Never: the loop ends at the html element, which is special.
        p
    } else if p.open[i].ns == Namespace::Html && p.open[i].name == tt.name {
        // 2. "Loop: If node is an HTML element with the same tag name as the
        // token, then: Generate implied end tags, except for HTML elements
        // with the same tag name as the token. If node is not the current
        // node, then this is a parse error. Pop all the nodes from the
        // current node up to node, including node, then stop these steps."
        pop_until_node_popped(generate_implied_end_tags(p, Some(tt.tag)), p.open[i].id)
    } else if is_special(p.open[i]) {
        // 3. "Otherwise, if node is in the special category, then this is a
        // parse error; ignore the token, and abort these steps."
        p
    } else {
        // 4. "Set node to the previous entry in the stack of open elements."
        // 5. "Return to the step labeled Loop."
        w3c_any_other_end_tag_loop(p, tt, i - 1)
    }
}

/// "Any other end tag": "1. Initialize node to be the current node (the
/// bottommost node of the stack)." Then [`w3c_any_other_end_tag_loop`].
pub open spec fn w3c_any_other_end_tag(p: Parser, tt: TagTok) -> Parser {
    w3c_any_other_end_tag_loop(p, tt, p.open.len() - 1)
}

// ---------------------------------------------------------------------
// The adoption agency algorithm
// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#adoption-agency-algorithm>)

/// Step 6: the index of "the last element in the list of active formatting
/// elements that is between the end of the list and the last marker in the
/// list, if any, or the start of the list otherwise, and has the tag name
/// subject", among the first `i` entries; -1 if there is none.
pub open spec fn w3c_aa_find(f: Seq<Fmt>, i: int, subject: Tag) -> int
    decreases i,
{
    if i <= 0 || i > f.len() {
        -1
    } else if f[i - 1] is Marker {
        -1
    } else if f[i - 1]->Entry_elem.tag == subject {
        i - 1
    } else {
        w3c_aa_find(f, i - 1, subject)
    }
}

/// Step 10: the index of "the topmost node in the stack of open elements
/// that is lower in the stack than formatting element, and is an element
/// in the special category", searching from index `i` down the stack; -1
/// if there is none.
pub open spec fn w3c_furthest_block(open: Seq<Elem>, i: int) -> int
    decreases open.len() - i,
{
    if i < 0 || i >= open.len() {
        -1
    } else if is_special(open[i]) {
        i
    } else {
        w3c_furthest_block(open, i + 1)
    }
}

/// The index of the element `id`'s entry in the list of active formatting
/// elements (-1 if none).
pub open spec fn w3c_fmt_index(p: Parser, id: NodeId) -> int {
    fmt_index_of(p.formatting, p.formatting.len() as int, id)
}

/// Remove entry `k` from the list of active formatting elements.
pub open spec fn w3c_fmt_remove(p: Parser, k: int) -> Parser {
    Parser { formatting: p.formatting.remove(k), ..p }
}

/// The bookmark (see the module comment) after removing the list's entry
/// `k`.
pub open spec fn w3c_bookmark_after_remove(bm: int, k: int) -> int {
    if k < bm {
        bm - 1
    } else {
        bm
    }
}

/// Step 14, from step 14.2: the inner loop, with node the stack entry at
/// index `ni` (see the module comment), last node `last`, the inner loop
/// counter `counter` and the bookmark `bm`. Returns the parser, last node
/// and the bookmark at step 15.
pub open spec fn w3c_aa_inner(
    p: Parser,
    fe: Elem,
    ca: Elem,
    fb: Elem,
    ni: int,
    last: Elem,
    counter: nat,
    bm: int,
) -> (Parser, Elem, int)
    decreases ni,
{
    if p.stopped || ni <= 0 || ni > p.open.len() {
        // Never with a running parser: formatting element is above node.
        (p, last, bm)
    } else {
        // 2. "Inner loop: Increment inner loop counter by one."
        let c = counter + 1;
        // 3. "Let node be the element immediately above node in the stack of
        // open elements, or if node is no longer in the stack of open
        // elements (e.g., because it got removed by this algorithm), the
        // element that was immediately above node in the stack of open
        // elements before node was removed."
        let i = ni - 1;
        let node = p.open[i];
        if node.id == fe.id {
            // 4. "If node is formatting element, then go to the next step in
            // the overall algorithm."
            (p, last, bm)
        } else {
            // 5. "If inner loop counter is greater than three and node is in
            // the list of active formatting elements, then remove node from
            // the list of active formatting elements."
            let k = w3c_fmt_index(p, node.id);
            let p1 = if c > 3 && k >= 0 {
                w3c_fmt_remove(p, k)
            } else {
                p
            };
            let bm1 = if c > 3 && k >= 0 {
                w3c_bookmark_after_remove(bm, k)
            } else {
                bm
            };
            let k1 = w3c_fmt_index(p1, node.id);
            if k1 < 0 {
                // 6. "If node is not in the list of active formatting
                // elements, then remove node from the stack of open elements
                // and then go back to the step labeled Inner loop."
                w3c_aa_inner(remove_open_at(p1, i), fe, ca, fb, i, last, c, bm1)
            } else {
                // 7. "Create an element for the token for which the element
                // node was created, in the HTML namespace, with common
                // ancestor as the intended parent;
                let token = p1.formatting[k1]->Entry_token;
                let (p2, new_el) = create_element_for_token(p1, token, Namespace::Html, ca.id);
                if p2.stopped {
                    (p2, last, bm1)
                } else {
                    // replace the entry for node in the list of active
                    // formatting elements with an entry for the new element,
                    // replace the entry for node in the stack of open
                    // elements with an entry for the new element, and let
                    // node be the new element."
                    let p3 = Parser {
                        formatting: p2.formatting.update(k1, Fmt::Entry { elem: new_el, token }),
                        open: p2.open.update(i, new_el),
                        ..p2
                    };
                    // 8. "If last node is furthest block, then move the
                    // aforementioned bookmark to be immediately after the new
                    // node in the list of active formatting elements."
                    let bm2 = if last.id == fb.id {
                        k1 + 1
                    } else {
                        bm1
                    };
                    // 9. "Insert last node into node, first removing it from
                    // its previous parent node if any."
                    let p4 = dom_insert(p3, last.id, new_el.id, None);
                    // 10. "Let last node be node." 11. "Return to the step
                    // labeled Inner loop."
                    w3c_aa_inner(p4, fe, ca, fb, i, new_el, c, bm2)
                }
            }
        }
    }
}

/// Steps 15 to 20, after the inner loop, for formatting element `fe` (whose
/// entry in the list was created for `fe_token`), furthest block `fb` and
/// common ancestor `ca`, with the parser, last node and bookmark the inner
/// loop hands over.
pub open spec fn w3c_aa_after_inner(p: Parser, fe: Elem, fe_token: TagTok, ca: Elem, fb: Elem, last: Elem, bm: int) -> Parser {
    // 15. "Insert whatever last node ended up being in the previous step at
    // the appropriate place for inserting a node, but using common ancestor
    // as the override target."
    let loc = appropriate_place(p, Some(ca));
    let p1 = dom_insert(p, last.id, loc.parent, loc.child);
    // 16. "Create an element for the token for which formatting element was
    // created, in the HTML namespace, with furthest block as the intended
    // parent."
    let (p2, new_el) = create_element_for_token(p1, fe_token, Namespace::Html, fb.id);
    if p2.stopped {
        p2
    } else {
        // 17. "Take all of the child nodes of furthest block and append them
        // to the element created in the last step."
        let p3 = if dom::valid(p2.doc, fb.id) && dom::valid(p2.doc, new_el.id) {
            Parser { doc: dom::reparent_children(p2.doc, fb.id, new_el.id), ..p2 }
        } else {
            p2
        };
        // 18. "Append that new element to furthest block."
        let p4 = dom_insert(p3, new_el.id, fb.id, None);
        // 19. "Remove formatting element from the list of active formatting
        // elements, and insert the new element into the list of active
        // formatting elements at the position of the aforementioned
        // bookmark."
        let k = w3c_fmt_index(p4, fe.id);
        let bm1 = w3c_bookmark_after_remove(bm, k);
        let f1 = p4.formatting.remove(k);
        let p5 = Parser { formatting: f1.insert(bm1, Fmt::Entry { elem: new_el, token: fe_token }), ..p4 };
        // 20. "Remove formatting element from the stack of open elements, and
        // insert the new element into the stack of open elements immediately
        // below the position of furthest block in that stack."
        let p6 = remove_open_at(p5, open_index_of(p5, fe.id));
        Parser { open: p6.open.insert(open_index_of(p6, fb.id) + 1, new_el), ..p6 }
    }
}

/// Steps 4 to 21: the outer loop, with the outer loop counter `counter`,
/// for the token `tt` (subject is its tag name).
pub open spec fn w3c_aa_outer(p: Parser, tt: TagTok, counter: nat) -> Parser
    decreases 8 - counter,
{
    if counter >= 8 || p.stopped {
        // 4. "Outer loop: If outer loop counter is greater than or equal to
        // eight, then abort these steps."
        p
    } else {
        // 5. "Increment outer loop counter by one."
        let c = counter + 1;
        // 6. "Let formatting element be the last element in the list of
        // active formatting elements that: is between the end of the list and
        // the last marker in the list, if any, or the start of the list
        // otherwise, and has the tag name subject."
        let k = w3c_aa_find(p.formatting, p.formatting.len() as int, tt.tag);
        if k < 0 {
            // "If there is no such element, then abort these steps and
            // instead act as described in the "any other end tag" entry
            // above."
            w3c_any_other_end_tag(p, tt)
        } else {
            let fe = p.formatting[k]->Entry_elem;
            let fe_token = p.formatting[k]->Entry_token;
            let fi = open_index_of(p, fe.id);
            if fi < 0 {
                // 7. "If formatting element is not in the stack of open
                // elements, then this is a parse error; remove the element
                // from the list, and abort these steps."
                w3c_fmt_remove(p, k)
            } else if !has_node_in_scope(p, fe.id, Scope::Default) {
                // 8. "If formatting element is in the stack of open elements,
                // but the element is not in scope, then this is a parse
                // error; abort these steps."
                p
            } else {
                // 9. "If formatting element is not the current node, this is a
                // parse error. (But do not abort these steps.)"
                // 10. "Let furthest block be the topmost node in the stack of
                // open elements that is lower in the stack than formatting
                // element, and is an element in the special category. There
                // might not be one."
                let b = w3c_furthest_block(p.open, fi + 1);
                if b < 0 {
                    // 11. "If there is no furthest block, then the UA must
                    // first pop all the nodes from the bottom of the stack of
                    // open elements, from the current node up to and including
                    // formatting element, then remove formatting element from
                    // the list of active formatting elements, and finally
                    // abort these steps."
                    let q = pop_until_node_popped(p, fe.id);
                    w3c_fmt_remove(q, w3c_fmt_index(q, fe.id))
                } else {
                    let fb = p.open[b];
                    // 12. "Let common ancestor be the element immediately above
                    // formatting element in the stack of open elements."
                    let ca = p.open[fi - 1];
                    // 13. "Let a bookmark note the position of formatting
                    // element in the list of active formatting elements
                    // relative to the elements on either side of it in the
                    // list."
                    let bm = k;
                    // 14. "Let node and last node be furthest block." 14.1 "Let
                    // inner loop counter be zero."
                    let (p1, last, bm1) = w3c_aa_inner(p, fe, ca, fb, b, fb, 0, bm);
                    // 15. to 20.
                    let p2 = w3c_aa_after_inner(p1, fe, fe_token, ca, fb, last, bm1);
                    // 21. "Jump back to the step labeled Outer loop."
                    w3c_aa_outer(p2, tt, c)
                }
            }
        }
    }
}

/// The adoption agency algorithm for the token `tt`.
pub open spec fn w3c_adoption_agency(p: Parser, tt: TagTok) -> Parser {
    // 1. "Let subject be token's tag name."
    // 2. "If the current node is an HTML element whose tag name is subject,
    // and the current node is not in the list of active formatting
    // elements, then pop the current node off the stack of open elements,
    // and abort these steps."
    if is_html(current_node(p), tt.tag) && !in_formatting(p, current_node(p).id) {
        pop(p)
    } else {
        // 3. "Let outer loop counter be zero."
        w3c_aa_outer(p, tt, 0)
    }
}

// ---------------------------------------------------------------------
// The entries

/// The entries for a character token.
pub open spec fn w3c_in_body_char(p: Parser, c: u32) -> Outcome {
    if c == 0 {
        // "A character token that is U+0000 NULL": "Parse error."
        Outcome::Done(p)
    } else if w3c_space_char(Tok::Char(c)) {
        // "A character token that is one of U+0009 …": "Reconstruct the
        // active formatting elements, if any. Insert the token's
        // character."
        Outcome::Done(insert_char(reconstruct_formatting(p), c))
    } else {
        // "Any other character token": "Reconstruct the active formatting
        // elements, if any. Insert the token's character. Set the
        // frameset-ok flag to "not ok"."
        Outcome::Done(w3c_frameset_not_ok(insert_char(reconstruct_formatting(p), c)))
    }
}

/// The tags of "A start tag whose tag name is one of: "address",
/// "article", "aside", "blockquote", "center", "details", "dialog",
/// "dir", "div", "dl", "fieldset", "figcaption", "figure", "footer",
/// "header", "main", "nav", "ol", "p", "section", "summary", "ul"".
pub open spec fn w3c_block_start_tag(g: Tag) -> bool {
    g == Tag::Address || g == Tag::Article || g == Tag::Aside || g == Tag::Blockquote || g == Tag::Center || g == Tag::Details
        || g == Tag::Dialog || g == Tag::Dir || g == Tag::Div || g == Tag::Dl || g == Tag::Fieldset || g == Tag::Figcaption || g
        == Tag::Figure || g == Tag::Footer || g == Tag::Header || g == Tag::Main || g == Tag::Nav || g == Tag::Ol || g == Tag::P
        || g == Tag::Section || g == Tag::Summary || g == Tag::Ul
}

/// "h1", "h2", "h3", "h4", "h5", "h6"
pub open spec fn w3c_heading_tag(g: Tag) -> bool {
    g == Tag::H1 || g == Tag::H2 || g == Tag::H3 || g == Tag::H4 || g == Tag::H5 || g == Tag::H6
}

/// "b", "big", "code", "em", "font", "i", "s", "small", "strike",
/// "strong", "tt", "u"
pub open spec fn w3c_formatting_start_tag(g: Tag) -> bool {
    g == Tag::B || g == Tag::Big || g == Tag::Code || g == Tag::Em || g == Tag::Font || g == Tag::I || g == Tag::S || g
        == Tag::Small || g == Tag::Strike || g == Tag::Strong || g == Tag::Tt || g == Tag::U
}

/// The input token has "an attribute with the name "type"" whose value is
/// "an ASCII case-insensitive match for the string "hidden"".
pub open spec fn w3c_input_hidden(tt: TagTok) -> bool {
    match attr_value(tt.attrs, w3c_name_type()) {
        Some(v) => ascii_ci_eq(v, w3c_hidden()),
        None => false,
    }
}

/// The entries for a start tag token, in the W3C's order.
pub open spec fn w3c_in_body_start(env: EncFns, p: Parser, tt: TagTok) -> Outcome {
    let g = tt.tag;
    if g == Tag::Html {
        // "A start tag whose tag name is "html"": "Parse error."
        if open_has_html(p, Tag::Template) {
            // "If there is a template element on the stack of open elements,
            // then ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, for each attribute on the token, check to see if the
            // attribute is already present on the top element of the stack of
            // open elements. If it is not, add the attribute and its
            // corresponding value to that element."
            Outcome::Done(w3c_add_missing_attributes(p, p.open[0].id, tt.attrs, 0))
        }
    } else if g == Tag::Base || g == Tag::Basefont || g == Tag::Bgsound || g == Tag::Link || g == Tag::Meta || g == Tag::Noframes
        || g == Tag::Script || g == Tag::Style || g == Tag::Template || g == Tag::Title {
        // "A start tag whose tag name is one of: "base", "basefont",
        // "bgsound", "link", "meta", "noframes", "script", "style",
        // "template", "title"": "Process the token using the rules for the
        // "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, Tok::Start(tt))
    } else if g == Tag::Body {
        // "A start tag whose tag name is "body"": "Parse error."
        if p.open.len() < 2 || !is_html(p.open[1], Tag::Body) || open_has_html(p, Tag::Template) {
            // "If the second element on the stack of open elements is not a
            // body element, if the stack of open elements has only one node on
            // it, or if there is a template element on the stack of open
            // elements, then ignore the token. (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise, set the frameset-ok flag to "not ok"; then, for each
            // attribute on the token, check to see if the attribute is already
            // present on the body element (the second element) on the stack
            // of open elements, and if it is not, add the attribute and its
            // corresponding value to that element."
            Outcome::Done(w3c_add_missing_attributes(w3c_frameset_not_ok(p), p.open[1].id, tt.attrs, 0))
        }
    } else if g == Tag::Frameset {
        // "A start tag whose tag name is "frameset"": "Parse error."
        if p.open.len() < 2 || !is_html(p.open[1], Tag::Body) {
            // "If the stack of open elements has only one node on it, or if
            // the second element on the stack of open elements is not a body
            // element, then ignore the token. (fragment case)"
            Outcome::Done(p)
        } else if !p.frameset_ok {
            // "If the frameset-ok flag is set to "not ok", ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run the following steps:"
            // 1. "Remove the second element on the stack of open elements from
            // its parent node, if it has one."
            let p1 = dom_remove(p, p.open[1].id);
            // 2. "Pop all the nodes from the bottom of the stack of open
            // elements, from the current node up to, but not including, the
            // root html element."
            let p2 = w3c_pop_to_root(p1);
            // 3. "Insert an HTML element for the token."
            let p3 = insert_html_element(p2, tt).0;
            // 4. "Switch the insertion mode to "in frameset"."
            Outcome::Done(Parser { mode: Mode::InFrameset, ..p3 })
        }
    } else if w3c_block_start_tag(g) {
        // "A start tag whose tag name is one of: "address", …, "ul"": "If the
        // stack of open elements has a p element in button scope, then close a
        // p element. Insert an HTML element for the token."
        Outcome::Done(insert_html_element(w3c_close_p_in_button_scope(p), tt).0)
    } else if w3c_heading_tag(g) {
        // "A start tag whose tag name is one of: "h1", "h2", "h3", "h4",
        // "h5", "h6"": "If the stack of open elements has a p element in
        // button scope, then close a p element."
        let p1 = w3c_close_p_in_button_scope(p);
        // "If the current node is an HTML element whose tag name is one of
        // "h1", "h2", "h3", "h4", "h5", or "h6", then this is a parse error;
        // pop the current node off the stack of open elements."
        let p2 = if current_node(p1).ns == Namespace::Html && w3c_heading_tag(current_node(p1).tag) {
            pop(p1)
        } else {
            p1
        };
        // "Insert an HTML element for the token."
        Outcome::Done(insert_html_element(p2, tt).0)
    } else if g == Tag::Pre || g == Tag::Listing {
        // "A start tag whose tag name is one of: "pre", "listing"": "If the
        // stack of open elements has a p element in button scope, then close
        // a p element. Insert an HTML element for the token."
        let p1 = insert_html_element(w3c_close_p_in_button_scope(p), tt).0;
        // "If the next token is a U+000A LINE FEED (LF) character token, then
        // ignore that token and move on to the next one." "Set the
        // frameset-ok flag to "not ok"."
        Outcome::Done(w3c_frameset_not_ok(Parser { skip_lf: true, ..p1 }))
    } else if g == Tag::Form {
        // "A start tag whose tag name is "form"":
        if p.form is Some && !open_has_html(p, Tag::Template) {
            // "If the form element pointer is not null, and there is no
            // template element on the stack of open elements, then this is a
            // parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise: If the stack of open elements has a p element in
            // button scope, then close a p element. Insert an HTML element for
            // the token, and, if there is no template element on the stack of
            // open elements, set the form element pointer to point to the
            // element created."
            // (The stack the check reads is the one the element is inserted
            // into; the new element is a form, not a template.)
            let p1 = w3c_close_p_in_button_scope(p);
            let (p2, e) = insert_html_element(p1, tt);
            if !open_has_html(p1, Tag::Template) && !p2.stopped {
                Outcome::Done(Parser { form: Some(e.id), ..p2 })
            } else {
                Outcome::Done(p2)
            }
        }
    } else if g == Tag::Li {
        // "A start tag whose tag name is "li"": 1. "Set the frameset-ok flag
        // to "not ok"." 2. "Initialize node to be the current node (the
        // bottommost node of the stack)." 3. to 5.: the loop.
        let p1 = w3c_frameset_not_ok(p);
        let p2 = w3c_li_loop(p1, p1.open.len() - 1);
        // 6. "Done: If the stack of open elements has a p element in button
        // scope, then close a p element." 7. "Finally, insert an HTML element
        // for the token."
        Outcome::Done(insert_html_element(w3c_close_p_in_button_scope(p2), tt).0)
    } else if g == Tag::Dd || g == Tag::Dt {
        // "A start tag whose tag name is one of: "dd", "dt"": 1. "Set the
        // frameset-ok flag to "not ok"." 2. "Initialize node to be the current
        // node (the bottommost node of the stack)." 3. to 6.: the loop.
        let p1 = w3c_frameset_not_ok(p);
        let p2 = w3c_dd_dt_loop(p1, p1.open.len() - 1);
        // 7. "Done: If the stack of open elements has a p element in button
        // scope, then close a p element." 8. "Finally, insert an HTML element
        // for the token."
        Outcome::Done(insert_html_element(w3c_close_p_in_button_scope(p2), tt).0)
    } else if g == Tag::Plaintext {
        // "A start tag whose tag name is "plaintext"": "If the stack of open
        // elements has a p element in button scope, then close a p element.
        // Insert an HTML element for the token. Switch the tokenizer to the
        // PLAINTEXT state."
        let p1 = insert_html_element(w3c_close_p_in_button_scope(p), tt).0;
        Outcome::Done(Parser { tokenizer: Some(TokenizerState::Plaintext), ..p1 })
    } else if g == Tag::Button {
        // "A start tag whose tag name is "button"":
        // 1. "If the stack of open elements has a button element in scope,
        // then run these substeps: Parse error. Generate implied end tags.
        // Pop elements from the stack of open elements until a button element
        // has been popped from the stack."
        let p1 = if has_in_scope(p, Tag::Button, Scope::Default) {
            pop_until_popped(generate_implied_end_tags(p, None), Tag::Button)
        } else {
            p
        };
        // 2. "Reconstruct the active formatting elements, if any." 3. "Insert
        // an HTML element for the token." 4. "Set the frameset-ok flag to
        // "not ok"."
        Outcome::Done(w3c_frameset_not_ok(insert_html_element(reconstruct_formatting(p1), tt).0))
    } else if g == Tag::A {
        // "A start tag whose tag name is "a"": "If the list of active
        // formatting elements contains an a element between the end of the
        // list and the last marker on the list (or the start of the list if
        // there is no marker on the list), then this is a parse error; run the
        // adoption agency algorithm for the token, then remove that element
        // from the list of active formatting elements and the stack of open
        // elements if the adoption agency algorithm didn't already remove it
        // (it might not have if the element is not in table scope)."
        let k = w3c_aa_find(p.formatting, p.formatting.len() as int, Tag::A);
        let p1 = if k >= 0 {
            let a = p.formatting[k]->Entry_elem;
            let q = w3c_adoption_agency(p, tt);
            if q.stopped {
                q
            } else {
                let kq = w3c_fmt_index(q, a.id);
                let q1 = if kq >= 0 {
                    w3c_fmt_remove(q, kq)
                } else {
                    q
                };
                let iq = open_index_of(q1, a.id);
                if iq >= 0 {
                    remove_open_at(q1, iq)
                } else {
                    q1
                }
            }
        } else {
            p
        };
        // "Reconstruct the active formatting elements, if any. Insert an HTML
        // element for the token. Push onto the list of active formatting
        // elements that element."
        Outcome::Done(w3c_insert_formatting(reconstruct_formatting(p1), tt))
    } else if w3c_formatting_start_tag(g) {
        // "A start tag whose tag name is one of: "b", "big", "code", "em",
        // "font", "i", "s", "small", "strike", "strong", "tt", "u"":
        // "Reconstruct the active formatting elements, if any. Insert an HTML
        // element for the token. Push onto the list of active formatting
        // elements that element."
        Outcome::Done(w3c_insert_formatting(reconstruct_formatting(p), tt))
    } else if g == Tag::Nobr {
        // "A start tag whose tag name is "nobr"": "Reconstruct the active
        // formatting elements, if any."
        let p1 = reconstruct_formatting(p);
        // "If the stack of open elements has a nobr element in scope, then
        // this is a parse error; run the adoption agency algorithm for the
        // token, then once again Reconstruct the active formatting elements,
        // if any."
        let p2 = if has_in_scope(p1, Tag::Nobr, Scope::Default) {
            reconstruct_formatting(w3c_adoption_agency(p1, tt))
        } else {
            p1
        };
        // "Insert an HTML element for the token. Push onto the list of active
        // formatting elements that element."
        Outcome::Done(w3c_insert_formatting(p2, tt))
    } else if g == Tag::Applet || g == Tag::Marquee || g == Tag::Object {
        // "A start tag whose tag name is one of: "applet", "marquee",
        // "object"": "Reconstruct the active formatting elements, if any.
        // Insert an HTML element for the token. Insert a marker at the end of
        // the list of active formatting elements. Set the frameset-ok flag to
        // "not ok"."
        Outcome::Done(w3c_frameset_not_ok(push_marker(insert_html_element(reconstruct_formatting(p), tt).0)))
    } else if g == Tag::Table {
        // "A start tag whose tag name is "table"": "If the Document is not
        // set to quirks mode, and the stack of open elements has a p element
        // in button scope, then close a p element."
        let p1 = if !(p.doc.nodes[0].kind->Document_mode == DocumentMode::Quirks) && has_in_scope(p, Tag::P, Scope::Button) {
            w3c_close_p(p)
        } else {
            p
        };
        // "Insert an HTML element for the token. Set the frameset-ok flag to
        // "not ok". Switch the insertion mode to "in table"."
        let p2 = insert_html_element(p1, tt).0;
        Outcome::Done(Parser { frameset_ok: false, mode: Mode::InTable, ..p2 })
    } else if g == Tag::Area || g == Tag::Br || g == Tag::Embed || g == Tag::Img || g == Tag::Wbr {
        // "A start tag whose tag name is one of: "area", "br", "embed", "img",
        // "wbr"": "Reconstruct the active formatting elements, if any. Insert
        // an HTML element for the token. Immediately pop the current node off
        // the stack of open elements. Acknowledge the token's self-closing
        // flag, if it is set. Set the frameset-ok flag to "not ok"."
        Outcome::Done(w3c_frameset_not_ok(w3c_insert_and_pop(reconstruct_formatting(p), tt)))
    } else if g == Tag::Input {
        // "A start tag whose tag name is "input"": "Reconstruct the active
        // formatting elements, if any. Insert an HTML element for the token.
        // Immediately pop the current node off the stack of open elements.
        // Acknowledge the token's self-closing flag, if it is set."
        let p1 = w3c_insert_and_pop(reconstruct_formatting(p), tt);
        if !w3c_input_hidden(tt) {
            // "If the token does not have an attribute with the name "type",
            // or if it does, but that attribute's value is not an ASCII
            // case-insensitive match for the string "hidden", then: set the
            // frameset-ok flag to "not ok"."
            Outcome::Done(w3c_frameset_not_ok(p1))
        } else {
            Outcome::Done(p1)
        }
    } else if g == Tag::Param || g == Tag::Source || g == Tag::Track {
        // "A start tag whose tag name is one of: "param", "source", "track"":
        // "Insert an HTML element for the token. Immediately pop the current
        // node off the stack of open elements. Acknowledge the token's
        // self-closing flag, if it is set."
        Outcome::Done(w3c_insert_and_pop(p, tt))
    } else if g == Tag::Hr {
        // "A start tag whose tag name is "hr"": "If the stack of open elements
        // has a p element in button scope, then close a p element. Insert an
        // HTML element for the token. Immediately pop the current node off the
        // stack of open elements. Acknowledge the token's self-closing flag,
        // if it is set. Set the frameset-ok flag to "not ok"."
        Outcome::Done(w3c_frameset_not_ok(w3c_insert_and_pop(w3c_close_p_in_button_scope(p), tt)))
    } else if g == Tag::Image {
        // "A start tag whose tag name is "image"": "Parse error. Change the
        // token's tag name to "img" and reprocess it. (Don't ask.)"
        Outcome::Reprocess(p, Tok::Start(TagTok { name: w3c_name_img(), tag: tag_of(w3c_name_img()), ..tt }))
    } else if g == Tag::Textarea {
        // "A start tag whose tag name is "textarea"": 1. "Insert an HTML
        // element for the token."
        let p1 = insert_html_element(p, tt).0;
        // 2. "If the next token is a U+000A LINE FEED (LF) character token,
        // then ignore that token and move on to the next one." 3. "Switch the
        // tokenizer to the RCDATA state." 4. "Let the original insertion mode
        // be the current insertion mode." 5. "Set the frameset-ok flag to "not
        // ok"." 6. "Switch the insertion mode to "text"."
        Outcome::Done(
            Parser {
                skip_lf: true,
                tokenizer: Some(TokenizerState::Rcdata),
                original_mode: p1.mode,
                frameset_ok: false,
                mode: Mode::Text,
                ..p1
            },
        )
    } else if g == Tag::Xmp {
        // "A start tag whose tag name is "xmp"": "If the stack of open
        // elements has a p element in button scope, then close a p element.
        // Reconstruct the active formatting elements, if any. Set the
        // frameset-ok flag to "not ok". Follow the generic raw text element
        // parsing algorithm."
        let p1 = w3c_frameset_not_ok(reconstruct_formatting(w3c_close_p_in_button_scope(p)));
        Outcome::Done(generic_text_parsing(p1, tt, true))
    } else if g == Tag::Iframe {
        // "A start tag whose tag name is "iframe"": "Set the frameset-ok flag
        // to "not ok". Follow the generic raw text element parsing
        // algorithm."
        Outcome::Done(generic_text_parsing(w3c_frameset_not_ok(p), tt, true))
    } else if g == Tag::Noembed || (g == Tag::Noscript && p.scripting) {
        // "A start tag whose tag name is "noembed"", "A start tag whose tag
        // name is "noscript", if the scripting flag is enabled": "Follow the
        // generic raw text element parsing algorithm."
        Outcome::Done(generic_text_parsing(p, tt, true))
    } else if g == Tag::Select {
        // "A start tag whose tag name is "select"": "Reconstruct the active
        // formatting elements, if any. Insert an HTML element for the token.
        // Set the frameset-ok flag to "not ok". If the insertion mode is one
        // of "in table", "in caption", "in table body", "in row", or "in
        // cell", then switch the insertion mode to "in select in table".
        // Otherwise, switch the insertion mode to "in select"." (Neither mode
        // is a `Mode`: the switch is not modelled; see the module comment.)
        Outcome::Done(w3c_frameset_not_ok(insert_html_element(reconstruct_formatting(p), tt).0))
    } else if g == Tag::Optgroup || g == Tag::Option {
        // "A start tag whose tag name is one of: "optgroup", "option"": "If
        // the current node is an option element, then pop the current node
        // off the stack of open elements."
        let p1 = if w3c_current_is(p, Tag::Option) {
            pop(p)
        } else {
            p
        };
        // "Reconstruct the active formatting elements, if any. Insert an HTML
        // element for the token."
        Outcome::Done(insert_html_element(reconstruct_formatting(p1), tt).0)
    } else if g == Tag::Rb || g == Tag::Rtc {
        // "A start tag whose tag name is one of: "rb", "rtc"": "If the stack
        // of open elements has a ruby element in scope, then generate implied
        // end tags. If the current node is not now a ruby element, this is a
        // parse error. Insert an HTML element for the token."
        let p1 = if has_in_scope(p, Tag::Ruby, Scope::Default) {
            generate_implied_end_tags(p, None)
        } else {
            p
        };
        Outcome::Done(insert_html_element(p1, tt).0)
    } else if g == Tag::Rp || g == Tag::Rt {
        // "A start tag whose tag name is one of: "rp", "rt"": "If the stack of
        // open elements has a ruby element in scope, then generate implied end
        // tags, except for rtc elements. If the current node is not now a rtc
        // element or a ruby element, this is a parse error. Insert an HTML
        // element for the token."
        let p1 = if has_in_scope(p, Tag::Ruby, Scope::Default) {
            generate_implied_end_tags(p, Some(Tag::Rtc))
        } else {
            p
        };
        Outcome::Done(insert_html_element(p1, tt).0)
    } else if g == Tag::Math {
        // "A start tag whose tag name is "math"": "Reconstruct the active
        // formatting elements, if any. Adjust MathML attributes for the token.
        // Adjust foreign attributes for the token. Insert a foreign element
        // for the token, in the MathML namespace."
        let t1 = adjust_foreign_attributes(adjust_mathml_attributes(tt));
        let p1 = insert_foreign_element(reconstruct_formatting(p), t1, Namespace::MathMl).0;
        // "If the token has its self-closing flag set, pop the current node
        // off the stack of open elements and acknowledge the token's
        // self-closing flag."
        Outcome::Done(
            if tt.self_closing {
                pop(p1)
            } else {
                p1
            },
        )
    } else if g == Tag::Svg {
        // "A start tag whose tag name is "svg"": "Reconstruct the active
        // formatting elements, if any. Adjust SVG attributes for the token.
        // Adjust foreign attributes for the token. Insert a foreign element
        // for the token, in the SVG namespace."
        let t1 = adjust_foreign_attributes(adjust_svg_attributes(tt));
        let p1 = insert_foreign_element(reconstruct_formatting(p), t1, Namespace::Svg).0;
        // "If the token has its self-closing flag set, pop the current node
        // off the stack of open elements and acknowledge the token's
        // self-closing flag."
        Outcome::Done(
            if tt.self_closing {
                pop(p1)
            } else {
                p1
            },
        )
    } else if g == Tag::Caption || g == Tag::Col || g == Tag::Colgroup || g == Tag::Frame || g == Tag::Head || g == Tag::Tbody || g
        == Tag::Td || g == Tag::Tfoot || g == Tag::Th || g == Tag::Thead || g == Tag::Tr {
        // "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "frame", "head", "tbody", "td", "tfoot", "th", "thead",
        // "tr"": "Parse error."
        Outcome::Done(p)
    } else {
        // "Any other start tag": "Reconstruct the active formatting elements,
        // if any. Insert an HTML element for the token."
        Outcome::Done(insert_html_element(reconstruct_formatting(p), tt).0)
    }
}

/// The tags of "An end tag whose tag name is one of: "address",
/// "article", "aside", "blockquote", "button", "center", "details",
/// "dialog", "dir", "div", "dl", "fieldset", "figcaption", "figure",
/// "footer", "header", "listing", "main", "nav", "ol", "pre", "section",
/// "summary", "ul"".
pub open spec fn w3c_block_end_tag(g: Tag) -> bool {
    g == Tag::Address || g == Tag::Article || g == Tag::Aside || g == Tag::Blockquote || g == Tag::Button || g == Tag::Center || g
        == Tag::Details || g == Tag::Dialog || g == Tag::Dir || g == Tag::Div || g == Tag::Dl || g == Tag::Fieldset || g
        == Tag::Figcaption || g == Tag::Figure || g == Tag::Footer || g == Tag::Header || g == Tag::Listing || g == Tag::Main || g
        == Tag::Nav || g == Tag::Ol || g == Tag::Pre || g == Tag::Section || g == Tag::Summary || g == Tag::Ul
}

/// "a", "b", "big", "code", "em", "font", "i", "nobr", "s", "small",
/// "strike", "strong", "tt", "u"
pub open spec fn w3c_formatting_end_tag(g: Tag) -> bool {
    g == Tag::A || g == Tag::B || g == Tag::Big || g == Tag::Code || g == Tag::Em || g == Tag::Font || g == Tag::I || g == Tag::Nobr
        || g == Tag::S || g == Tag::Small || g == Tag::Strike || g == Tag::Strong || g == Tag::Tt || g == Tag::U
}

/// The entries for an end tag token, in the W3C's order. (The `body` and
/// `html` entries' "if there is a node in the stack of open elements that is
/// not either a dd element, …, the body element, or the html element, then
/// this is a parse error" changes nothing: parse errors are not modelled.)
pub open spec fn w3c_in_body_end(env: EncFns, p: Parser, tt: TagTok) -> Outcome {
    let g = tt.tag;
    if g == Tag::Template {
        // "An end tag whose tag name is "template"": "Process the token using
        // the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, Tok::End(tt))
    } else if g == Tag::Body {
        // "An end tag whose tag name is "body"":
        if !has_in_scope(p, Tag::Body, Scope::Default) {
            // "If the stack of open elements does not have a body element in
            // scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, if there is a node … then this is a parse error."
            // "Switch the insertion mode to "after body"."
            Outcome::Done(Parser { mode: Mode::AfterBody, ..p })
        }
    } else if g == Tag::Html {
        // "An end tag whose tag name is "html"":
        if !has_in_scope(p, Tag::Body, Scope::Default) {
            // "If the stack of open elements does not have a body element in
            // scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, if there is a node … then this is a parse error."
            // "Switch the insertion mode to "after body". Reprocess the
            // token."
            Outcome::Reprocess(Parser { mode: Mode::AfterBody, ..p }, Tok::End(tt))
        }
    } else if w3c_block_end_tag(g) {
        // "An end tag whose tag name is one of: "address", …, "ul"":
        if !has_in_scope(p, g, Scope::Default) {
            // "If the stack of open elements does not have an element in scope
            // that is an HTML element with the same tag name as that of the
            // token, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps: 1. Generate implied end tags. 2. If
            // the current node is not an HTML element with the same tag name
            // as that of the token, then this is a parse error. 3. Pop
            // elements from the stack of open elements until an HTML element
            // with the same tag name as the token has been popped from the
            // stack."
            Outcome::Done(pop_until_popped(generate_implied_end_tags(p, None), g))
        }
    } else if g == Tag::Form {
        // "An end tag whose tag name is "form"":
        if !open_has_html(p, Tag::Template) {
            // "If there is no template element on the stack of open elements,
            // then run these substeps:"
            // 1. "Let node be the element that the form element pointer is set
            // to, or null if it is not set to an element."
            let node = p.form;
            // 2. "Set the form element pointer to null."
            let p1 = Parser { form: None, ..p };
            if node is None || !has_node_in_scope(p1, node->Some_0, Scope::Default) {
                // 3. "If node is null or if the stack of open elements does not
                // have node in scope, then this is a parse error; abort these
                // steps and ignore the token."
                Outcome::Done(p1)
            } else {
                // 4. "Generate implied end tags."
                let p2 = generate_implied_end_tags(p1, None);
                // 5. "If the current node is not node, then this is a parse
                // error."
                // 6. "Remove node from the stack of open elements."
                let i = open_index_of(p2, node->Some_0);
                Outcome::Done(
                    if i >= 0 {
                        remove_open_at(p2, i)
                    } else {
                        p2
                    },
                )
            }
        } else {
            // "If there is a template element on the stack of open elements,
            // then run these substeps instead:"
            if !has_in_scope(p, Tag::Form, Scope::Default) {
                // 1. "If the stack of open elements does not have a form element
                // in scope, then this is a parse error; abort these steps and
                // ignore the token."
                Outcome::Done(p)
            } else {
                // 2. "Generate implied end tags." 3. "If the current node is not
                // a form element, then this is a parse error." 4. "Pop elements
                // from the stack of open elements until a form element has been
                // popped from the stack."
                Outcome::Done(pop_until_popped(generate_implied_end_tags(p, None), Tag::Form))
            }
        }
    } else if g == Tag::P {
        // "An end tag whose tag name is "p"": "If the stack of open elements
        // does not have a p element in button scope, then this is a parse
        // error; insert an HTML element for a "p" start tag token with no
        // attributes."
        let p1 = if !has_in_scope(p, Tag::P, Scope::Button) {
            insert_html_element(p, start_tag_named(w3c_name_p())).0
        } else {
            p
        };
        // "Close a p element."
        Outcome::Done(w3c_close_p(p1))
    } else if g == Tag::Li {
        // "An end tag whose tag name is "li"":
        if !has_in_scope(p, Tag::Li, Scope::ListItem) {
            // "If the stack of open elements does not have an li element in
            // list item scope, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps: 1. Generate implied end tags, except
            // for li elements. 2. If the current node is not an li element,
            // then this is a parse error. 3. Pop elements from the stack of
            // open elements until an li element has been popped from the
            // stack."
            Outcome::Done(pop_until_popped(generate_implied_end_tags(p, Some(Tag::Li)), Tag::Li))
        }
    } else if g == Tag::Dd || g == Tag::Dt {
        // "An end tag whose tag name is one of: "dd", "dt"":
        if !has_in_scope(p, g, Scope::Default) {
            // "If the stack of open elements does not have an element in scope
            // that is an HTML element with the same tag name as that of the
            // token, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps: 1. Generate implied end tags, except
            // for HTML elements with the same tag name as the token. 2. If the
            // current node is not an HTML element with the same tag name as
            // that of the token, then this is a parse error. 3. Pop elements
            // from the stack of open elements until an HTML element with the
            // same tag name as the token has been popped from the stack."
            Outcome::Done(pop_until_popped(generate_implied_end_tags(p, Some(g)), g))
        }
    } else if w3c_heading_tag(g) {
        // "An end tag whose tag name is one of: "h1", "h2", "h3", "h4", "h5",
        // "h6"":
        if !has_heading_in_scope(p) {
            // "If the stack of open elements does not have an element in scope
            // that is an HTML element and whose tag name is one of "h1", "h2",
            // "h3", "h4", "h5", or "h6", then this is a parse error; ignore the
            // token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps: 1. Generate implied end tags. 2. If
            // the current node is not an HTML element with the same tag name
            // as that of the token, then this is a parse error. 3. Pop
            // elements from the stack of open elements until an HTML element
            // whose tag name is one of "h1", "h2", "h3", "h4", "h5", or "h6" has
            // been popped from the stack."
            Outcome::Done(pop_until_heading_popped(generate_implied_end_tags(p, None)))
        }
    }
    // "An end tag whose tag name is "sarcasm"": "Take a deep breath, then act
    // as described in the "any other end tag" entry below." ("sarcasm" has
    // no `Tag`: it is `Tag::Other`, and reaches that entry below.)
     else if w3c_formatting_end_tag(g) {
        // "An end tag whose tag name is one of: "a", "b", "big", "code", "em",
        // "font", "i", "nobr", "s", "small", "strike", "strong", "tt", "u"":
        // "Run the adoption agency algorithm for the token."
        Outcome::Done(w3c_adoption_agency(p, tt))
    } else if g == Tag::Applet || g == Tag::Marquee || g == Tag::Object {
        // "An end tag token whose tag name is one of: "applet", "marquee",
        // "object"":
        if !has_in_scope(p, g, Scope::Default) {
            // "If the stack of open elements does not have an element in scope
            // that is an HTML element with the same tag name as that of the
            // token, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps: 1. Generate implied end tags. 2. If
            // the current node is not an HTML element with the same tag name
            // as that of the token, then this is a parse error. 3. Pop
            // elements from the stack of open elements until an HTML element
            // with the same tag name as the token has been popped from the
            // stack. 4. Clear the list of active formatting elements up to the
            // last marker."
            Outcome::Done(clear_to_last_marker(pop_until_popped(generate_implied_end_tags(p, None), g)))
        }
    } else if g == Tag::Br {
        // "An end tag whose tag name is "br"": "Parse error. Drop the
        // attributes from the token, and act as described in the next entry;
        // i.e., act as if this was a "br" start tag token with no attributes,
        // rather than the end tag token that it actually is."
        w3c_in_body_start(env, p, start_tag_named(w3c_name_br()))
    } else {
        // "Any other end tag": "Run these steps: …"
        Outcome::Done(w3c_any_other_end_tag(p, tt))
    }
}

/// W3C HTML 5.2 §8.2.5.4.7 the "in body" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-body-insertion-mode>).
pub open spec fn w3c_mode_in_body(env: EncFns, p: Parser, t: Tok) -> Outcome {
    match t {
        // "A character token that is U+0000 NULL", "A character token that is
        // one of U+0009 …", "Any other character token".
        Tok::Char(c) => w3c_in_body_char(p, c),
        // "A comment token": "Insert a comment."
        Tok::Comment(data) => Outcome::Done(insert_comment(p, data, None)),
        // "A DOCTYPE token": "Parse error."
        Tok::Doctype { .. } => Outcome::Done(p),
        Tok::Start(tt) => w3c_in_body_start(env, p, tt),
        Tok::End(tt) => w3c_in_body_end(env, p, tt),
        Tok::Eof => {
            // "An end-of-file token":
            if p.template_modes.len() > 0 {
                // "If the stack of template insertion modes is not empty, then
                // process the token using the rules for the "in template"
                // insertion mode."
                Outcome::Using(Mode::InTemplate, p, t)
            } else {
                // "Otherwise, follow these steps: 1. If there is a node in the
                // stack of open elements that is not either … then this is a
                // parse error. 2. Stop parsing."
                Outcome::Done(stop_parsing(p))
            }
        },
        // No entry (see [`super`]): ignored.
        Tok::Pi(..) => Outcome::Done(p),
    }
}

} // verus!
