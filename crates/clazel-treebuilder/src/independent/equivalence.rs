//! The equivalence lemmas: for each insertion mode, the W3C transcription
//! ([`super`]) and [`crate::spec`]'s give the same outcome on every input
//! where the two documents prescribe the same thing. Each lemma's
//! precondition excludes exactly the inputs where they differ, and its doc
//! comment says what the difference is; the WHATWG text (which
//! [`crate::spec`] follows) is the one the parser implements.
//!
//! Common to every lemma: the W3C has no processing instruction tokens
//! (`Tok::Pi`), which the WHATWG modes insert as nodes.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §8.2.5.4.1 to §8.2.5.4.3, §8.2.5.4.5

/// "initial" (W3C §8.2.5.4.1, WHATWG §13.2.6.4.1): the same rules.
pub proof fn lemma_initial(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_initial(env, p, t) == mode_initial(env, p, t),
{
}

/// The insertion target redirection map has no entry for the Document
/// node: its only entry is the fragment case's `html` root (§13.4 step 15),
/// an element. (The WHATWG "before html" inserts the root "at the adjusted
/// insertion location", which consults the map; the W3C appends it.)
pub open spec fn no_document_redirect(p: Parser) -> bool {
    p.redirect is None || p.redirect->Some_0.0 != 0
}

/// A node `create_element_for_token` just created has no parent.
proof fn lemma_created_parentless(p: Parser, tt: TagTok, ns: Namespace, parent: NodeId)
    requires
        !p.stopped,
        !create_element_for_token(p, tt, ns, parent).0.stopped,
        !(ns == Namespace::Html && tt.tag == Tag::Template),
    ensures
        ({
            let (p1, e) = create_element_for_token(p, tt, ns, parent);
            p1.doc.nodes[e.id as int].parent is None
        }),
{
}

/// W3C "append" to the Document is the WHATWG "insert an element at the
/// adjusted insertion location" with the location (the Document, null), for
/// a node with no parent, when the map does not redirect the Document.
proof fn lemma_append_to_document(p: Parser, node: NodeId)
    requires
        no_document_redirect(p),
        p.stopped || p.doc.nodes[node as int].parent is None,
    ensures
        w3c_append_to_document(p, node) == insert_element_at(p, node, Some(document_location())),
{
}

/// "before html" (W3C §8.2.5.4.2, WHATWG §13.2.6.4.2): the same rules,
/// where the W3C's "append it to the Document object" (DOM pre-insert) and
/// the WHATWG's "insert an element at the adjusted insertion location" with
/// the Document as the location agree: when the insertion target
/// redirection map has no entry for the Document ([`no_document_redirect`]).
pub proof fn lemma_before_html(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        no_document_redirect(p),
    ensures
        w3c_mode_before_html(env, p, t) == mode_before_html(env, p, t),
{
    let tt = if w3c_start(t, Tag::Html) {
        t->Start_0
    } else {
        start_tag_named(w3c_name_html())
    };
    assert(tag_of(w3c_name_html()) == Tag::Html) by (compute_only);
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, 0);
    if !p1.stopped {
        lemma_created_parentless(p, tt, Namespace::Html, 0);
    }
    lemma_append_to_document(p1, e.id);
}

/// "before head" (W3C §8.2.5.4.3, WHATWG §13.2.6.4.3): the same rules.
pub proof fn lemma_before_head(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_before_head(env, p, t) == mode_before_head(env, p, t),
{
}

/// "in head" (W3C §8.2.5.4.4, WHATWG §13.2.6.4.4): the same rules.
pub proof fn lemma_in_head(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_in_head(env, p, t) == mode_in_head(env, p, t),
{
}

/// "in head noscript" (W3C §8.2.5.4.5, WHATWG §13.2.6.4.5): the same rules.
pub proof fn lemma_in_head_noscript(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_in_head_noscript(env, p, t) == mode_in_head_noscript(env, p, t),
{
}

/// "after head" (W3C §8.2.5.4.6, WHATWG §13.2.6.4.6): the same rules.
pub proof fn lemma_after_head(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_after_head(env, p, t) == mode_after_head(env, p, t),
{
}

// ---------------------------------------------------------------------
// §8.2.5.4.8

/// "text" (W3C §8.2.5.4.8, WHATWG §13.2.6.4.8): the same rules.
pub proof fn lemma_text(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_text(env, p, t) == mode_text(env, p, t),
{
}

// ---------------------------------------------------------------------
// §8.2.5.4.11, §8.2.5.4.12

/// "in caption" (W3C §8.2.5.4.11, WHATWG §13.2.6.4.11): the same rules.
pub proof fn lemma_in_caption(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_in_caption(env, p, t) == mode_in_caption(env, p, t),
{
}

/// "in column group" (W3C §8.2.5.4.12, WHATWG §13.2.6.4.12): the same
/// rules.
pub proof fn lemma_in_column_group(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_in_column_group(env, p, t) == mode_in_column_group(env, p, t),
{
}

// ---------------------------------------------------------------------
// §8.2.5.4.19 to §8.2.5.4.23

/// "after body" (W3C §8.2.5.4.19, WHATWG §13.2.6.4.17): the same rules.
pub proof fn lemma_after_body(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_after_body(env, p, t) == mode_after_body(env, p, t),
{
}

/// The stack's only `html` element is its first entry, "the root html
/// element" (the parser creates one `html` element, in "before html", and
/// the fragment case puts its root first).
pub open spec fn html_only_at_root(p: Parser) -> bool {
    &&& p.open.len() > 0
    &&& is_html(p.open[0], Tag::Html)
    &&& forall|i: int| 0 < i < p.open.len() ==> !is_html(#[trigger] p.open[i], Tag::Html)
}

/// "in frameset" (W3C §8.2.5.4.20, WHATWG §13.2.6.4.18): the same rules,
/// where the W3C's "if the current node is the root html element" (read
/// here as: the current node is an `html` element) and the WHATWG
/// transcription's reading of the same words agree: when the root is the
/// stack's only `html` element ([`html_only_at_root`]).
pub proof fn lemma_in_frameset(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        html_only_at_root(p),
    ensures
        w3c_mode_in_frameset(env, p, t) == mode_in_frameset(env, p, t),
{
}

/// "after frameset" (W3C §8.2.5.4.21, WHATWG §13.2.6.4.19): the same rules.
pub proof fn lemma_after_frameset(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_after_frameset(env, p, t) == mode_after_frameset(env, p, t),
{
}

/// "after after body" (W3C §8.2.5.4.22, WHATWG §13.2.6.4.20): the same
/// rules.
pub proof fn lemma_after_after_body(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_after_after_body(env, p, t) == mode_after_after_body(env, p, t),
{
}

/// "after after frameset" (W3C §8.2.5.4.23, WHATWG §13.2.6.4.21): the same
/// rules.
pub proof fn lemma_after_after_frameset(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_after_after_frameset(env, p, t) == mode_after_after_frameset(env, p, t),
{
}

} // verus!
