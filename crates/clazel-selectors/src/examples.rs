//! Concrete selectors on a concrete document, evaluated on the spec, each stating what the
//! standard's text says. They are the kill certificates of `mutations.json`: each mutation of
//! the spec makes one of these false. Kept apart from the theorems so that a mutant that
//! breaks one does not stop Verus before it checks a certificate.
//!
//! The document ([`doc`]): 0 the document, 1 `html`, 2 `body`, 3 `div id=x class="ab c"`
//! holding 4, a text node of two spaces, then 5 `p lang=EN`, 6 `a href=/`, 7 `p` and 8
//! `span`, the children of `body` in that order.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An HTML element named `name` with attributes `attributes`.
pub open spec fn element(name: Seq<u32>, attributes: Seq<Attr>) -> NodeKind {
    NodeKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: name,
        attributes,
        template_contents: None,
        form_owner: None,
    }
}

/// An attribute without a namespace.
pub open spec fn attr(name: Seq<u32>, value: Seq<u32>) -> Attr {
    Attr { namespace: None, prefix: None, local_name: name, value }
}

/// A node.
pub open spec fn node(kind: NodeKind, parent: Option<NodeId>, children: Seq<NodeId>) -> clazel_dom::spec::Node {
    clazel_dom::spec::Node { kind, parent, children, wrapper: None }
}

/// The document, in `mode`.
pub open spec fn doc(mode: DocumentMode) -> Document {
    Document {
        nodes: seq![
            node(NodeKind::Document { mode, url: seq![], base_url: seq![] }, None, seq![1usize]),
            node(element(seq![0x68u32, 0x74, 0x6D, 0x6C], seq![]), Some(0usize), seq![2usize]),
            node(element(seq![0x62u32, 0x6F, 0x64, 0x79], seq![]), Some(1usize), seq![3usize, 5, 6, 7, 8]),
            node(
                element(
                    seq![0x64u32, 0x69, 0x76],
                    seq![
                        attr(seq![0x69u32, 0x64], seq![0x78u32]),
                        attr(seq![0x63u32, 0x6C, 0x61, 0x73, 0x73], seq![0x61u32, 0x62, 0x20, 0x63]),
                    ],
                ),
                Some(2usize),
                seq![4usize],
            ),
            node(NodeKind::Text { data: seq![0x20u32, 0x20] }, Some(3usize), seq![]),
            node(element(seq![0x70u32], seq![attr(seq![0x6Cu32, 0x61, 0x6E, 0x67], seq![0x45u32, 0x4E])]), Some(2usize), seq![]),
            node(element(seq![0x61u32], seq![attr(seq![0x68u32, 0x72, 0x65, 0x66], seq![0x2Fu32])]), Some(2usize), seq![]),
            node(element(seq![0x70u32], seq![]), Some(2usize), seq![]),
            node(element(seq![0x73u32, 0x70, 0x61, 0x6E], seq![]), Some(2usize), seq![]),
        ],
    }
}

/// True if `source` parses and matches node `x` of the document in `mode`.
pub open spec fn matches(mode: DocumentMode, source: Seq<u32>, x: NodeId) -> bool {
    match parse_a_selector(source) {
        Some(list) => match_a_selector_against_an_element(doc(mode), list, x),
        None => false,
    }
}

/// True if `source` is a valid selector.
pub open spec fn parses(source: Seq<u32>) -> bool {
    parse_a_selector(source) is Some
}

/// The specificity of the first complex selector of `source`.
pub open spec fn specificity_of(source: Seq<u32>) -> Specificity {
    match parse_a_selector(source) {
        Some(list) => if list.len() > 0 {
            specificity(list[0])
        } else {
            zero()
        },
        None => zero(),
    }
}

/// `P` matches node 5. HTML: a type selector is lowercased before it is compared with an HTML element's name, so P matches p.
pub proof fn lemma_example_type_name_case()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x50u32], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x50u32], 5)) by (compute_only);
}

/// `|p` does not match node 5. §5.3: |p is an element without a namespace, which an HTML p is not.
pub proof fn lemma_example_no_namespace_ignored()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x7Cu32, 0x70], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x7Cu32, 0x70], 5)) by (compute_only);
}

/// `#y` does not match node 3. §7: #y does not match the element whose ID is x.
pub proof fn lemma_example_id_value_ignored()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x23u32, 0x79], 3),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x23u32, 0x79], 3)) by (compute_only);
}

/// `#X` matches node 3 in quirks mode. §7 and HTML: in quirks mode IDs match ASCII case-insensitively, so #X matches id=x.
pub proof fn lemma_example_quirks_id_case()
    ensures
        matches(DocumentMode::Quirks, seq![0x23u32, 0x58], 3),
{
    assert(matches(DocumentMode::Quirks, seq![0x23u32, 0x58], 3)) by (compute_only);
}

/// `.C` matches node 3 in quirks mode. §6.6: in quirks mode class names match ASCII case-insensitively, so .C matches class="ab c".
pub proof fn lemma_example_quirks_class_case()
    ensures
        matches(DocumentMode::Quirks, seq![0x2Eu32, 0x43], 3),
{
    assert(matches(DocumentMode::Quirks, seq![0x2Eu32, 0x43], 3)) by (compute_only);
}

/// `.a` does not match node 3. §6.6: a class selector is [class~=v], a whole word: .a does not match class="ab c".
pub proof fn lemma_example_class_substring()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x2Eu32, 0x61], 3),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x2Eu32, 0x61], 3)) by (compute_only);
}

/// `[lang=e]` does not match node 5. §6.1: [lang=e] needs the whole value, which is "EN".
pub proof fn lemma_example_attr_equals_prefix()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x3D, 0x65, 0x5D], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x3D, 0x65, 0x5D], 5)) by (compute_only);
}

/// `[class~=b]` does not match node 3. §6.1: [class~=b] needs the word b, and class="ab c" has none.
pub proof fn lemma_example_attr_includes_substring()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x7E, 0x3D, 0x62, 0x5D], 3),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x7E, 0x3D, 0x62, 0x5D], 3)) by (compute_only);
}

/// `[lang|=e]` does not match node 5. §6.1: |=e needs "e" or "e-" at the start, and "EN" is neither.
pub proof fn lemma_example_attr_dashmatch_any()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x7C, 0x3D, 0x65, 0x5D], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x7C, 0x3D, 0x65, 0x5D], 5)) by (compute_only);
}

/// `[href^=x]` does not match node 6. §6.2: [href^=x] needs href to begin with x.
pub proof fn lemma_example_attr_prefix_any()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x68, 0x72, 0x65, 0x66, 0x5E, 0x3D, 0x78, 0x5D], 6),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x68, 0x72, 0x65, 0x66, 0x5E, 0x3D, 0x78, 0x5D], 6)) by (compute_only);
}

/// `[href$="/"]` matches node 6. §6.2: [href$="/"] matches href="/".
pub proof fn lemma_example_attr_suffix_negated()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x68, 0x72, 0x65, 0x66, 0x24, 0x3D, 0x22, 0x2F, 0x22, 0x5D], 6),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x68, 0x72, 0x65, 0x66, 0x24, 0x3D, 0x22, 0x2F, 0x22, 0x5D], 6)) by (compute_only);
}

/// `[href*=""]` does not match node 6. §6.2: "If val is the empty string then the selector does not represent anything."
pub proof fn lemma_example_attr_substring_empty()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x68, 0x72, 0x65, 0x66, 0x2A, 0x3D, 0x22, 0x22, 0x5D], 6),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x68, 0x72, 0x65, 0x66, 0x2A, 0x3D, 0x22, 0x22, 0x5D], 6)) by (compute_only);
}

/// `[id=X i]` matches node 3. §6.3: [id=X i] matches id=x case-insensitively.
pub proof fn lemma_example_flag_i_ignored()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x69, 0x64, 0x3D, 0x58, 0x20, 0x69, 0x5D], 3),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x69, 0x64, 0x3D, 0x58, 0x20, 0x69, 0x5D], 3)) by (compute_only);
}

/// `[lang=en s]` does not match node 5. §6.3: [lang=en s] is case-sensitive, and the value is "EN".
pub proof fn lemma_example_flag_s_ignored()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x3D, 0x65, 0x6E, 0x20, 0x73, 0x5D], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x3D, 0x65, 0x6E, 0x20, 0x73, 0x5D], 5)) by (compute_only);
}

/// `[lang=en]` matches node 5. HTML §4.16.2 lists lang, so [lang=en] matches lang=EN.
pub proof fn lemma_example_html_list_without_lang()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x3D, 0x65, 0x6E, 0x5D], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x3D, 0x65, 0x6E, 0x5D], 5)) by (compute_only);
}

/// `:visited` does not match node 6. :visited never matches (modelling choice).
pub proof fn lemma_example_visited_matches()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x76, 0x69, 0x73, 0x69, 0x74, 0x65, 0x64], 6),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x76, 0x69, 0x73, 0x69, 0x74, 0x65, 0x64], 6)) by (compute_only);
}

/// `:any-link` matches node 6. §9.1: :any-link matches what :link or :visited does: an a with href.
pub proof fn lemma_example_any_link_never()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x61, 0x6E, 0x79, 0x2D, 0x6C, 0x69, 0x6E, 0x6B], 6),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x61, 0x6E, 0x79, 0x2D, 0x6C, 0x69, 0x6E, 0x6B], 6)) by (compute_only);
}

/// `:link` matches node 6. HTML §4.16.3: an a with an href attribute matches :link.
pub proof fn lemma_example_link_needs_no_href()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x6C, 0x69, 0x6E, 0x6B], 6),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x6C, 0x69, 0x6E, 0x6B], 6)) by (compute_only);
}

/// `:root` matches node 1. §15.1: :root is the document element, html.
pub proof fn lemma_example_root_is_element()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x72, 0x6F, 0x6F, 0x74], 1),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x72, 0x6F, 0x6F, 0x74], 1)) by (compute_only);
}

/// `div:empty` matches node 3. §15.2: white space does not make an element non-empty.
pub proof fn lemma_example_empty_whitespace_counts()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x64u32, 0x69, 0x76, 0x3A, 0x65, 0x6D, 0x70, 0x74, 0x79], 3),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x64u32, 0x69, 0x76, 0x3A, 0x65, 0x6D, 0x70, 0x74, 0x79], 3)) by (compute_only);
}

/// `:first-child` matches node 3. §15.3.3: :first-child is :nth-child(1); div is body's first child.
pub proof fn lemma_example_first_child_second()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64], 3),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64], 3)) by (compute_only);
}

/// `span:last-child` matches node 8. §15.3.4: span is body's last child.
pub proof fn lemma_example_last_child_from_start()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x73u32, 0x70, 0x61, 0x6E, 0x3A, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64], 8),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x73u32, 0x70, 0x61, 0x6E, 0x3A, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64], 8)) by (compute_only);
}

/// `div:only-child` does not match node 3. §15.3.5: div has siblings.
pub proof fn lemma_example_only_child_or()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x64u32, 0x69, 0x76, 0x3A, 0x6F, 0x6E, 0x6C, 0x79, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64], 3),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x64u32, 0x69, 0x76, 0x3A, 0x6F, 0x6E, 0x6C, 0x79, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64], 3)) by (compute_only);
}

/// `p:first-of-type` matches node 5. §15.4: the first p is the first of its type, though not the first child.
pub proof fn lemma_example_of_type_counts_all()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x70u32, 0x3A, 0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x70u32, 0x3A, 0x66, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65], 5)) by (compute_only);
}

/// `:nth-child(2n+1)` does not match node 5. §15.3.1: 2n+1 does not take index 2.
pub proof fn lemma_example_nth_ignores_step()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x32, 0x6E, 0x2B, 0x31, 0x29], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x32, 0x6E, 0x2B, 0x31, 0x29], 5)) by (compute_only);
}

/// `span:nth-last-child(1)` matches node 8. §15.3.2: :nth-last-child(1) counts from the end.
pub proof fn lemma_example_nth_last_from_start()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x73u32, 0x70, 0x61, 0x6E, 0x3A, 0x6E, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x31, 0x29], 8),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x73u32, 0x70, 0x61, 0x6E, 0x3A, 0x6E, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x31, 0x29], 8)) by (compute_only);
}

/// `:is(p)` matches node 5. §4.2: :is(p) matches a p.
pub proof fn lemma_example_is_negated()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x69, 0x73, 0x28, 0x70, 0x29], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x69, 0x73, 0x28, 0x70, 0x29], 5)) by (compute_only);
}

/// `p:not(#x)` matches node 5. §4.3: p:not(#x) matches a p whose ID is not x.
pub proof fn lemma_example_not_not_negated()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x70u32, 0x3A, 0x6E, 0x6F, 0x74, 0x28, 0x23, 0x78, 0x29], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x70u32, 0x3A, 0x6E, 0x6F, 0x74, 0x28, 0x23, 0x78, 0x29], 5)) by (compute_only);
}

/// `:where(span)` does not match node 5. §4.4: :where(span) does not match a p.
pub proof fn lemma_example_where_always()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28, 0x73, 0x70, 0x61, 0x6E, 0x29], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28, 0x73, 0x70, 0x61, 0x6E, 0x29], 5)) by (compute_only);
}

/// `html p` matches node 5. §16.1: html p matches a p inside html.
pub proof fn lemma_example_descendant_negated()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x68u32, 0x74, 0x6D, 0x6C, 0x20, 0x70], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x68u32, 0x74, 0x6D, 0x6C, 0x20, 0x70], 5)) by (compute_only);
}

/// `html > p` does not match node 5. §16.2: html > p needs p's parent to be html.
pub proof fn lemma_example_child_any_parent()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x68u32, 0x74, 0x6D, 0x6C, 0x20, 0x3E, 0x20, 0x70], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x68u32, 0x74, 0x6D, 0x6C, 0x20, 0x3E, 0x20, 0x70], 5)) by (compute_only);
}

/// `div + a` does not match node 6. §16.3: div + a needs div immediately before a.
pub proof fn lemma_example_next_sibling_any_earlier()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x64u32, 0x69, 0x76, 0x20, 0x2B, 0x20, 0x61], 6),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x64u32, 0x69, 0x76, 0x20, 0x2B, 0x20, 0x61], 6)) by (compute_only);
}

/// `div ~ a` matches node 6. §16.4: div ~ a needs div anywhere before a.
pub proof fn lemma_example_subsequent_sibling_next_only()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x64u32, 0x69, 0x76, 0x20, 0x7E, 0x20, 0x61], 6),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x64u32, 0x69, 0x76, 0x20, 0x7E, 0x20, 0x61], 6)) by (compute_only);
}

/// `#x34y` has specificity (1, 0, 0). §17's example: #x34y is a=1 b=0 c=0.
pub proof fn lemma_example_id_counts_b()
    ensures
        specificity_of(seq![0x23u32, 0x78, 0x33, 0x34, 0x79]) == (Specificity { a: 1, b: 0, c: 0 }),
{
    assert(specificity_of(seq![0x23u32, 0x78, 0x33, 0x34, 0x79]) == (Specificity { a: 1, b: 0, c: 0 })) by (compute_only);
}

/// `LI.red.level` has specificity (0, 2, 1). §17's example: LI.red.level is a=0 b=2 c=1.
pub proof fn lemma_example_class_counts_c()
    ensures
        specificity_of(seq![0x4Cu32, 0x49, 0x2E, 0x72, 0x65, 0x64, 0x2E, 0x6C, 0x65, 0x76, 0x65, 0x6C]) == (Specificity { a: 0, b: 2, c: 1 }),
{
    assert(specificity_of(seq![0x4Cu32, 0x49, 0x2E, 0x72, 0x65, 0x64, 0x2E, 0x6C, 0x65, 0x76, 0x65, 0x6C]) == (Specificity { a: 0, b: 2, c: 1 })) by (compute_only);
}

/// `H1 + *[REL=up]` has specificity (0, 1, 1). §17's example: H1 + *[REL=up] is a=0 b=1 c=1.
pub proof fn lemma_example_attribute_counts_c()
    ensures
        specificity_of(seq![0x48u32, 0x31, 0x20, 0x2B, 0x20, 0x2A, 0x5B, 0x52, 0x45, 0x4C, 0x3D, 0x75, 0x70, 0x5D]) == (Specificity { a: 0, b: 1, c: 1 }),
{
    assert(specificity_of(seq![0x48u32, 0x31, 0x20, 0x2B, 0x20, 0x2A, 0x5B, 0x52, 0x45, 0x4C, 0x3D, 0x75, 0x70, 0x5D]) == (Specificity { a: 0, b: 1, c: 1 })) by (compute_only);
}

/// `UL OL+LI` has specificity (0, 0, 3). §17's example: UL OL+LI is a=0 b=0 c=3.
pub proof fn lemma_example_type_counts_nothing()
    ensures
        specificity_of(seq![0x55u32, 0x4C, 0x20, 0x4F, 0x4C, 0x2B, 0x4C, 0x49]) == (Specificity { a: 0, b: 0, c: 3 }),
{
    assert(specificity_of(seq![0x55u32, 0x4C, 0x20, 0x4F, 0x4C, 0x2B, 0x4C, 0x49]) == (Specificity { a: 0, b: 0, c: 3 })) by (compute_only);
}

/// `*` has specificity (0, 0, 0). §17: "ignore the universal selector"; * is a=0 b=0 c=0.
pub proof fn lemma_example_universal_counts()
    ensures
        specificity_of(seq![0x2Au32]) == (Specificity { a: 0, b: 0, c: 0 }),
{
    assert(specificity_of(seq![0x2Au32]) == (Specificity { a: 0, b: 0, c: 0 })) by (compute_only);
}

/// `.qux:where(em, #foo#bar#baz)` has specificity (0, 1, 0). §17's example: .qux:where(em, #foo#bar#baz) is (0,1,0).
pub proof fn lemma_example_where_counts_argument()
    ensures
        specificity_of(seq![0x2Eu32, 0x71, 0x75, 0x78, 0x3A, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28, 0x65, 0x6D, 0x2C, 0x20, 0x23, 0x66, 0x6F, 0x6F, 0x23, 0x62, 0x61, 0x72, 0x23, 0x62, 0x61, 0x7A, 0x29]) == (Specificity { a: 0, b: 1, c: 0 }),
{
    assert(specificity_of(seq![0x2Eu32, 0x71, 0x75, 0x78, 0x3A, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28, 0x65, 0x6D, 0x2C, 0x20, 0x23, 0x66, 0x6F, 0x6F, 0x23, 0x62, 0x61, 0x72, 0x23, 0x62, 0x61, 0x7A, 0x29]) == (Specificity { a: 0, b: 1, c: 0 })) by (compute_only);
}

/// `:is(em, #foo)` has specificity (1, 0, 0). §17's example: :is(em, #foo) is (1,0,0), its most specific argument.
pub proof fn lemma_example_is_sums_arguments()
    ensures
        specificity_of(seq![0x3Au32, 0x69, 0x73, 0x28, 0x65, 0x6D, 0x2C, 0x20, 0x23, 0x66, 0x6F, 0x6F, 0x29]) == (Specificity { a: 1, b: 0, c: 0 }),
{
    assert(specificity_of(seq![0x3Au32, 0x69, 0x73, 0x28, 0x65, 0x6D, 0x2C, 0x20, 0x23, 0x66, 0x6F, 0x6F, 0x29]) == (Specificity { a: 1, b: 0, c: 0 })) by (compute_only);
}

/// `#s12:not(FOO)` has specificity (1, 0, 1). §17's example: #s12:not(FOO) is a=1 b=0 c=1.
pub proof fn lemma_example_not_counts_nothing()
    ensures
        specificity_of(seq![0x23u32, 0x73, 0x31, 0x32, 0x3A, 0x6E, 0x6F, 0x74, 0x28, 0x46, 0x4F, 0x4F, 0x29]) == (Specificity { a: 1, b: 0, c: 1 }),
{
    assert(specificity_of(seq![0x23u32, 0x73, 0x31, 0x32, 0x3A, 0x6E, 0x6F, 0x74, 0x28, 0x46, 0x4F, 0x4F, 0x29]) == (Specificity { a: 1, b: 0, c: 1 })) by (compute_only);
}

/// `:is(.a, #b)` has specificity (1, 0, 0). §17 compares A first: :is(.a, #b) takes #b's (1,0,0).
pub proof fn lemma_example_compare_b_before_a()
    ensures
        specificity_of(seq![0x3Au32, 0x69, 0x73, 0x28, 0x2E, 0x61, 0x2C, 0x20, 0x23, 0x62, 0x29]) == (Specificity { a: 1, b: 0, c: 0 }),
{
    assert(specificity_of(seq![0x3Au32, 0x69, 0x73, 0x28, 0x2E, 0x61, 0x2C, 0x20, 0x23, 0x62, 0x29]) == (Specificity { a: 1, b: 0, c: 0 })) by (compute_only);
}

/// `:not(::before)` is invalid. §4.3: pseudo-elements "are not valid within :not()".
pub proof fn lemma_example_pseudo_element_in_not()
    ensures
        !parses(seq![0x3Au32, 0x6E, 0x6F, 0x74, 0x28, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65, 0x29]),
{
    assert(!parses(seq![0x3Au32, 0x6E, 0x6F, 0x74, 0x28, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65, 0x29])) by (compute_only);
}

/// `:not()` is invalid. §4.3: :not() takes a <complex-real-selector-list>, which is not forgiving: :not() is invalid.
pub proof fn lemma_example_unforgiving_not()
    ensures
        !parses(seq![0x3Au32, 0x6E, 0x6F, 0x74, 0x28, 0x29]),
{
    assert(!parses(seq![0x3Au32, 0x6E, 0x6F, 0x74, 0x28, 0x29])) by (compute_only);
}

/// `:is(p, 0)` matches node 5. §18.1: a forgiving list keeps the items that parse: :is(p, 0) still matches p.
pub proof fn lemma_example_forgiving_is_strict()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x69, 0x73, 0x28, 0x70, 0x2C, 0x20, 0x30, 0x29], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x3Au32, 0x69, 0x73, 0x28, 0x70, 0x2C, 0x20, 0x30, 0x29], 5)) by (compute_only);
}

} // verus!
