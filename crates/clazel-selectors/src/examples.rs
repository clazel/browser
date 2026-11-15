//! Concrete selectors on a concrete document, evaluated on the spec, each stating what the
//! standard's text says. They are the kill certificates of `mutations.json`: each mutation of
//! the spec makes one of these false. Kept apart from the theorems so that a mutant that
//! breaks one does not stop Verus before it checks a certificate.
//!
//! The document ([`doc`]): 0 the document, 1 `html`, 2 `body`, 3 `div id=x class="ab c"`
//! holding 4, a text node of two spaces, then 5 `p lang=EN`, 6 `a href=/`, 7 `p` and 8
//! `span`, the children of `body` in that order. Node 7 also has an attribute `k` in the XLink
//! namespace.

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

/// An attribute in the XLink namespace.
pub open spec fn xattr(name: Seq<u32>, value: Seq<u32>) -> Attr {
    Attr { namespace: Some(Namespace::XLink), prefix: Some(seq![0x78u32, 0x6C, 0x69, 0x6E, 0x6B]), local_name: name, value }
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
            node(element(seq![0x70u32], seq![xattr(seq![0x6Bu32], seq![0x76u32])]), Some(2usize), seq![]),
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

/// The serialization of the selector `source` parses to (empty if it is invalid).
pub open spec fn serialized(source: Seq<u32>) -> Seq<u32> {
    match parse_a_selector(source) {
        Some(list) => serialize_a_group_of_selectors(list),
        None => Seq::empty(),
    }
}

/// `a` and `b` are the same sequence, checked element by element (so that `compute_only` can
/// decide it).
pub open spec fn same_seq(a: Seq<u32>, b: Seq<u32>) -> bool {
    a.len() == b.len() && same_from(a, b, 0)
}

/// `a` and `b` agree from index `i` on, which is within both.
pub open spec fn same_from(a: Seq<u32>, b: Seq<u32>, i: int) -> bool
    decreases a.len() - i,
{
    if i < 0 || i >= a.len() || i >= b.len() {
        true
    } else {
        a[i] == b[i] && same_from(a, b, i + 1)
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

/// `*|p` matches node 5. §5.3: `*|E` is an E in any namespace, so `*|p` matches an HTML p.
pub proof fn lemma_example_star_pipe_ident()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x2Au32, 0x7C, 0x70], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x2Au32, 0x7C, 0x70], 5)) by (compute_only);
}

/// `|*` does not match node 5. §5.3: `|*` is any element without a namespace, which an HTML p is not.
pub proof fn lemma_example_pipe_star_no_namespace()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x7Cu32, 0x2A], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x7Cu32, 0x2A], 5)) by (compute_only);
}

/// `[*|k]` matches node 7. §6.4: `*|k` matches an attribute k "without regard to the attribute's namespace"; node 7 has k in the XLink namespace.
pub proof fn lemma_example_attr_any_namespace()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x2A, 0x7C, 0x6B, 0x5D], 7),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x2A, 0x7C, 0x6B, 0x5D], 7)) by (compute_only);
}

/// `[class~=c]` matches node 3. §6.1: `~=` needs the word c, and class="ab c" has it.
pub proof fn lemma_example_includes_parsed()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x7E, 0x3D, 0x63, 0x5D], 3),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x7E, 0x3D, 0x63, 0x5D], 3)) by (compute_only);
}

/// `[class^=ab]` matches node 3. §6.2: `^=` needs the value to begin with ab, and class="ab c" does.
pub proof fn lemma_example_prefix_parsed()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x5E, 0x3D, 0x61, 0x62, 0x5D], 3),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x5E, 0x3D, 0x61, 0x62, 0x5D], 3)) by (compute_only);
}

/// `[class$=" c"]` matches node 3. §6.2: `$=` needs the value to end with " c", and class="ab c" does.
pub proof fn lemma_example_suffix_parsed()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x24, 0x3D, 0x22, 0x20, 0x63, 0x22, 0x5D], 3),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x24, 0x3D, 0x22, 0x20, 0x63, 0x22, 0x5D], 3)) by (compute_only);
}

/// `[class*="b "]` matches node 3. §6.2: `*=` needs the substring "b ", which class="ab c" holds, but not as the whole value.
pub proof fn lemma_example_substring_parsed()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x2A, 0x3D, 0x22, 0x62, 0x20, 0x22, 0x5D], 3),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x63, 0x6C, 0x61, 0x73, 0x73, 0x2A, 0x3D, 0x22, 0x62, 0x20, 0x22, 0x5D], 3)) by (compute_only);
}

/// `[lang]` matches node 5. §6.1: `[att]` matches an element with the attribute att, whatever its value.
pub proof fn lemma_example_attr_presence()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x5D], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6C, 0x61, 0x6E, 0x67, 0x5D], 5)) by (compute_only);
}

/// `a:before` is valid. §3.6 and §18 `<legacy-pseudo-element-selector>`: `:before` is accepted for compatibility.
pub proof fn lemma_example_legacy_pseudo_element()
    ensures
        parses(seq![0x61u32, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65]),
{
    assert(parses(seq![0x61u32, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65])) by (compute_only);
}

/// `a::before` is valid. §18 `<pseudo-element-selector>`: `::before` is a pseudo-element.
pub proof fn lemma_example_double_colon_pseudo_element()
    ensures
        parses(seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65]),
{
    assert(parses(seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65])) by (compute_only);
}

/// `#1` is invalid. §18 `<id-selector>` is a `<hash-token>` whose type flag is "id"; `#1` is "unrestricted".
pub proof fn lemma_example_hash_needs_id_flag()
    ensures
        !parses(seq![0x23u32, 0x31]),
{
    assert(!parses(seq![0x23u32, 0x31])) by (compute_only);
}

/// `span` does not match node 5. §18 `<compound-selector>`: the type selector is part of the compound, so span matches only a span.
pub proof fn lemma_example_type_selector_kept()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x73u32, 0x70, 0x61, 0x6E], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x73u32, 0x70, 0x61, 0x6E], 5)) by (compute_only);
}

/// `.a*` is invalid. §18 `<complex-selector>`: "Whitespace is required between two `<complex-selector-unit>`s if the `<combinator>` between them is omitted", and a `*` cannot follow a class in a compound selector.
pub proof fn lemma_example_no_combinator_without_space()
    ensures
        !parses(seq![0x2Eu32, 0x61, 0x2A]),
{
    assert(!parses(seq![0x2Eu32, 0x61, 0x2A])) by (compute_only);
}

/// `a::before b` is invalid. §18 note: a pseudo-element is only valid at the end of the last compound selector.
pub proof fn lemma_example_pseudo_element_last()
    ensures
        !parses(seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65, 0x20, 0x62]),
{
    assert(!parses(seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65, 0x20, 0x62])) by (compute_only);
}

/// `p,span` matches node 8. §18 `<selector-list>`: the items are separated by a comma and each is a selector, so it matches a span.
pub proof fn lemma_example_list_second_item()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x70u32, 0x2C, 0x73, 0x70, 0x61, 0x6E], 8),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x70u32, 0x2C, 0x73, 0x70, 0x61, 0x6E], 8)) by (compute_only);
}

/// `a::before:hover` is valid. §18 note: the user action pseudo-classes are allowed after any pseudo-element.
pub proof fn lemma_example_hover_after_pseudo_element()
    ensures
        parses(seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65, 0x3A, 0x68, 0x6F, 0x76, 0x65, 0x72]),
{
    assert(parses(seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65, 0x3A, 0x68, 0x6F, 0x76, 0x65, 0x72])) by (compute_only);
}

/// `[k]` does not match node 7. §6.4: an attribute selector without a namespace component applies only to attributes without a namespace (`|k`), and node 7's k is in the XLink namespace.
pub proof fn lemma_example_attr_without_namespace()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6B, 0x5D], 7),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x6B, 0x5D], 7)) by (compute_only);
}

/// `[LANG]` matches node 5. HTML §4.16.2: the name part of an attribute selector is lowercased before it is compared with the names of an HTML element's attributes, so [LANG] matches lang.
pub proof fn lemma_example_attr_name_lowercased()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x4C, 0x41, 0x4E, 0x47, 0x5D], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x5Bu32, 0x4C, 0x41, 0x4E, 0x47, 0x5D], 5)) by (compute_only);
}

/// `p:last-of-type` matches node 7. §15.4.4: node 7 is the last p although a span follows it; only elements of its type count.
pub proof fn lemma_example_last_of_type_other_types()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x70u32, 0x3A, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65], 7),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x70u32, 0x3A, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65], 7)) by (compute_only);
}

/// `p#x` does not match node 5. §2.1: a compound selector matches an element only if all its simple selectors do; node 5 is a p but has no ID x.
pub proof fn lemma_example_compound_needs_all()
    ensures
        !matches(DocumentMode::NoQuirks, seq![0x70u32, 0x23, 0x78], 5),
{
    assert(!matches(DocumentMode::NoQuirks, seq![0x70u32, 0x23, 0x78], 5)) by (compute_only);
}

/// `p, span` matches node 5. §21.3: a selector list matches if any of its complex selectors does; node 5 is a p.
pub proof fn lemma_example_list_any_matches()
    ensures
        matches(DocumentMode::NoQuirks, seq![0x70u32, 0x2C, 0x20, 0x73, 0x70, 0x61, 0x6E], 5),
{
    assert(matches(DocumentMode::NoQuirks, seq![0x70u32, 0x2C, 0x20, 0x73, 0x70, 0x61, 0x6E], 5)) by (compute_only);
}

/// Adding 1 to a component at the limit stays at the limit. §17: "values higher than the limit must be clamped to that limit, and not overflow"; spec.rs takes the limit to be 2^32 - 1.
pub proof fn lemma_example_specificity_saturates()
    ensures
        add_specificity(Specificity { a: 0xFFFF_FFFF, b: 0xFFFF_FFFF, c: 0xFFFF_FFFF }, Specificity { a: 1, b: 1, c: 1 }) == (Specificity { a: 0xFFFF_FFFF, b: 0xFFFF_FFFF, c: 0xFFFF_FFFF }),
{
    assert(add_specificity(Specificity { a: 0xFFFF_FFFF, b: 0xFFFF_FFFF, c: 0xFFFF_FFFF }, Specificity { a: 1, b: 1, c: 1 }) == (Specificity { a: 0xFFFF_FFFF, b: 0xFFFF_FFFF, c: 0xFFFF_FFFF })) by (compute_only);
}

/// `:nth-child(99999999999)` serializes as `:nth-child(2147483647)`. spec.rs clamps `A` and `B` to the 32-bit signed range (CSS Values 4 §5.1).
pub proof fn lemma_example_clamp_above()
    ensures
        same_seq(serialized(seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x29]), seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x32, 0x31, 0x34, 0x37, 0x34, 0x38, 0x33, 0x36, 0x34, 0x37, 0x29]),
{
    assert(same_seq(serialized(seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x29]), seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x32, 0x31, 0x34, 0x37, 0x34, 0x38, 0x33, 0x36, 0x34, 0x37, 0x29])) by (compute_only);
}

/// `:nth-child(-99999999999)` serializes as `:nth-child(-2147483648)`. spec.rs clamps `A` and `B` to the 32-bit signed range (CSS Values 4 §5.1).
pub proof fn lemma_example_clamp_below()
    ensures
        same_seq(serialized(seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x2D, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x29]), seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x2D, 0x32, 0x31, 0x34, 0x37, 0x34, 0x38, 0x33, 0x36, 0x34, 0x38, 0x29]),
{
    assert(same_seq(serialized(seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x2D, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x29]), seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x2D, 0x32, 0x31, 0x34, 0x37, 0x34, 0x38, 0x33, 0x36, 0x34, 0x38, 0x29])) by (compute_only);
}

/// `.a\1f b` serializes as itself. CSSOM "serialize an identifier": U+001F is "escaped as code point": `\`, its code point in lowercase hexadecimal, and a space.
pub proof fn lemma_example_escape_control()
    ensures
        same_seq(serialized(seq![0x2Eu32, 0x61, 0x5C, 0x31, 0x66, 0x20, 0x62]), seq![0x2Eu32, 0x61, 0x5C, 0x31, 0x66, 0x20, 0x62]),
{
    assert(same_seq(serialized(seq![0x2Eu32, 0x61, 0x5C, 0x31, 0x66, 0x20, 0x62]), seq![0x2Eu32, 0x61, 0x5C, 0x31, 0x66, 0x20, 0x62])) by (compute_only);
}

/// The identifier "a", U+0000, "b" serializes as "a", U+FFFD, "b". CSSOM "serialize an identifier": U+0000 is U+FFFD.
pub proof fn lemma_example_identifier_nul()
    ensures
        same_seq(serialize_an_identifier(seq![0x61u32, 0x0, 0x62]), seq![0x61u32, 0xFFFD, 0x62]),
{
    assert(same_seq(serialize_an_identifier(seq![0x61u32, 0x0, 0x62]), seq![0x61u32, 0xFFFD, 0x62])) by (compute_only);
}

/// The identifier "1a" serializes as `\31 a`. CSSOM "serialize an identifier": a first character in 0-9 is escaped as code point.
pub proof fn lemma_example_identifier_first_digit()
    ensures
        same_seq(serialize_an_identifier(seq![0x31u32, 0x61]), seq![0x5Cu32, 0x33, 0x31, 0x20, 0x61]),
{
    assert(same_seq(serialize_an_identifier(seq![0x31u32, 0x61]), seq![0x5Cu32, 0x33, 0x31, 0x20, 0x61])) by (compute_only);
}

/// The identifier "-1" serializes as `-\31 `. CSSOM "serialize an identifier": a second character in 0-9 after a first "-" is escaped as code point.
pub proof fn lemma_example_identifier_dash_digit()
    ensures
        same_seq(serialize_an_identifier(seq![0x2Du32, 0x31]), seq![0x2Du32, 0x5C, 0x33, 0x31, 0x20]),
{
    assert(same_seq(serialize_an_identifier(seq![0x2Du32, 0x31]), seq![0x2Du32, 0x5C, 0x33, 0x31, 0x20])) by (compute_only);
}

/// The identifier "-" serializes as `\-`. CSSOM "serialize an identifier": a first "-" with no second character is escaped.
pub proof fn lemma_example_identifier_lone_dash()
    ensures
        same_seq(serialize_an_identifier(seq![0x2Du32]), seq![0x5Cu32, 0x2D]),
{
    assert(same_seq(serialize_an_identifier(seq![0x2Du32]), seq![0x5Cu32, 0x2D])) by (compute_only);
}

/// The identifier "a", U+007F serializes as `a\7f `. CSSOM "serialize an identifier": U+007F is escaped as code point.
pub proof fn lemma_example_identifier_del()
    ensures
        same_seq(serialize_an_identifier(seq![0x61u32, 0x7F]), seq![0x61u32, 0x5C, 0x37, 0x66, 0x20]),
{
    assert(same_seq(serialize_an_identifier(seq![0x61u32, 0x7F]), seq![0x61u32, 0x5C, 0x37, 0x66, 0x20])) by (compute_only);
}

/// The identifier "a b" serializes as `a\ b`. CSSOM "serialize an identifier": any other character is escaped, as "\" and itself.
pub proof fn lemma_example_identifier_punctuation()
    ensures
        same_seq(serialize_an_identifier(seq![0x61u32, 0x20, 0x62]), seq![0x61u32, 0x5C, 0x20, 0x62]),
{
    assert(same_seq(serialize_an_identifier(seq![0x61u32, 0x20, 0x62]), seq![0x61u32, 0x5C, 0x20, 0x62])) by (compute_only);
}

/// The string `\` serializes as `"\\"`. CSSOM "serialize a string": `"` and `\` are escaped as the character.
pub proof fn lemma_example_string_backslash()
    ensures
        same_seq(serialize_a_string(seq![0x5Cu32]), seq![0x22u32, 0x5C, 0x5C, 0x22]),
{
    assert(same_seq(serialize_a_string(seq![0x5Cu32]), seq![0x22u32, 0x5C, 0x5C, 0x22])) by (compute_only);
}

/// The string "a" serializes with both quotes. CSSOM "serialize a string": `"`, the characters, `"`.
pub proof fn lemma_example_string_closing_quote()
    ensures
        same_seq(serialize_a_string(seq![0x61u32]), seq![0x22u32, 0x61, 0x22]),
{
    assert(same_seq(serialize_a_string(seq![0x61u32]), seq![0x22u32, 0x61, 0x22])) by (compute_only);
}

/// The string U+007F serializes as `"\7f "`. CSSOM "serialize a string": U+007F is escaped as code point.
pub proof fn lemma_example_string_del()
    ensures
        same_seq(serialize_a_string(seq![0x7Fu32]), seq![0x22u32, 0x5C, 0x37, 0x66, 0x20, 0x22]),
{
    assert(same_seq(serialize_a_string(seq![0x7Fu32]), seq![0x22u32, 0x5C, 0x37, 0x66, 0x20, 0x22])) by (compute_only);
}

/// `[a|=b]` serializes as `[a|="b"]`. CSSOM "serialize an attribute selector": the matcher, then the value as a string.
pub proof fn lemma_example_serialize_dashmatch()
    ensures
        same_seq(serialized(seq![0x5Bu32, 0x61, 0x7C, 0x3D, 0x62, 0x5D]), seq![0x5Bu32, 0x61, 0x7C, 0x3D, 0x22, 0x62, 0x22, 0x5D]),
{
    assert(same_seq(serialized(seq![0x5Bu32, 0x61, 0x7C, 0x3D, 0x62, 0x5D]), seq![0x5Bu32, 0x61, 0x7C, 0x3D, 0x22, 0x62, 0x22, 0x5D])) by (compute_only);
}

/// `[a~=b]` serializes as `[a~="b"]`. CSSOM "serialize an attribute selector": the matcher, then the value as a string.
pub proof fn lemma_example_serialize_includes()
    ensures
        same_seq(serialized(seq![0x5Bu32, 0x61, 0x7E, 0x3D, 0x62, 0x5D]), seq![0x5Bu32, 0x61, 0x7E, 0x3D, 0x22, 0x62, 0x22, 0x5D]),
{
    assert(same_seq(serialized(seq![0x5Bu32, 0x61, 0x7E, 0x3D, 0x62, 0x5D]), seq![0x5Bu32, 0x61, 0x7E, 0x3D, 0x22, 0x62, 0x22, 0x5D])) by (compute_only);
}

/// `[a*=b]` serializes as `[a*="b"]`. CSSOM "serialize an attribute selector": the matcher, then the value as a string.
pub proof fn lemma_example_serialize_substring()
    ensures
        same_seq(serialized(seq![0x5Bu32, 0x61, 0x2A, 0x3D, 0x62, 0x5D]), seq![0x5Bu32, 0x61, 0x2A, 0x3D, 0x22, 0x62, 0x22, 0x5D]),
{
    assert(same_seq(serialized(seq![0x5Bu32, 0x61, 0x2A, 0x3D, 0x62, 0x5D]), seq![0x5Bu32, 0x61, 0x2A, 0x3D, 0x22, 0x62, 0x22, 0x5D])) by (compute_only);
}

/// `|a` serializes as `|a`. CSSOM "serialize a type selector": a prefix that maps to the null namespace appends "|".
pub proof fn lemma_example_serialize_no_namespace()
    ensures
        same_seq(serialized(seq![0x7Cu32, 0x61]), seq![0x7Cu32, 0x61]),
{
    assert(same_seq(serialized(seq![0x7Cu32, 0x61]), seq![0x7Cu32, 0x61])) by (compute_only);
}

/// `[*|a]` serializes as `[*|a]`. spec.rs keeps `*|` on attribute selectors, where it changes the meaning.
pub proof fn lemma_example_serialize_attr_any_namespace()
    ensures
        same_seq(serialized(seq![0x5Bu32, 0x2A, 0x7C, 0x61, 0x5D]), seq![0x5Bu32, 0x2A, 0x7C, 0x61, 0x5D]),
{
    assert(same_seq(serialized(seq![0x5Bu32, 0x2A, 0x7C, 0x61, 0x5D]), seq![0x5Bu32, 0x2A, 0x7C, 0x61, 0x5D])) by (compute_only);
}

/// `[a=b i]` serializes as `[a="b" i]`. CSSOM "serialize an attribute selector": the flag after a space.
pub proof fn lemma_example_serialize_flag_i()
    ensures
        same_seq(serialized(seq![0x5Bu32, 0x61, 0x3D, 0x62, 0x20, 0x69, 0x5D]), seq![0x5Bu32, 0x61, 0x3D, 0x22, 0x62, 0x22, 0x20, 0x69, 0x5D]),
{
    assert(same_seq(serialized(seq![0x5Bu32, 0x61, 0x3D, 0x62, 0x20, 0x69, 0x5D]), seq![0x5Bu32, 0x61, 0x3D, 0x22, 0x62, 0x22, 0x20, 0x69, 0x5D])) by (compute_only);
}

/// `[a=b s]` serializes as `[a="b" s]`. spec.rs writes the `s` flag as `s` (as engines do).
pub proof fn lemma_example_serialize_flag_s()
    ensures
        same_seq(serialized(seq![0x5Bu32, 0x61, 0x3D, 0x62, 0x20, 0x73, 0x5D]), seq![0x5Bu32, 0x61, 0x3D, 0x22, 0x62, 0x22, 0x20, 0x73, 0x5D]),
{
    assert(same_seq(serialized(seq![0x5Bu32, 0x61, 0x3D, 0x62, 0x20, 0x73, 0x5D]), seq![0x5Bu32, 0x61, 0x3D, 0x22, 0x62, 0x22, 0x20, 0x73, 0x5D])) by (compute_only);
}

/// `.a` serializes as `.a`. CSSOM "serialize a simple selector": a class selector is "." and the class as an identifier.
pub proof fn lemma_example_serialize_class()
    ensures
        same_seq(serialized(seq![0x2Eu32, 0x61]), seq![0x2Eu32, 0x61]),
{
    assert(same_seq(serialized(seq![0x2Eu32, 0x61]), seq![0x2Eu32, 0x61])) by (compute_only);
}

/// `#a` serializes as `#a`. CSSOM "serialize a simple selector": an ID selector is "#" and the ID as an identifier.
pub proof fn lemma_example_serialize_id()
    ensures
        same_seq(serialized(seq![0x23u32, 0x61]), seq![0x23u32, 0x61]),
{
    assert(same_seq(serialized(seq![0x23u32, 0x61]), seq![0x23u32, 0x61])) by (compute_only);
}

/// `:nth-child(2n+1)` serializes as itself. CSSOM: the name, "(", the <an+b> serialized, ")".
pub proof fn lemma_example_serialize_nth()
    ensures
        same_seq(serialized(seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x32, 0x6E, 0x2B, 0x31, 0x29]), seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x32, 0x6E, 0x2B, 0x31, 0x29]),
{
    assert(same_seq(serialized(seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x32, 0x6E, 0x2B, 0x31, 0x29]), seq![0x3Au32, 0x6E, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64, 0x28, 0x32, 0x6E, 0x2B, 0x31, 0x29])) by (compute_only);
}

/// `a>b` serializes as `a > b`. CSSOM "serialize a selector": a space, the combinator, a space.
pub proof fn lemma_example_serialize_child()
    ensures
        same_seq(serialized(seq![0x61u32, 0x3E, 0x62]), seq![0x61u32, 0x20, 0x3E, 0x20, 0x62]),
{
    assert(same_seq(serialized(seq![0x61u32, 0x3E, 0x62]), seq![0x61u32, 0x20, 0x3E, 0x20, 0x62])) by (compute_only);
}

/// `a+b` serializes as `a + b`. CSSOM "serialize a selector": a space, the combinator, a space.
pub proof fn lemma_example_serialize_plus()
    ensures
        same_seq(serialized(seq![0x61u32, 0x2B, 0x62]), seq![0x61u32, 0x20, 0x2B, 0x20, 0x62]),
{
    assert(same_seq(serialized(seq![0x61u32, 0x2B, 0x62]), seq![0x61u32, 0x20, 0x2B, 0x20, 0x62])) by (compute_only);
}

/// `a~b` serializes as `a ~ b`. CSSOM "serialize a selector": a space, the combinator, a space.
pub proof fn lemma_example_serialize_tilde()
    ensures
        same_seq(serialized(seq![0x61u32, 0x7E, 0x62]), seq![0x61u32, 0x20, 0x7E, 0x20, 0x62]),
{
    assert(same_seq(serialized(seq![0x61u32, 0x7E, 0x62]), seq![0x61u32, 0x20, 0x7E, 0x20, 0x62])) by (compute_only);
}

/// `a   b` serializes as `a b`. CSSOM "serialize a selector": the descendant combinator is a single space.
pub proof fn lemma_example_serialize_descendant()
    ensures
        same_seq(serialized(seq![0x61u32, 0x20, 0x20, 0x20, 0x62]), seq![0x61u32, 0x20, 0x62]),
{
    assert(same_seq(serialized(seq![0x61u32, 0x20, 0x20, 0x20, 0x62]), seq![0x61u32, 0x20, 0x62])) by (compute_only);
}

/// `a,b` serializes as `a, b`. CSSOM "serialize a group of selectors": comma-separated, with a space.
pub proof fn lemma_example_serialize_list()
    ensures
        same_seq(serialized(seq![0x61u32, 0x2C, 0x62]), seq![0x61u32, 0x2C, 0x20, 0x62]),
{
    assert(same_seq(serialized(seq![0x61u32, 0x2C, 0x62]), seq![0x61u32, 0x2C, 0x20, 0x62])) by (compute_only);
}

/// `*|*.a` serializes as `.a`. CSSOM "serialize a selector": a universal selector in a compound with others is left out when its namespace is not the null one.
pub proof fn lemma_example_serialize_omits_universal()
    ensures
        same_seq(serialized(seq![0x2Au32, 0x7C, 0x2A, 0x2E, 0x61]), seq![0x2Eu32, 0x61]),
{
    assert(same_seq(serialized(seq![0x2Au32, 0x7C, 0x2A, 0x2E, 0x61]), seq![0x2Eu32, 0x61])) by (compute_only);
}

/// `|*.a` serializes as `|*.a`. CSSOM: a universal selector whose prefix is the null namespace is kept.
pub proof fn lemma_example_serialize_keeps_no_namespace_universal()
    ensures
        same_seq(serialized(seq![0x7Cu32, 0x2A, 0x2E, 0x61]), seq![0x7Cu32, 0x2A, 0x2E, 0x61]),
{
    assert(same_seq(serialized(seq![0x7Cu32, 0x2A, 0x2E, 0x61]), seq![0x7Cu32, 0x2A, 0x2E, 0x61])) by (compute_only);
}

/// `*` serializes as `*`. CSSOM "serialize a selector" step 1: "If there is only one simple selector in the compound selectors which is a universal selector, append the result of serializing the universal selector."
pub proof fn lemma_example_serialize_lone_universal()
    ensures
        same_seq(serialized(seq![0x2Au32]), seq![0x2Au32]),
{
    assert(same_seq(serialized(seq![0x2Au32]), seq![0x2Au32])) by (compute_only);
}

/// `:is(a)` serializes as itself. spec.rs: :is() is serialized as :not() is, a group of selectors.
pub proof fn lemma_example_serialize_is()
    ensures
        same_seq(serialized(seq![0x3Au32, 0x69, 0x73, 0x28, 0x61, 0x29]), seq![0x3Au32, 0x69, 0x73, 0x28, 0x61, 0x29]),
{
    assert(same_seq(serialized(seq![0x3Au32, 0x69, 0x73, 0x28, 0x61, 0x29]), seq![0x3Au32, 0x69, 0x73, 0x28, 0x61, 0x29])) by (compute_only);
}

/// `:where(a)` serializes as itself. spec.rs: :where() is serialized as :not() is, a group of selectors.
pub proof fn lemma_example_serialize_where()
    ensures
        same_seq(serialized(seq![0x3Au32, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28, 0x61, 0x29]), seq![0x3Au32, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28, 0x61, 0x29]),
{
    assert(same_seq(serialized(seq![0x3Au32, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28, 0x61, 0x29]), seq![0x3Au32, 0x77, 0x68, 0x65, 0x72, 0x65, 0x28, 0x61, 0x29])) by (compute_only);
}

/// `:not(a)` serializes as itself. CSSOM "serialize a simple selector": ":not(", the argument as a group of selectors, ")".
pub proof fn lemma_example_serialize_not()
    ensures
        same_seq(serialized(seq![0x3Au32, 0x6E, 0x6F, 0x74, 0x28, 0x61, 0x29]), seq![0x3Au32, 0x6E, 0x6F, 0x74, 0x28, 0x61, 0x29]),
{
    assert(same_seq(serialized(seq![0x3Au32, 0x6E, 0x6F, 0x74, 0x28, 0x61, 0x29]), seq![0x3Au32, 0x6E, 0x6F, 0x74, 0x28, 0x61, 0x29])) by (compute_only);
}

/// `a::before` serializes as itself. CSSOM "serialize a selector": "::" followed by the name of the pseudo-element.
pub proof fn lemma_example_serialize_pseudo_element()
    ensures
        same_seq(serialized(seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65]), seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65]),
{
    assert(same_seq(serialized(seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65]), seq![0x61u32, 0x3A, 0x3A, 0x62, 0x65, 0x66, 0x6F, 0x72, 0x65])) by (compute_only);
}

/// `E` serializes as `E`. CSSOM "serialize a type selector": the element name as an identifier.
pub proof fn lemma_example_serialize_type()
    ensures
        same_seq(serialized(seq![0x45u32]), seq![0x45u32]),
{
    assert(same_seq(serialized(seq![0x45u32]), seq![0x45u32])) by (compute_only);
}

/// `a:hover` serializes as itself. CSSOM "serialize a simple selector": ":" followed by the name of the pseudo-class.
pub proof fn lemma_example_serialize_hover()
    ensures
        same_seq(serialized(seq![0x61u32, 0x3A, 0x68, 0x6F, 0x76, 0x65, 0x72]), seq![0x61u32, 0x3A, 0x68, 0x6F, 0x76, 0x65, 0x72]),
{
    assert(same_seq(serialized(seq![0x61u32, 0x3A, 0x68, 0x6F, 0x76, 0x65, 0x72]), seq![0x61u32, 0x3A, 0x68, 0x6F, 0x76, 0x65, 0x72])) by (compute_only);
}

} // verus!
