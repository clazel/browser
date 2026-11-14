//! What matching asks of one element, read from a `clazel-dom` arena through its public
//! readers only, and proven equal to the spec's functions.

use super::exec_strings::*;
#[allow(unused_imports)]
use super::spec::*;
use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`is_element`].
pub fn element(arena: &Arena, x: usize) -> (r: bool)
    ensures
        r == is_element(arena@, x),
{
    x < arena.len() && matches!(arena.kind(x), ExecKind::Element { .. })
}

/// [`in_quirks_mode`].
pub fn quirks(arena: &Arena) -> (r: bool)
    ensures
        r == in_quirks_mode(arena@),
{
    if arena.is_empty() {
        return false;
    }
    matches!(arena.kind(0), ExecKind::Document { mode: DocumentMode::Quirks, .. })
}

/// Two namespaces are the same.
pub fn same_namespace(a: &Option<Namespace>, b: &Option<Namespace>) -> (r: bool)
    ensures
        r == (*a == *b),
{
    matches!(
        (a, b),
        (None, None) | (Some(Namespace::Html), Some(Namespace::Html)) | (
            Some(Namespace::MathMl),
            Some(Namespace::MathMl),
        ) | (Some(Namespace::Svg), Some(Namespace::Svg)) | (
            Some(Namespace::XLink),
            Some(Namespace::XLink),
        ) | (Some(Namespace::Xml), Some(Namespace::Xml)) | (
            Some(Namespace::Xmlns),
            Some(Namespace::Xmlns),
        )
    )
}

/// True for the HTML namespace.
pub fn is_html(ns: &Option<Namespace>) -> (r: bool)
    ensures
        r == (*ns == Some(Namespace::Html)),
{
    matches!(ns, Some(Namespace::Html))
}

/// [`plain_attribute_value`] keeps the first value it finds.
proof fn lemma_plain_keeps(doc: Document, x: NodeId, name: Seq<u32>, k: int, m: int)
    requires
        k <= m <= attributes_of(doc, x).len(),
        plain_attribute_value(doc, x, name, k) is Some,
    ensures
        plain_attribute_value(doc, x, name, m) == plain_attribute_value(doc, x, name, k),
    decreases m - k,
{
    if m > k {
        lemma_plain_keeps(doc, x, name, k, m - 1);
    }
}

/// The index of the first attribute with no namespace and the local name `name`, which is
/// [`get_attribute`].
pub fn find_attribute(attrs: &[ExecAttr], name: &[u32], Ghost(doc): Ghost<Document>, Ghost(x): Ghost<NodeId>) -> (r: Option<usize>)
    requires
        clazel_dom::exec::attrs_view(attrs@) == attributes_of(doc, x),
    ensures
        match r {
            Some(i) => i < attrs.len() && get_attribute(doc, x, name@) == Some(attrs@[i as int].value@),
            None => get_attribute(doc, x, name@) is None,
        },
{
    let mut i: usize = 0;
    while i < attrs.len()
        invariant
            i <= attrs.len(),
            clazel_dom::exec::attrs_view(attrs@) == attributes_of(doc, x),
            plain_attribute_value(doc, x, name@, i as int) is None,
        decreases attrs.len() - i,
    {
        let a = super::exec_types::item(attrs, i);
        proof {
            assert(clazel_dom::exec::attrs_view(attrs@)[i as int] == attrs@[i as int]@);
        }
        if a.namespace.is_none() && same(a.local_name.as_slice(), name) {
            proof {
                assert(plain_attribute_value(doc, x, name@, i + 1) == Some(attrs@[i as int].value@));
                lemma_plain_keeps(doc, x, name@, i + 1, attrs.len() as int);
            }
            return Some(i);
        }
        i = i.saturating_add(1);
    }
    None
}

/// [`has_id`].
pub fn id_matches(attrs: &[ExecAttr], name: &[u32], quirks_mode: bool, Ghost(doc): Ghost<Document>, Ghost(x): Ghost<NodeId>) -> (r: bool)
    requires
        clazel_dom::exec::attrs_view(attrs@) == attributes_of(doc, x),
        quirks_mode == in_quirks_mode(doc),
    ensures
        r == has_id(doc, x, name@),
{
    match find_attribute(attrs, &[0x69, 0x64], Ghost(doc), Ghost(x)) {
        None => {
            proof {
                assert(str_id() =~= seq![0x69u32, 0x64]);
            }
            false
        },
        Some(i) => {
            proof {
                assert(str_id() =~= seq![0x69u32, 0x64]);
            }
            let value = super::exec_types::item(attrs, i).value.as_slice();
            if quirks_mode {
                let a = lowered(value);
                let b = lowered(name);
                same(a.as_slice(), b.as_slice())
            } else {
                same(value, name)
            }
        },
    }
}

/// [`has_class`].
pub fn class_matches(attrs: &[ExecAttr], name: &[u32], quirks_mode: bool, Ghost(doc): Ghost<Document>, Ghost(x): Ghost<NodeId>) -> (r: bool)
    requires
        clazel_dom::exec::attrs_view(attrs@) == attributes_of(doc, x),
        quirks_mode == in_quirks_mode(doc),
    ensures
        r == has_class(doc, x, name@),
{
    proof {
        assert(str_class() =~= seq![0x63u32, 0x6C, 0x61, 0x73, 0x73]);
    }
    match find_attribute(attrs, &[0x63, 0x6C, 0x61, 0x73, 0x73], Ghost(doc), Ghost(x)) {
        None => false,
        Some(i) => {
            let value = super::exec_types::item(attrs, i).value.as_slice();
            if quirks_mode {
                let a = lowered(value);
                let b = lowered(name);
                one_of_the_words(a.as_slice(), b.as_slice())
            } else {
                one_of_the_words(value, name)
            }
        },
    }
}

/// [`names_attribute`], with `html` saying whether the element is an HTML element.
fn names(ns: NsPrefix, name: &[u32], attr: &ExecAttr, html: bool, Ghost(doc): Ghost<Document>, Ghost(x): Ghost<NodeId>) -> (r: bool)
    requires
        html == is_html_element(doc, x),
    ensures
        r == names_attribute(doc, x, ns, name@, attr@),
{
    let ns_ok = match ns {
        NsPrefix::Any => true,
        _ => attr.namespace.is_none(),
    };
    let name_ok = if html && attr.namespace.is_none() {
        lowered_is(name, attr.local_name.as_slice())
    } else {
        same(name, attr.local_name.as_slice())
    };
    ns_ok && name_ok
}

/// [`attribute_passes`].
fn passes(attr: &ExecAttr, test: &Option<super::exec_types::ExecAttrTest>, html: bool, Ghost(doc): Ghost<Document>, Ghost(x): Ghost<NodeId>) -> (r: bool)
    requires
        html == is_html_element(doc, x),
    ensures
        r == attribute_passes(doc, x, attr@, super::exec_types::view_test(*test)),
{
    match test {
        None => true,
        Some(t) => {
            let insensitive = match t.flag {
                Some(CaseFlag::I) => true,
                Some(CaseFlag::S) => false,
                None => html && attr.namespace.is_none() && case_insensitive_name(
                    attr.local_name.as_slice(),
                ),
            };
            if insensitive {
                let v = lowered(attr.value.as_slice());
                let s = lowered(t.value.as_slice());
                value_test(t.matcher, v.as_slice(), s.as_slice())
            } else {
                value_test(t.matcher, attr.value.as_slice(), t.value.as_slice())
            }
        },
    }
}

/// [`some_attribute`] over all the attributes.
pub fn attribute_matches(
    attrs: &[ExecAttr],
    ns: NsPrefix,
    name: &[u32],
    test: &Option<super::exec_types::ExecAttrTest>,
    html: bool,
    Ghost(doc): Ghost<Document>,
    Ghost(x): Ghost<NodeId>,
) -> (r: bool)
    requires
        clazel_dom::exec::attrs_view(attrs@) == attributes_of(doc, x),
        html == is_html_element(doc, x),
    ensures
        r == some_attribute(
            doc,
            x,
            ns,
            name@,
            super::exec_types::view_test(*test),
            attributes_of(doc, x).len() as int,
        ),
{
    let mut i: usize = 0;
    let mut found = false;
    while i < attrs.len()
        invariant
            i <= attrs.len(),
            clazel_dom::exec::attrs_view(attrs@) == attributes_of(doc, x),
            html == is_html_element(doc, x),
            found == some_attribute(doc, x, ns, name@, super::exec_types::view_test(*test), i as int),
        decreases attrs.len() - i,
    {
        let a = super::exec_types::item(attrs, i);
        proof {
            assert(clazel_dom::exec::attrs_view(attrs@)[i as int] == attrs@[i as int]@);
        }
        let here = names(ns, name, a, html, Ghost(doc), Ghost(x)) && passes(
            a,
            test,
            html,
            Ghost(doc),
            Ghost(x),
        );
        found = here || found;
        i = i.saturating_add(1);
    }
    found
}

/// [`is_hyperlink`].
pub fn hyperlink(arena: &Arena, x: usize) -> (r: bool)
    requires
        x < arena@.nodes.len(),
    ensures
        r == is_hyperlink(arena@, x),
{
    match arena.kind(x) {
        ExecKind::Element { namespace, local_name, attributes, .. } => {
            if !is_html(namespace) {
                return false;
            }
            let name = local_name.as_slice();
            let a_name: [u32; 1] = [0x61];
            let area_name: [u32; 4] = [0x61, 0x72, 0x65, 0x61];
            proof {
                assert(a_name@ =~= seq![0x61u32]);
                assert(area_name@ =~= seq![0x61u32, 0x72, 0x65, 0x61]);
            }
            if !(same(name, a_name.as_slice()) || same(name, area_name.as_slice())) {
                return false;
            }
            proof {
                assert(str_href() =~= seq![0x68u32, 0x72, 0x65, 0x66]);
            }
            find_attribute(attributes, &[0x68, 0x72, 0x65, 0x66], Ghost(arena@), Ghost(x)).is_some()
        },
        _ => false,
    }
}

/// The `:root` test.
pub fn root(arena: &Arena, x: usize) -> (r: bool)
    requires
        x < arena@.nodes.len(),
    ensures
        r == pseudo_class_matches(arena@, PseudoClass::Root, x),
{
    match arena.parent(x) {
        Some(p) => p < arena.len() && matches!(arena.kind(p), ExecKind::Document { .. }),
        None => false,
    }
}

/// The `:empty` test.
pub fn empty(arena: &Arena, x: usize) -> (r: bool)
    requires
        x < arena@.nodes.len(),
    ensures
        r == pseudo_class_matches(arena@, PseudoClass::Empty, x),
{
    let kids = arena.children(x);
    let ghost doc = arena@;
    let mut i: usize = 0;
    while i < kids.len()
        invariant
            i <= kids.len(),
            doc == arena@,
            kids@ == children_of(doc, x),
            empty_up_to(doc, kids@, i as int),
        decreases kids.len() - i,
    {
        let child = *super::exec_types::item(kids, i);
        if child < arena.len() {
            match arena.kind(child) {
                ExecKind::Element { .. } => {
                    proof {
                        lemma_empty_stops(doc, kids@, i as int, kids.len() as int);
                    }
                    return false;
                },
                ExecKind::Text { data } if !all_white(data.as_slice()) => {
                    proof {
                        lemma_empty_stops(doc, kids@, i as int, kids.len() as int);
                    }
                    return false;
                },
                _ => {},
            }
        }
        i = i.saturating_add(1);
    }
    true
}

/// A child that affects emptiness at `k` makes [`empty_up_to`] false from `k + 1` on.
proof fn lemma_empty_stops(doc: Document, kids: Seq<NodeId>, k: int, m: int)
    requires
        0 <= k < m <= kids.len(),
        !empty_up_to(doc, kids, k + 1),
    ensures
        !empty_up_to(doc, kids, m),
    decreases m - k,
{
    if m > k + 1 {
        lemma_empty_stops(doc, kids, k, m - 1);
    }
}

/// [`counts`].
fn counted(arena: &Arena, x: usize, y: usize, of_type: bool) -> (r: bool)
    requires
        x < arena@.nodes.len(),
    ensures
        r == counts(arena@, x, y, of_type),
{
    if y >= arena.len() {
        return false;
    }
    match arena.kind(y) {
        ExecKind::Element { namespace: ny, local_name: ly, .. } => {
            if !of_type {
                return true;
            }
            match arena.kind(x) {
                ExecKind::Element { namespace: nx, local_name: lx, .. } => same_namespace(nx, ny)
                    && same(lx.as_slice(), ly.as_slice()),
                _ => {
                    // namespace_of and local_name_of of a non-element are null and empty.
                    proof {
                        if ly@.len() == 0 {
                            assert(ly@ =~= Seq::<u32>::empty());
                        }
                    }
                    ny.is_none() && ly.is_empty()
                },
            }
        },
        _ => false,
    }
}

/// [`child_index`], which is at most the number of siblings and one.
pub fn index_among_siblings(arena: &Arena, x: usize, of_type: bool, from_end: bool) -> (r: u128)
    requires
        x < arena@.nodes.len(),
    ensures
        r as int == child_index(arena@, x, of_type, from_end),
        r <= usize::MAX as u128 + 1,
{
    let ghost doc = arena@;
    let ghost sibs = inclusive_siblings(doc, x);
    let ghost j = sibling_index(doc, x);
    let p = match arena.parent(x) {
        Some(p) => p,
        None => {
            // Inclusive siblings are x alone, at index 0.
            proof {
                assert(sibs == seq![x]);
                assert(clazel_dom::spec::index_of(seq![x], x) == 0);
                assert(count_before(doc, x, sibs, 0, of_type) == 0);
                assert(count_from(doc, x, sibs, 2, of_type) == 0);
                assert(count_from(doc, x, sibs, 1, of_type) == 0);
            }
            return 1;
        },
    };
    let kids: &[usize] = if p < arena.len() {
        arena.children(p)
    } else {
        &[]
    };
    proof {
        assert(kids@ == sibs);
    }
    let found = clazel_dom::exec::find(kids, x);
    let mut count: u128 = 0;
    if !from_end {
        let end = found.unwrap_or_default();
        let mut i: usize = 0;
        while i < end
            invariant
                i <= end <= kids.len(),
                doc == arena@,
                kids@ == sibs,
                x < doc.nodes.len(),
                count as nat == count_before(doc, x, sibs, i as int, of_type),
                count <= i,
            decreases end - i,
        {
            if counted(arena, x, *super::exec_types::item(kids, i), of_type) {
                count = count.saturating_add(1);
            }
            i = i.saturating_add(1);
        }
        proof {
            if found is None {
                assert(j == -1);
            }
        }
    } else {
        let start = match found {
            Some(i) => i.saturating_add(1),
            None => 0,
        };
        let mut i: usize = kids.len();
        proof {
            assert(count_from(doc, x, sibs, kids.len() as int, of_type) == 0);
        }
        while i > start
            invariant
                start <= i <= kids.len(),
                doc == arena@,
                kids@ == sibs,
                x < doc.nodes.len(),
                count as nat == count_from(doc, x, sibs, i as int, of_type),
                count <= kids.len() - i,
            decreases i,
        {
            i = i.saturating_sub(1);
            if counted(arena, x, *super::exec_types::item(kids, i), of_type) {
                count = count.saturating_add(1);
            }
        }
        proof {
            if found is None {
                assert(j == -1);
            }
        }
    }
    count.saturating_add(1)
}

/// [`nth_index_matches`].
pub fn nth(a: i32, b: i32, i: u128) -> (r: bool)
    requires
        i <= usize::MAX as u128 + 1,
    ensures
        r == nth_index_matches(a as int, b as int, i as int),
{
    let ai = a as i128;
    let bi = b as i128;
    let ii = i as i128;
    if ai == 0 {
        ii == bi
    } else if ai > 0 {
        match ii.checked_sub(bi) {
            Some(d) if d >= 0 => (d as u128).is_multiple_of(ai as u128),
            _ => false,
        }
    } else {
        match (bi.checked_sub(ii), 0i128.checked_sub(ai)) {
            (Some(d), Some(m)) if d >= 0 => (d as u128).is_multiple_of(m as u128),
            _ => false,
        }
    }
}

} // verus!
