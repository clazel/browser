//! Strings and attributes: the independent transcription's matching of attribute values, IDs and
//! classes is equal to the spec's ([`super::independent_match`] uses these).

#[cfg(verus_only)]
use super::independent::*;
#[cfg(verus_only)]
use super::independent_equivalence::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The lower case of a code point is the same in both.
pub proof fn lemma_lower_same(c: u32)
    ensures
        i_lower(c) == ascii_lowercase(c),
{
}

/// The lower case of a string is the same in both.
pub proof fn lemma_lowercase_same(s: Seq<u32>)
    ensures
        i_lowercase(s) == to_ascii_lowercase(s),
{
    assert forall|k: int| 0 <= k < s.len() implies i_lowercase(s)[k] == to_ascii_lowercase(s)[k] by {}
    assert(i_lowercase(s) =~= to_ascii_lowercase(s));
}

/// Lower-casing keeps the length and each code point's lower case.
pub proof fn lemma_lowercase_index(s: Seq<u32>, k: int)
    requires
        0 <= k < s.len(),
    ensures
        i_lowercase(s).len() == s.len(),
        i_lowercase(s)[k] == i_lower(s[k]),
{
}

/// White space has no case, and no letter lower-cases to it.
pub proof fn lemma_white_lower(c: u32)
    ensures
        i_white(i_lower(c)) == i_white(c),
        i_white(c) == is_selector_whitespace(c),
{
}

/// ASCII case-insensitive equality is equality of the lower cases.
pub proof fn lemma_ci_eq_lower(a: Seq<u32>, b: Seq<u32>)
    ensures
        i_ci_eq(a, b) <==> i_lowercase(a) == i_lowercase(b),
{
    if i_ci_eq(a, b) {
        assert(i_lowercase(a) =~= i_lowercase(b));
    }
    assert(i_lowercase(a).len() == a.len());
    assert(i_lowercase(b).len() == b.len());
    if i_lowercase(a) == i_lowercase(b) {
        assert(a.len() == b.len());
        assert forall|k: int| 0 <= k < a.len() implies i_lower(#[trigger] a[k]) == i_lower(b[k]) by {
            assert(i_lowercase(a)[k] == i_lowercase(b)[k]);
        }
    }
}

/// A string as a case flag compares it: lower-cased if insensitive.
pub open spec fn fold(ci: bool, s: Seq<u32>) -> Seq<u32> {
    if ci {
        i_lowercase(s)
    } else {
        s
    }
}

/// Two strings are the same as a flag says exactly when their folds are equal.
pub proof fn lemma_same_fold(ci: bool, a: Seq<u32>, b: Seq<u32>)
    ensures
        i_same(ci, a, b) <==> fold(ci, a) == fold(ci, b),
{
    lemma_ci_eq_lower(a, b);
}

/// A part of a string, lower-cased, is the same part of the lower-cased string.
pub proof fn lemma_lower_sub(s: Seq<u32>, a: int, b: int)
    requires
        0 <= a <= b <= s.len(),
    ensures
        i_lowercase(s.subrange(a, b)) == i_lowercase(s).subrange(a, b),
{
    assert(i_lowercase(s.subrange(a, b)) =~= i_lowercase(s).subrange(a, b));
}

// ------------------------------------------------------------------------------------
// Words
// ------------------------------------------------------------------------------------

/// "Has no white space from `i` on", as the spec recurses, is each code point being none.
pub proof fn lemma_no_white_iff(s: Seq<u32>, i: int)
    requires
        0 <= i,
    ensures
        no_whitespace_from(s, i) <==> forall|k: int| i <= k < s.len() ==> !i_white(#[trigger] s[k]),
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_no_white_iff(s, i + 1);
        lemma_white_lower(s[i]);
    }
}

/// The spec's search for a word, from the last position down, is a witness.
pub proof fn lemma_word_up_to_iff(v: Seq<u32>, s: Seq<u32>, i: int)
    ensures
        word_up_to(v, s, i) <==> exists|i2: int|
            0 <= i2 <= i && occurs_at(v, s, i2) && (i2 == 0 || is_selector_whitespace(v[i2 - 1]))
                && (i2 + s.len() == v.len() || is_selector_whitespace(v[i2 + s.len()])),
    decreases i + 1,
{
    if i >= 0 {
        lemma_word_up_to_iff(v, s, i - 1);
        if exists|i2: int|
            0 <= i2 <= i && occurs_at(v, s, i2) && (i2 == 0 || is_selector_whitespace(v[i2 - 1]))
                && (i2 + s.len() == v.len() || is_selector_whitespace(v[i2 + s.len()])) {
            let i2 = choose|i2: int|
                0 <= i2 <= i && occurs_at(v, s, i2) && (i2 == 0 || is_selector_whitespace(v[i2 - 1]))
                    && (i2 + s.len() == v.len() || is_selector_whitespace(v[i2 + s.len()]));
            if i2 < i {
                assert(0 <= i2 <= i - 1);
            }
        }
    }
}

/// The spec's "one of the words" is the transcription's, on strings compared as they are.
pub proof fn lemma_words_plain(v: Seq<u32>, s: Seq<u32>)
    ensures
        i_has_word(false, v, s) <==> is_one_of_the_words(v, s),
{
    lemma_word_up_to_iff(v, s, v.len() - s.len());
    lemma_no_white_iff(s, 0);
    if is_one_of_the_words(v, s) {
        let i2 = choose|i2: int|
            0 <= i2 <= v.len() - s.len() && occurs_at(v, s, i2) && (i2 == 0 || is_selector_whitespace(v[i2 - 1]))
                && (i2 + s.len() == v.len() || is_selector_whitespace(v[i2 + s.len()]));
        let j = i2 + s.len();
        assert(v.subrange(i2, j) == s);
        assert forall|k: int| i2 <= k < j implies !i_white(#[trigger] v[k]) by {
            assert(v.subrange(i2, j)[k - i2] == s[k - i2]);
            assert(!i_white(s[k - i2]));
        }
        assert(i_word(v, i2, j));
    }
    if i_has_word(false, v, s) {
        let (i, j) = choose|i: int, j: int| i_word(v, i, j) && v.subrange(i, j) == s;
        assert(s.len() == j - i);
        assert forall|k: int| 0 <= k < s.len() implies !i_white(#[trigger] s[k]) by {
            assert(v.subrange(i, j)[k] == v[i + k]);
        }
        assert(occurs_at(v, s, i));
        assert(0 <= i <= v.len() - s.len());
    }
}

/// Words, compared as a flag says: the folds, compared as they are.
pub proof fn lemma_has_word_fold(ci: bool, v: Seq<u32>, w: Seq<u32>)
    ensures
        i_has_word(ci, v, w) <==> i_has_word(false, fold(ci, v), fold(ci, w)),
{
    if ci {
        let lv = i_lowercase(v);
        // The same word boundaries, since the lower case of white space is itself and no other
        // code point's is.
        assert forall|i: int, j: int| i_word(v, i, j) <==> i_word(lv, i, j) by {
            if 0 <= i < j <= v.len() {
                assert forall|k: int| i <= k < j implies (!i_white(#[trigger] v[k])) <==> !i_white(lv[k]) by {
                    lemma_white_lower(v[k]);
                }
                if i > 0 {
                    lemma_white_lower(v[i - 1]);
                }
                if j < v.len() {
                    lemma_white_lower(v[j]);
                }
            }
        }
        if i_has_word(true, v, w) {
            let (i, j) = choose|i: int, j: int| i_word(v, i, j) && i_same(true, v.subrange(i, j), w);
            lemma_lower_sub(v, i, j);
            lemma_ci_eq_lower(v.subrange(i, j), w);
            assert(i_word(lv, i, j));
            assert(lv.subrange(i, j) == i_lowercase(w));
        }
        if i_has_word(false, lv, i_lowercase(w)) {
            let (i, j) = choose|i: int, j: int| i_word(lv, i, j) && lv.subrange(i, j) == i_lowercase(w);
            lemma_lower_sub(v, i, j);
            lemma_ci_eq_lower(v.subrange(i, j), w);
            assert(i_word(v, i, j));
            assert(i_same(true, v.subrange(i, j), w));
        }
    }
}

// ------------------------------------------------------------------------------------
// Attribute values
// ------------------------------------------------------------------------------------

/// The spec's search for an occurrence is a witness.
pub proof fn lemma_occurs_up_to_iff(v: Seq<u32>, s: Seq<u32>, i: int)
    ensures
        occurs_up_to(v, s, i) <==> exists|i2: int| 0 <= i2 <= i && occurs_at(v, s, i2),
    decreases i + 1,
{
    if i >= 0 {
        lemma_occurs_up_to_iff(v, s, i - 1);
        if exists|i2: int| 0 <= i2 <= i && occurs_at(v, s, i2) {
            let i2 = choose|i2: int| 0 <= i2 <= i && occurs_at(v, s, i2);
            if i2 < i {
                assert(0 <= i2 <= i - 1);
            }
        }
    }
}

/// Matching a value, compared as it is, is the spec's.
pub proof fn lemma_value_plain(m: AttrMatcher, op: IAttrOp, v: Seq<u32>, s: Seq<u32>)
    requires
        rel_matcher(m, op),
    ensures
        i_value_matches(op, false, v, s) == value_matches(m, v, s),
{
    match m {
        AttrMatcher::Includes => {
            lemma_words_plain(v, s);
        },
        AttrMatcher::DashMatch => {},
        AttrMatcher::Substring => {
            if s.len() > 0 {
                lemma_occurs_up_to_iff(v, s, v.len() - s.len());
                if exists|i: int| 0 <= i && i + s.len() <= v.len() && #[trigger] v.subrange(i, i + s.len()) == s {
                    let i = choose|i: int| 0 <= i && i + s.len() <= v.len() && #[trigger] v.subrange(i, i + s.len()) == s;
                    assert(occurs_at(v, s, i));
                }
            }
        },
        _ => {},
    }
}

/// Matching a value as a flag says is matching the folds as they are.
pub proof fn lemma_value_fold(op: IAttrOp, ci: bool, v: Seq<u32>, s: Seq<u32>)
    ensures
        i_value_matches(op, ci, v, s) == i_value_matches(op, false, fold(ci, v), fold(ci, s)),
{
    lemma_same_fold(ci, v, s);
    if ci {
        let lv = i_lowercase(v);
        let ls = i_lowercase(s);
        assert(lv.len() == v.len());
        assert(ls.len() == s.len());
        match op {
            IAttrOp::Exists => {},
            IAttrOp::Eq => {},
            IAttrOp::Includes => {
                lemma_has_word_fold(ci, v, s);
            },
            IAttrOp::Dash => {
                if v.len() > s.len() {
                    lemma_lower_sub(v, 0, s.len() as int);
                    lemma_same_fold(ci, v.subrange(0, s.len() as int), s);
                    assert(lv[s.len() as int] == i_lower(v[s.len() as int]));
                }
            },
            IAttrOp::Prefix => {
                if v.len() >= s.len() {
                    lemma_lower_sub(v, 0, s.len() as int);
                    lemma_same_fold(ci, v.subrange(0, s.len() as int), s);
                }
            },
            IAttrOp::Suffix => {
                if v.len() >= s.len() {
                    lemma_lower_sub(v, v.len() - s.len(), v.len() as int);
                    lemma_same_fold(ci, v.subrange(v.len() - s.len(), v.len() as int), s);
                }
            },
            IAttrOp::Substring => {
                if s.len() > 0 {
                    if exists|i: int|
                        0 <= i && i + s.len() <= v.len() && i_same(
                            true,
                            #[trigger] v.subrange(i, i + s.len()),
                            s,
                        ) {
                        let i = choose|i: int|
                            0 <= i && i + s.len() <= v.len() && i_same(
                                true,
                                #[trigger] v.subrange(i, i + s.len()),
                                s,
                            );
                        lemma_lower_sub(v, i, i + s.len());
                        lemma_same_fold(true, v.subrange(i, i + s.len()), s);
                        assert(lv.subrange(i, i + ls.len()) == ls);
                    }
                    if exists|i: int|
                        0 <= i && i + ls.len() <= lv.len() && i_same(
                            false,
                            #[trigger] lv.subrange(i, i + ls.len()),
                            ls,
                        ) {
                        let i = choose|i: int|
                            0 <= i && i + ls.len() <= lv.len() && i_same(
                                false,
                                #[trigger] lv.subrange(i, i + ls.len()),
                                ls,
                            );
                        lemma_lower_sub(v, i, i + s.len());
                        lemma_same_fold(true, v.subrange(i, i + s.len()), s);
                        assert(i_same(true, v.subrange(i, i + s.len()), s));
                    }
                }
            },
        }
    }
}

// ------------------------------------------------------------------------------------
// Attributes of an element
// ------------------------------------------------------------------------------------

/// The attribute list has no two attributes with one namespace and local name.
pub open spec fn uniq_attrs(doc: Document) -> bool {
    forall|x: NodeId, j: int, k: int|
        is_element(doc, x) && 0 <= j < k < attributes_of(doc, x).len() ==> !(
        (#[trigger] attributes_of(doc, x)[j]).namespace == (#[trigger] attributes_of(doc, x)[k]).namespace
            && attributes_of(doc, x)[j].local_name == attributes_of(doc, x)[k].local_name)
}

/// HTML §4.16.2's list of case-insensitive attributes is the same in both.
pub proof fn lemma_ci_attribute_same(name: Seq<u32>)
    ensures
        is_case_insensitive_attribute(name) == i_html_ci_attribute(name),
{
}

/// The transcription's test of one attribute against an attribute selector.
pub open spec fn attr_ok(doc: Document, x: NodeId, m: IAttr, a: Attr) -> bool {
    i_attr_name_matches(doc, x, m.name, a) && i_attr_ns_matches(m.ns, a.namespace) && i_value_matches(
        m.op,
        i_attr_ci(doc, x, m.flag, a),
        a.value,
        m.value,
    )
}

/// The spec's test of one attribute is the transcription's.
pub proof fn lemma_attr_same(doc: Document, x: NodeId, ns: NsPrefix, name: Seq<u32>, test: Option<AttrTest>, m: IAttr, a: Attr)
    requires
        is_element(doc, x),
        rel_attr(ns, name, test, m),
    ensures
        (names_attribute(doc, x, ns, name, a) && attribute_passes(doc, x, a, test)) == attr_ok(doc, x, m, a),
{
    lemma_lowercase_same(name);
    lemma_ci_attribute_same(a.local_name);
    match test {
        None => {},
        Some(t) => {
            let ci = i_attr_ci(doc, x, m.flag, a);
            lemma_value_fold(m.op, ci, a.value, m.value);
            lemma_value_plain(t.matcher, m.op, fold(ci, a.value), fold(ci, m.value));
            lemma_lowercase_same(a.value);
            lemma_lowercase_same(m.value);
            assert(ci == match t.flag {
                Some(CaseFlag::I) => true,
                Some(CaseFlag::S) => false,
                None => is_html_element(doc, x) && a.namespace is None && is_case_insensitive_attribute(a.local_name),
            });
        },
    }
}

/// The spec's search through the first `k` attributes is the transcription's quantifier.
pub proof fn lemma_some_attribute(
    doc: Document,
    x: NodeId,
    ns: NsPrefix,
    name: Seq<u32>,
    test: Option<AttrTest>,
    m: IAttr,
    k: int,
)
    requires
        is_element(doc, x),
        rel_attr(ns, name, test, m),
        0 <= k <= attributes_of(doc, x).len(),
    ensures
        some_attribute(doc, x, ns, name, test, k) == exists|j: int|
            0 <= j < k && attr_ok(doc, x, m, #[trigger] attributes_of(doc, x)[j]),
    decreases k,
{
    if k > 0 {
        lemma_some_attribute(doc, x, ns, name, test, m, k - 1);
        lemma_attr_same(doc, x, ns, name, test, m, attributes_of(doc, x)[k - 1]);
        if exists|j: int| 0 <= j < k && attr_ok(doc, x, m, #[trigger] attributes_of(doc, x)[j]) {
            let j = choose|j: int| 0 <= j < k && attr_ok(doc, x, m, #[trigger] attributes_of(doc, x)[j]);
            if j < k - 1 {
                assert(0 <= j < k - 1);
            }
        }
    }
}

/// An attribute selector matches an element as the spec says.
pub proof fn lemma_attribute_same(doc: Document, x: NodeId, ns: NsPrefix, name: Seq<u32>, test: Option<AttrTest>, m: IAttr)
    requires
        is_element(doc, x),
        rel_attr(ns, name, test, m),
    ensures
        some_attribute(doc, x, ns, name, test, attributes_of(doc, x).len() as int) == i_attr_matches(
            doc,
            x,
            m,
        ),
{
    lemma_some_attribute(doc, x, ns, name, test, m, attributes_of(doc, x).len() as int);
}

/// The attribute `a` has no namespace and the local name `name`.
pub open spec fn plain_named(a: Attr, name: Seq<u32>) -> bool {
    a.namespace is None && a.local_name == name
}

/// With no two attributes of the same namespace and name, the spec's "first" attribute named
/// `name`, of the first `k`, is the only one.
pub proof fn lemma_first_attr(doc: Document, x: NodeId, name: Seq<u32>, k: int)
    requires
        is_element(doc, x),
        uniq_attrs(doc),
        0 <= k <= attributes_of(doc, x).len(),
    ensures
        forall|j: int|
            0 <= j < k && plain_named(#[trigger] attributes_of(doc, x)[j], name)
                ==> plain_attribute_value(doc, x, name, k) == Some(attributes_of(doc, x)[j].value),
        plain_attribute_value(doc, x, name, k) is None ==> forall|j: int|
            0 <= j < k ==> !plain_named(#[trigger] attributes_of(doc, x)[j], name),
    decreases k,
{
    if k > 0 {
        lemma_first_attr(doc, x, name, k - 1);
        let attr = attributes_of(doc, x)[k - 1];
        // An earlier attribute named `name` clashes with the last if the last is named so too.
        if plain_named(attr, name) {
            assert forall|j: int| 0 <= j < k - 1 implies !plain_named(#[trigger] attributes_of(doc, x)[j], name) by {
                if plain_named(attributes_of(doc, x)[j], name) {
                    assert(attributes_of(doc, x)[j].namespace == attr.namespace);
                    assert(attributes_of(doc, x)[j].local_name == attr.local_name);
                }
            }
        }
        assert forall|j: int|
            0 <= j < k && plain_named(#[trigger] attributes_of(doc, x)[j], name)
            implies plain_attribute_value(doc, x, name, k) == Some(attributes_of(doc, x)[j].value) by {
            if j < k - 1 {
                assert(plain_attribute_value(doc, x, name, k - 1) == Some(attributes_of(doc, x)[j].value));
            } else {
                lemma_first_attr_witness(doc, x, name, k - 1);
                assert(plain_attribute_value(doc, x, name, k - 1) is None);
            }
        }
    }
}

/// The spec's attribute value, if any, is the value of an attribute named `name`.
pub proof fn lemma_first_attr_witness(doc: Document, x: NodeId, name: Seq<u32>, k: int)
    requires
        0 <= k <= attributes_of(doc, x).len(),
    ensures
        plain_attribute_value(doc, x, name, k) is Some ==> exists|j: int|
            0 <= j < k && plain_named(#[trigger] attributes_of(doc, x)[j], name)
                && Some(attributes_of(doc, x)[j].value) == plain_attribute_value(doc, x, name, k),
    decreases k,
{
    if k > 0 {
        lemma_first_attr_witness(doc, x, name, k - 1);
        if plain_attribute_value(doc, x, name, k - 1) is Some {
            let j = choose|j: int|
                0 <= j < k - 1 && plain_named(#[trigger] attributes_of(doc, x)[j], name)
                    && Some(attributes_of(doc, x)[j].value) == plain_attribute_value(doc, x, name, k - 1);
            assert(0 <= j < k);
        } else if plain_attribute_value(doc, x, name, k) is Some {
            assert(plain_named(attributes_of(doc, x)[k - 1], name));
        }
    }
}

/// The document is in quirks mode, in both.
pub proof fn lemma_quirks_same(doc: Document)
    requires
        doc.nodes.len() > 0,
    ensures
        in_quirks_mode(doc) == i_quirks(doc),
{
}

/// An ID selector matches as the spec says.
pub proof fn lemma_id_same(doc: Document, x: NodeId, id: Seq<u32>)
    requires
        is_element(doc, x),
        uniq_attrs(doc),
        doc.nodes.len() > 0,
    ensures
        has_id(doc, x, id) == i_has_id(doc, x, id),
{
    lemma_quirks_same(doc);
    let attrs = attributes_of(doc, x);
    lemma_first_attr(doc, x, str_id(), attrs.len() as int);
    lemma_first_attr_witness(doc, x, str_id(), attrs.len() as int);
    lemma_lowercase_same(id);
    if let Some(value) = get_attribute(doc, x, str_id()) {
        lemma_lowercase_same(value);
        lemma_same_fold(i_quirks(doc), value, id);
    }
    if i_has_id(doc, x, id) {
        let k = choose|k: int|
            0 <= k < attrs.len() && #[trigger] attrs[k].namespace is None && attrs[k].local_name == seq![0x69u32, 0x64]
                && i_same(i_quirks(doc), attrs[k].value, id);
        assert(plain_named(attrs[k], str_id()));
        lemma_lowercase_same(attrs[k].value);
        lemma_same_fold(i_quirks(doc), attrs[k].value, id);
    }
}

/// A class selector matches as the spec says.
pub proof fn lemma_class_same(doc: Document, x: NodeId, class: Seq<u32>)
    requires
        is_element(doc, x),
        uniq_attrs(doc),
        doc.nodes.len() > 0,
    ensures
        has_class(doc, x, class) == i_has_class(doc, x, class),
{
    lemma_quirks_same(doc);
    let attrs = attributes_of(doc, x);
    lemma_first_attr(doc, x, str_class(), attrs.len() as int);
    lemma_first_attr_witness(doc, x, str_class(), attrs.len() as int);
    lemma_lowercase_same(class);
    if let Some(value) = get_attribute(doc, x, str_class()) {
        lemma_has_word_fold(i_quirks(doc), value, class);
        lemma_words_plain(fold(i_quirks(doc), value), fold(i_quirks(doc), class));
        lemma_lowercase_same(value);
    }
    if i_has_class(doc, x, class) {
        let k = choose|k: int|
            0 <= k < attrs.len() && #[trigger] attrs[k].namespace is None
                && attrs[k].local_name == seq![0x63u32, 0x6C, 0x61, 0x73, 0x73] && i_has_word(
                i_quirks(doc),
                attrs[k].value,
                class,
            );
        assert(plain_named(attrs[k], str_class()));
        lemma_has_word_fold(i_quirks(doc), attrs[k].value, class);
        lemma_words_plain(fold(i_quirks(doc), attrs[k].value), fold(i_quirks(doc), class));
        lemma_lowercase_same(attrs[k].value);
    }
}

// ------------------------------------------------------------------------------------
// Type selectors, :root and :empty
// ------------------------------------------------------------------------------------

/// A type or universal selector matches as the spec says.
pub proof fn lemma_type_same(doc: Document, scope: Option<NodeId>, x: NodeId, s: Simple, t: IType)
    requires
        is_element(doc, x),
        rel_type(s, t),
    ensures
        simple_matches(doc, scope, s, x) == i_type_matches(doc, x, t),
{
    lemma_lowercase_same(match s {
        Simple::Type { name, .. } => name,
        _ => Seq::empty(),
    });
}

/// Every code point of a string is white space, as the spec recurses.
pub proof fn lemma_all_whitespace_iff(data: Seq<u32>, i: int)
    requires
        0 <= i,
    ensures
        all_whitespace(data, i) <==> forall|k: int| i <= k < data.len() ==> i_white(#[trigger] data[k]),
    decreases data.len() - i,
{
    if i < data.len() {
        lemma_all_whitespace_iff(data, i + 1);
    }
}

/// The spec's `:empty` check of the first `k` children is the transcription's quantifier.
pub proof fn lemma_empty_up_to(doc: Document, kids: Seq<NodeId>, k: int)
    requires
        0 <= k <= kids.len(),
    ensures
        empty_up_to(doc, kids, k) == forall|j: int|
            0 <= j < k ==> {
                let c = #[trigger] kids[j];
                c >= doc.nodes.len() || i_node_is_empty_content(doc, c)
            },
    decreases k,
{
    if k > 0 {
        lemma_empty_up_to(doc, kids, k - 1);
        let child = kids[k - 1];
        if child < doc.nodes.len() {
            match doc.nodes[child as int].kind {
                NodeKind::Text { data } => lemma_all_whitespace_iff(data, 0),
                _ => {},
            }
        }
    }
}

/// `:empty` matches as the spec says.
pub proof fn lemma_empty_same(doc: Document, x: NodeId)
    requires
        is_element(doc, x),
    ensures
        empty_up_to(doc, children_of(doc, x), children_of(doc, x).len() as int) == i_is_empty(doc, x),
{
    lemma_empty_up_to(doc, children_of(doc, x), children_of(doc, x).len() as int);
}

} // verus!
