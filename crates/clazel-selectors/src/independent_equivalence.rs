//! The independent transcription ([`super::independent`]) is equal to the spec ([`super::spec`])
//! on the selectors the two have in common, as three theorems (docs/VERIFICATION.md, "Trust
//! without reviewers", item 2):
//!
//! - [`theorem_specificity_equivalent`]: the specificity of a selector list;
//! - [`theorem_match_equivalent`]: whether a selector list matches an element;
//! - the parse theorems of [`super::independent_parse`].
//!
//! The two texts do not parse and match the same set of selectors, so the theorems are about
//! the selectors both have. [`rel_simple`] and the relations around it say which spec selector
//! is which transcription selector, and they hold of the common ones only: the spec's
//! `:link`, `:visited`, `:any-link`, user action pseudo-classes and pseudo-elements, which the
//! transcription takes as invalid, are related to nothing, and so is every transcription
//! selector the spec has no counterpart for (`:has()`, `:scope`, `:defined`, `of S`: with
//! [`ICtx::ext`] false the transcription parses none of them).
//!
//! The matching theorem takes the arena to be well-formed and its elements to have no two
//! attributes with the same namespace and local name (DOM's attribute list has none): the spec
//! reads an ID or class from the first such attribute, the transcription from any, as §8 says
//! of multiple IDs.

#[cfg(verus_only)]
use super::independent::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Which spec selector is which transcription selector
// ------------------------------------------------------------------------------------

/// The namespace component of a type or universal selector: no `|` is `*|E`, as the spec's
/// "if no default namespace has been declared for selectors, this is equivalent to `*|E`".
pub open spec fn rel_ns_type(n: NsPrefix, m: INs) -> bool {
    match n {
        NsPrefix::Absent => m == INs::Any,
        NsPrefix::Any => m == INs::Any,
        NsPrefix::NoNamespace => m == INs::NoNs,
    }
}

/// The namespace component of an attribute selector: no `|` is `|`, "default namespaces do not
/// apply to attributes".
pub open spec fn rel_ns_attr(n: NsPrefix, m: INs) -> bool {
    match n {
        NsPrefix::Absent => m == INs::NoNs,
        NsPrefix::Any => m == INs::Any,
        NsPrefix::NoNamespace => m == INs::NoNs,
    }
}

/// The matchers.
pub open spec fn rel_matcher(a: AttrMatcher, b: IAttrOp) -> bool {
    match a {
        AttrMatcher::Equals => b == IAttrOp::Eq,
        AttrMatcher::Includes => b == IAttrOp::Includes,
        AttrMatcher::DashMatch => b == IAttrOp::Dash,
        AttrMatcher::Prefix => b == IAttrOp::Prefix,
        AttrMatcher::Suffix => b == IAttrOp::Suffix,
        AttrMatcher::Substring => b == IAttrOp::Substring,
    }
}

/// The case flags.
pub open spec fn rel_flag(f: Option<CaseFlag>, m: IFlag) -> bool {
    match f {
        None => m == IFlag::Default,
        Some(CaseFlag::I) => m == IFlag::I,
        Some(CaseFlag::S) => m == IFlag::S,
    }
}

/// An attribute selector.
pub open spec fn rel_attr(ns: NsPrefix, name: Seq<u32>, test: Option<AttrTest>, m: IAttr) -> bool {
    rel_ns_attr(ns, m.ns) && m.name == name && match test {
        None => m.op == IAttrOp::Exists && m.value == Seq::<u32>::empty() && m.flag == IFlag::Default,
        Some(t) => rel_matcher(t.matcher, m.op) && m.value == t.value && rel_flag(t.flag, m.flag),
    }
}

/// The combinators.
pub open spec fn rel_comb(a: Combinator, m: IComb) -> bool {
    match a {
        Combinator::Descendant => m == IComb::Descendant,
        Combinator::Child => m == IComb::Child,
        Combinator::NextSibling => m == IComb::Next,
        Combinator::SubsequentSibling => m == IComb::Subsequent,
    }
}

/// A spec simple selector that is a type or universal selector: the transcription keeps it
/// apart from the others, in [`ICompound::ty`].
pub open spec fn is_type_or_universal(s: Simple) -> bool {
    s is Type || s is Universal
}

/// A type or universal selector and its transcription.
pub open spec fn rel_type(s: Simple, t: IType) -> bool {
    match s {
        Simple::Type { ns, name } => rel_ns_type(ns, t.ns) && t.name == IName::Local(name),
        Simple::Universal { ns } => rel_ns_type(ns, t.ns) && t.name == IName::Star,
        _ => false,
    }
}

/// A spec simple selector that is neither a type nor a universal selector, and its
/// transcription. Only the selectors the two have in common are related.
pub open spec fn rel_simple(s: Simple, m: ISimple) -> bool
    decreases s, 0nat,
{
    match s {
        Simple::Type { .. } => false,
        Simple::Universal { .. } => false,
        Simple::PseudoElement { .. } => false,
        Simple::Id { name } => m == ISimple::Id(name),
        Simple::Class { name } => m == ISimple::Class(name),
        Simple::Attribute { ns, name, test } => match m {
            ISimple::Attr(a) => rel_attr(ns, name, test, a),
            _ => false,
        },
        Simple::PseudoClass { class } => match class {
            PseudoClass::Root => m == ISimple::Root,
            PseudoClass::Empty => m == ISimple::Empty,
            PseudoClass::FirstChild => m == ISimple::NthChild {
                a: 0,
                b: 1,
                last: false,
                has_of: false,
                of: Seq::empty(),
            },
            PseudoClass::LastChild => m == ISimple::NthChild {
                a: 0,
                b: 1,
                last: true,
                has_of: false,
                of: Seq::empty(),
            },
            PseudoClass::OnlyChild => m == ISimple::OnlyChild,
            PseudoClass::FirstOfType => m == ISimple::NthType { a: 0, b: 1, last: false },
            PseudoClass::LastOfType => m == ISimple::NthType { a: 0, b: 1, last: true },
            PseudoClass::OnlyOfType => m == ISimple::OnlyOfType,
            _ => false,
        },
        Simple::Nth { kind, a, b } => match kind {
            NthKind::Child => m == ISimple::NthChild {
                a,
                b,
                last: false,
                has_of: false,
                of: Seq::empty(),
            },
            NthKind::LastChild => m == ISimple::NthChild {
                a,
                b,
                last: true,
                has_of: false,
                of: Seq::empty(),
            },
            NthKind::OfType => m == ISimple::NthType { a, b, last: false },
            NthKind::LastOfType => m == ISimple::NthType { a, b, last: true },
        },
        Simple::Is { arg } => match m {
            ISimple::Is(l) => rel_list(arg, l),
            _ => false,
        },
        Simple::Where { arg } => match m {
            ISimple::Where(l) => rel_list(arg, l),
            _ => false,
        },
        Simple::Not { arg } => match m {
            ISimple::Not(l) => rel_list(arg, l),
            _ => false,
        },
    }
}

/// How many items a spec compound selector starts with that the transcription keeps apart: one
/// type or universal selector, if the compound selector starts with one.
pub open spec fn comp_off(c: Seq<Simple>) -> int {
    if c.len() > 0 && is_type_or_universal(c[0]) {
        1
    } else {
        0
    }
}

/// A spec compound selector (a type or universal selector first, if any, then the others) and
/// its transcription.
pub open spec fn rel_compound(c: Seq<Simple>, m: ICompound) -> bool
    decreases c, 1nat,
{
    let off = comp_off(c);
    (match m.ty {
        Some(t) => off == 1 && rel_type(c[0], t),
        None => off == 0,
    }) && m.subs.len() == c.len() - off && forall|k: int|
        0 <= k < m.subs.len() ==> rel_simple(#[trigger] c[off + k], m.subs[k])
}

/// A spec complex selector and its transcription (a complex selector, not a relative one).
pub open spec fn rel_complex(c: Complex, m: IComplex) -> bool
    decreases c, 2nat,
{
    m.lead is None && c.compounds.len() >= 1 && m.units.len() == c.compounds.len()
        && m.combs.len() == c.combinators.len() && c.combinators.len() + 1 == c.compounds.len()
        && (forall|k: int|
        0 <= k < m.units.len() ==> rel_compound(#[trigger] c.compounds[k], m.units[k]))
        && (forall|k: int|
        0 <= k < m.combs.len() ==> rel_comb(#[trigger] c.combinators[k], m.combs[k]))
}

/// A list of spec complex selectors and its transcription.
pub open spec fn rel_list(l: Seq<Complex>, m: Seq<IComplex>) -> bool
    decreases l, 3nat,
{
    l.len() == m.len() && forall|k: int| 0 <= k < l.len() ==> rel_complex(#[trigger] l[k], m[k])
}

// ------------------------------------------------------------------------------------
// Specificity
// ------------------------------------------------------------------------------------

/// A spec specificity as the transcription's.
pub open spec fn sp2i(x: Specificity) -> ISpec {
    ISpec { a: x.a, b: x.b, c: x.c }
}

/// `x` is within the limit in each component.
pub open spec fn sp_bounded(x: ISpec) -> bool {
    x.a <= 0xFFFF_FFFFnat && x.b <= 0xFFFF_FFFFnat && x.c <= 0xFFFF_FFFFnat
}

/// The spec's saturating addition is the transcription's.
pub proof fn lemma_add_same(x: Specificity, y: Specificity)
    ensures
        sp2i(add_specificity(x, y)) == i_sp_add(sp2i(x), sp2i(y)),
{
}

/// The spec's "most specific" is the transcription's (they differ on ties, where the two
/// are equal).
pub proof fn lemma_max_same(x: Specificity, y: Specificity)
    ensures
        sp2i(most_specific(x, y)) == i_sp_max(sp2i(x), sp2i(y)),
{
}

/// Saturating addition is associative.
pub proof fn lemma_add_assoc(x: ISpec, y: ISpec, z: ISpec)
    ensures
        i_sp_add(i_sp_add(x, y), z) == i_sp_add(x, i_sp_add(y, z)),
{
}

/// Saturating addition is commutative.
pub proof fn lemma_add_comm(x: ISpec, y: ISpec)
    ensures
        i_sp_add(x, y) == i_sp_add(y, x),
{
}

/// A sum is within the limit.
pub proof fn lemma_add_bounded(x: ISpec, y: ISpec)
    ensures
        sp_bounded(i_sp_add(x, y)),
{
}

/// Adding to nothing changes a value within the limit by nothing.
pub proof fn lemma_add_zero(x: ISpec)
    requires
        sp_bounded(x),
    ensures
        i_sp_add(i_sp_zero(), x) == x,
        i_sp_add(x, i_sp_zero()) == x,
{
}

/// `es[0..n)` added from the left, from nothing, as the spec's prefix sums are.
pub open spec fn lf_add(es: Seq<ISpec>, n: int) -> ISpec
    decreases n,
{
    if n <= 0 || n > es.len() {
        i_sp_zero()
    } else {
        i_sp_add(lf_add(es, n - 1), es[n - 1])
    }
}

/// `es[k..n)` added from the right, from nothing, as the transcription's suffix sums are.
pub open spec fn rf_add(es: Seq<ISpec>, k: int, n: int) -> ISpec
    decreases n - k,
{
    if k < 0 || k >= n || n > es.len() {
        i_sp_zero()
    } else {
        i_sp_add(es[k], rf_add(es, k + 1, n))
    }
}

/// A sum from the right is within the limit.
pub proof fn lemma_rf_add_bounded(es: Seq<ISpec>, k: int, n: int)
    ensures
        sp_bounded(rf_add(es, k, n)),
    decreases n - k,
{
    if !(k < 0 || k >= n || n > es.len()) {
        lemma_rf_add_bounded(es, k + 1, n);
        lemma_add_bounded(es[k], rf_add(es, k + 1, n));
    }
}

/// Adding one more item at the end of a sum from the right.
pub proof fn lemma_rf_add_append(es: Seq<ISpec>, k: int, n: int)
    requires
        0 <= k <= n,
        n < es.len(),
    ensures
        rf_add(es, k, n + 1) == i_sp_add(rf_add(es, k, n), es[n]),
    decreases n - k,
{
    if k == n {
        assert(rf_add(es, n, n) == i_sp_zero());
        assert(rf_add(es, n + 1, n + 1) == i_sp_zero());
        assert(rf_add(es, n, n + 1) == i_sp_add(es[n], i_sp_zero()));
        lemma_add_comm(es[n], i_sp_zero());
    } else {
        lemma_rf_add_append(es, k + 1, n);
        lemma_add_assoc(es[k], rf_add(es, k + 1, n), es[n]);
        assert(rf_add(es, k, n + 1) == i_sp_add(es[k], rf_add(es, k + 1, n + 1)));
        assert(rf_add(es, k, n) == i_sp_add(es[k], rf_add(es, k + 1, n)));
    }
}

/// A sum from the left is a sum from the right.
pub proof fn lemma_lf_rf_add(es: Seq<ISpec>, n: int)
    requires
        0 <= n <= es.len(),
    ensures
        lf_add(es, n) == rf_add(es, 0, n),
    decreases n,
{
    if n > 0 {
        lemma_lf_rf_add(es, n - 1);
        lemma_rf_add_append(es, 0, n - 1);
    }
}

/// The maximum is associative.
pub proof fn lemma_max_assoc(x: ISpec, y: ISpec, z: ISpec)
    ensures
        i_sp_max(i_sp_max(x, y), z) == i_sp_max(x, i_sp_max(y, z)),
{
}

/// The maximum is commutative.
pub proof fn lemma_max_comm(x: ISpec, y: ISpec)
    ensures
        i_sp_max(x, y) == i_sp_max(y, x),
{
}

/// `es[0..n)`, the most specific, from the left.
pub open spec fn lf_max(es: Seq<ISpec>, n: int) -> ISpec
    decreases n,
{
    if n <= 0 || n > es.len() {
        i_sp_zero()
    } else {
        i_sp_max(lf_max(es, n - 1), es[n - 1])
    }
}

/// `es[k..n)`, the most specific, from the right.
pub open spec fn rf_max(es: Seq<ISpec>, k: int, n: int) -> ISpec
    decreases n - k,
{
    if k < 0 || k >= n || n > es.len() {
        i_sp_zero()
    } else {
        i_sp_max(es[k], rf_max(es, k + 1, n))
    }
}

/// Adding one more item at the end of a maximum from the right.
pub proof fn lemma_rf_max_append(es: Seq<ISpec>, k: int, n: int)
    requires
        0 <= k <= n,
        n < es.len(),
    ensures
        rf_max(es, k, n + 1) == i_sp_max(rf_max(es, k, n), es[n]),
    decreases n - k,
{
    if k == n {
        assert(rf_max(es, n, n) == i_sp_zero());
        assert(rf_max(es, n + 1, n + 1) == i_sp_zero());
        assert(rf_max(es, n, n + 1) == i_sp_max(es[n], i_sp_zero()));
        lemma_max_comm(es[n], i_sp_zero());
    } else {
        lemma_rf_max_append(es, k + 1, n);
        lemma_max_assoc(es[k], rf_max(es, k + 1, n), es[n]);
        assert(rf_max(es, k, n + 1) == i_sp_max(es[k], rf_max(es, k + 1, n + 1)));
        assert(rf_max(es, k, n) == i_sp_max(es[k], rf_max(es, k + 1, n)));
    }
}

/// A maximum from the left is a maximum from the right.
pub proof fn lemma_lf_rf_max(es: Seq<ISpec>, n: int)
    requires
        0 <= n <= es.len(),
    ensures
        lf_max(es, n) == rf_max(es, 0, n),
    decreases n,
{
    if n > 0 {
        lemma_lf_rf_max(es, n - 1);
        lemma_rf_max_append(es, 0, n - 1);
    }
}

/// The specificities of a spec compound selector's simple selectors.
pub open spec fn sp_elems_compound(c: Seq<Simple>) -> Seq<ISpec> {
    Seq::new(c.len(), |j: int| sp2i(simple_specificity(c[j])))
}

/// The spec's prefix sum of a compound selector's specificities is a sum from the left.
pub proof fn lemma_compound_is_lf(c: Seq<Simple>, k: int)
    requires
        0 <= k <= c.len(),
    ensures
        sp2i(compound_specificity(c, k)) == lf_add(sp_elems_compound(c), k),
    decreases k,
{
    if k > 0 {
        lemma_compound_is_lf(c, k - 1);
        lemma_add_same(compound_specificity(c, k - 1), simple_specificity(c[k - 1]));
    }
}

/// The transcription's specificities of a compound selector's simple selectors.
pub open spec fn sp_elems_subs(subs: Seq<ISimple>) -> Seq<ISpec> {
    Seq::new(subs.len(), |j: int| i_sp_simple(subs[j]))
}

/// The transcription's suffix sum is a sum from the right.
pub proof fn lemma_subs_is_rf(subs: Seq<ISimple>, k: int)
    requires
        0 <= k,
    ensures
        i_sp_subs(subs, k) == rf_add(sp_elems_subs(subs), k, subs.len() as int),
    decreases subs.len() - k,
{
    if k < subs.len() {
        lemma_subs_is_rf(subs, k + 1);
    }
}

/// The specificities of a spec complex selector's compound selectors.
pub open spec fn sp_elems_complex(c: Complex) -> Seq<ISpec> {
    Seq::new(
        c.compounds.len(),
        |j: int| sp2i(compound_specificity(c.compounds[j], c.compounds[j].len() as int)),
    )
}

/// The spec's prefix sum over a complex selector is a sum from the left.
pub proof fn lemma_complex_is_lf(c: Complex, n: int)
    requires
        0 <= n <= c.compounds.len(),
    ensures
        sp2i(complex_specificity(c, n)) == lf_add(sp_elems_complex(c), n),
    decreases n,
{
    if n > 0 {
        lemma_complex_is_lf(c, n - 1);
        lemma_add_same(
            complex_specificity(c, n - 1),
            compound_specificity(c.compounds[n - 1], c.compounds[n - 1].len() as int),
        );
    }
}

/// The transcription's specificities of a complex selector's compound selectors.
pub open spec fn sp_elems_units(c: IComplex) -> Seq<ISpec> {
    Seq::new(c.units.len(), |j: int| i_sp_compound(c.units[j]))
}

/// The transcription's suffix sum over a complex selector is a sum from the right.
pub proof fn lemma_units_is_rf(c: IComplex, k: int)
    requires
        0 <= k,
    ensures
        i_sp_complex(c, k) == rf_add(sp_elems_units(c), k, c.units.len() as int),
    decreases c.units.len() - k,
{
    if k < c.units.len() {
        lemma_units_is_rf(c, k + 1);
    }
}

/// The specificities of a spec list's complex selectors.
pub open spec fn sp_elems_list(l: Seq<Complex>) -> Seq<ISpec> {
    Seq::new(l.len(), |j: int| sp2i(complex_specificity(l[j], l[j].compounds.len() as int)))
}

/// The spec's most specific of a prefix is a maximum from the left.
pub proof fn lemma_list_is_lf(l: Seq<Complex>, k: int)
    requires
        0 <= k <= l.len(),
    ensures
        sp2i(list_specificity(l, k)) == lf_max(sp_elems_list(l), k),
    decreases k,
{
    if k > 0 {
        lemma_list_is_lf(l, k - 1);
        lemma_max_same(
            list_specificity(l, k - 1),
            complex_specificity(l[k - 1], l[k - 1].compounds.len() as int),
        );
    }
}

/// The transcription's specificities of a list's complex selectors.
pub open spec fn sp_elems_ilist(l: Seq<IComplex>) -> Seq<ISpec> {
    Seq::new(l.len(), |j: int| i_sp_complex(l[j], 0))
}

/// The transcription's most specific of a suffix is a maximum from the right.
pub proof fn lemma_ilist_is_rf(l: Seq<IComplex>, k: int)
    requires
        0 <= k,
    ensures
        i_sp_list(l, k) == rf_max(sp_elems_ilist(l), k, l.len() as int),
    decreases l.len() - k,
{
    if k < l.len() {
        lemma_ilist_is_rf(l, k + 1);
    }
}

/// The sums of `es[off..n)` from the right and of `ms[k..)`, which hold the same items.
pub proof fn lemma_rf_shift_from(es: Seq<ISpec>, ms: Seq<ISpec>, off: int, n: int, k: int)
    requires
        0 <= off <= n,
        n == es.len(),
        ms.len() == n - off,
        0 <= k <= ms.len(),
        forall|j: int| 0 <= j < ms.len() ==> es[off + j] == #[trigger] ms[j],
    ensures
        rf_add(es, off + k, n) == rf_add(ms, k, ms.len() as int),
    decreases ms.len() - k,
{
    if k < ms.len() {
        lemma_rf_shift_from(es, ms, off, n, k + 1);
    }
}

/// A related simple selector has the same specificity.
pub proof fn lemma_sp_simple(s: Simple, m: ISimple)
    requires
        rel_simple(s, m),
    ensures
        sp2i(simple_specificity(s)) == i_sp_simple(m),
    decreases s, 0nat,
{
    match s {
        Simple::Is { arg } => {
            match m {
                ISimple::Is(l) => lemma_sp_list(arg, l),
                _ => {},
            }
        },
        Simple::Not { arg } => {
            match m {
                ISimple::Not(l) => lemma_sp_list(arg, l),
                _ => {},
            }
        },
        _ => {},
    }
}

/// A related compound selector has the same specificity.
pub proof fn lemma_sp_compound(c: Seq<Simple>, m: ICompound)
    requires
        rel_compound(c, m),
    ensures
        sp2i(compound_specificity(c, c.len() as int)) == i_sp_compound(m),
    decreases c, 1nat,
{
    let off = comp_off(c);
    let es = sp_elems_compound(c);
    let ms = sp_elems_subs(m.subs);
    assert forall|j: int| 0 <= j < m.subs.len() implies es[off + j] == ms[j] by {
        lemma_sp_simple(c[off + j], m.subs[j]);
    }
    lemma_compound_is_lf(c, c.len() as int);
    lemma_lf_rf_add(es, c.len() as int);
    lemma_subs_is_rf(m.subs, 0);
    lemma_rf_shift_from(es, ms, off, c.len() as int, 0);
    lemma_rf_add_bounded(ms, 0, ms.len() as int);
    match m.ty {
        Some(t) => {
            assert(rf_add(es, 0, c.len() as int) == i_sp_add(es[0], rf_add(es, 1, c.len() as int)));
            assert(es[0] == sp2i(simple_specificity(c[0])));
        },
        None => {
            lemma_add_zero(rf_add(ms, 0, ms.len() as int));
        },
    }
}

/// A related complex selector has the same specificity.
pub proof fn lemma_sp_complex(c: Complex, m: IComplex)
    requires
        rel_complex(c, m),
    ensures
        sp2i(specificity(c)) == i_sp_complex(m, 0),
    decreases c, 2nat,
{
    let es = sp_elems_complex(c);
    let ms = sp_elems_units(m);
    assert forall|j: int| 0 <= j < m.units.len() implies es[j] == ms[j] by {
        lemma_sp_compound(c.compounds[j], m.units[j]);
    }
    assert(es =~= ms);
    lemma_complex_is_lf(c, c.compounds.len() as int);
    lemma_lf_rf_add(es, c.compounds.len() as int);
    lemma_units_is_rf(m, 0);
}

/// A related list has the same specificity (the most specific of its selectors).
pub proof fn lemma_sp_list(l: Seq<Complex>, m: Seq<IComplex>)
    requires
        rel_list(l, m),
    ensures
        sp2i(list_specificity(l, l.len() as int)) == i_sp_list(m, 0),
    decreases l, 3nat,
{
    let es = sp_elems_list(l);
    let ms = sp_elems_ilist(m);
    assert forall|j: int| 0 <= j < l.len() implies es[j] == ms[j] by {
        lemma_sp_complex(l[j], m[j]);
    }
    assert(es =~= ms);
    lemma_list_is_lf(l, l.len() as int);
    lemma_lf_rf_max(es, l.len() as int);
    lemma_ilist_is_rf(m, 0);
}

/// **Specificity.** A spec selector list and its transcription have the same specificity, and so
/// does each selector of it.
pub proof fn theorem_specificity_equivalent(l: Seq<Complex>, m: Seq<IComplex>)
    requires
        rel_list(l, m),
    ensures
        sp2i(list_specificity(l, l.len() as int)) == i_sp_list(m, 0),
        forall|k: int|
            0 <= k < l.len() ==> sp2i(specificity(l[k])) == i_sp_complex(#[trigger] m[k], 0),
{
    lemma_sp_list(l, m);
    assert forall|k: int| 0 <= k < l.len() implies sp2i(specificity(l[k])) == i_sp_complex(
        #[trigger] m[k],
        0,
    ) by {
        lemma_sp_complex(l[k], m[k]);
    }
}

} // verus!
