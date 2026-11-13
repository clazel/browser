//! Contracts the executable code must be proven to meet, and the statements of the theorems
//! about the spec. Each exec entry point's `ensures` clause is one of these predicates, of
//! the views of what it takes and returns, so reading these and [`super::spec`] is enough to
//! know what the implementation guarantees.

#[cfg(verus_only)]
use super::algorithm::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Parsing
// ------------------------------------------------------------------------------------

/// How deeply the exec parser follows functions inside functions, `:is(:is(…))`, before it
/// gives up. It recurses once per level, so the limit keeps a page's selector from
/// exhausting the stack. The spec has no limit; [`parse_selector_ensures`] says where the
/// two can differ.
pub const MAX_NESTING: usize = 32;

/// How deeply functions and simple blocks nest in `value`: 0 for a token.
pub open spec fn value_depth(value: ComponentValue) -> nat
    decreases value, 0nat,
{
    match value {
        ComponentValue::Token { .. } => 0,
        ComponentValue::Function { value, .. } => 1 + values_depth(value, value.len()),
        ComponentValue::SimpleBlock { value, .. } => 1 + values_depth(value, value.len()),
    }
}

/// The deepest of the first `n` of `values`.
pub open spec fn values_depth(values: Seq<ComponentValue>, n: nat) -> nat
    decreases values, n,
{
    if n == 0 || n > values.len() {
        0
    } else {
        let rest = values_depth(values, (n - 1) as nat);
        let last = value_depth(values[n - 1]);
        if rest >= last {
            rest
        } else {
            last
        }
    }
}

/// The component values that "parse a selector" parses `input` into.
pub open spec fn selector_values(input: Seq<u32>) -> Seq<ComponentValue> {
    parse_a_list_of_component_values(Input::String { string: input })
}

/// Contract for `parse_selector(input)`. What it returns is always the spec's result; it
/// may return failure where the spec does not only if functions nest more deeply than
/// [`MAX_NESTING`].
pub open spec fn parse_selector_ensures(input: Seq<u32>, result: Option<Seq<Complex>>) -> bool {
    let values = selector_values(input);
    &&& result is Some ==> result == parse_a_selector(input)
    &&& values_depth(values, values.len()) <= MAX_NESTING ==> result == parse_a_selector(input)
}

// ------------------------------------------------------------------------------------
// Well-formed selectors
// ------------------------------------------------------------------------------------

/// True if the first `k` simple selectors of `compound` are well-formed.
pub open spec fn compound_wf(compound: Seq<Simple>, k: int) -> bool
    decreases compound, k, 0int,
{
    k <= 0 || k > compound.len() || (compound_wf(compound, k - 1) && simple_wf(compound[k - 1]))
}

/// True if a simple selector's argument, if any, is well-formed: `:not()`'s is not empty
/// (§4.3 takes a `<complex-real-selector-list>`, one or more), and those of `:is()` and
/// `:where()` may be (§4.2: "If the argument, after parsing, is an empty list, the
/// pseudo-class is valid but matches nothing").
pub open spec fn simple_wf(s: Simple) -> bool
    decreases s, 0int, 0int,
{
    match s {
        Simple::Is { arg } => list_wf(arg, arg.len() as int),
        Simple::Where { arg } => list_wf(arg, arg.len() as int),
        Simple::Not { arg } => arg.len() > 0 && list_wf(arg, arg.len() as int),
        _ => true,
    }
}

/// True if the first `n` compound selectors of `c` are well-formed and not empty.
pub open spec fn compounds_wf(c: Complex, n: int) -> bool
    decreases c, n, 0int,
{
    n <= 0 || n > c.compounds.len() || (compounds_wf(c, n - 1) && c.compounds[n - 1].len() > 0
        && compound_wf(c.compounds[n - 1], c.compounds[n - 1].len() as int))
}

/// A well-formed complex selector: at least one compound selector, none empty (§3.10: "an
/// empty selector, i.e. one that contains no compound selector, is invalid"; §18's `[ … ]!`),
/// and a combinator between each two.
pub open spec fn complex_wf(c: Complex) -> bool
    decreases c, c.compounds.len() + 1, 0int,
{
    c.compounds.len() >= 1 && c.combinators.len() + 1 == c.compounds.len() && compounds_wf(
        c,
        c.compounds.len() as int,
    )
}

/// True if the first `k` complex selectors of `list` are well-formed.
pub open spec fn list_wf(list: Seq<Complex>, k: int) -> bool
    decreases list, k, 0int,
{
    k <= 0 || k > list.len() || (list_wf(list, k - 1) && complex_wf(list[k - 1]))
}

// ------------------------------------------------------------------------------------
// Matching
// ------------------------------------------------------------------------------------

/// What matching needs of the document and the element: a well-formed arena (Phase 4's
/// `wf`, which every arena the HTML parser builds keeps) and one of its nodes.
pub open spec fn match_requires(doc: Document, x: NodeId) -> bool {
    clazel_dom::spec::wf(doc) && x < doc.nodes.len()
}

/// Contract for `matches(doc, selector, x)`: §21.3 "match a selector against an element".
pub open spec fn match_ensures(doc: Document, selector: Seq<Complex>, x: NodeId, r: bool) -> bool {
    r == match_a_selector_against_an_element(doc, selector, x)
}

/// How many nodes the walk for `x` meets when it visits siblings: each node of the chain
/// below the root, with the siblings before it, and the root.
pub open spec fn context_from(doc: Document, ch: Seq<NodeId>, k: int) -> nat
    decreases k,
{
    if k <= 0 || k >= ch.len() {
        1
    } else {
        context_from(doc, ch, k - 1) + (clazel_dom::spec::index_of(
            children_of(doc, ch[k - 1]),
            ch[k],
        ) + 1) as nat
    }
}

/// The number of nodes the walk for `x` meets when the selector has a sibling combinator.
pub open spec fn context_size(doc: Document, x: NodeId) -> nat {
    let ch = chain(doc, x);
    context_from(doc, ch, ch.len() - 1)
}

/// The work bound of item 5.5: one complex selector against one element visits at most depth
/// × compounds elements. Here "depth" is the length of `x`'s chain of inclusive ancestors
/// when no combinator is `+` or `~`; with one, the elements before each chain node among its
/// siblings are related too, so it is the number of those nodes and the chain's.
pub open spec fn work_bound(doc: Document, c: Complex, x: NodeId) -> nat {
    c.compounds.len() * if uses_siblings(c) {
        context_size(doc, x)
    } else {
        chain(doc, x).len()
    }
}

/// Contract for matching one complex selector and counting the work, and the statement of
/// `theorem_match_total` for the algorithm: the answer is the spec's, and the work is
/// within the bound.
pub open spec fn match_work_ensures(doc: Document, c: Complex, x: NodeId, r: bool, work: nat) -> bool {
    &&& r == match_complex(doc, c, c.compounds.len() as int, x)
    &&& work <= work_bound(doc, c, x)
}

// ------------------------------------------------------------------------------------
// Specificity and serialization
// ------------------------------------------------------------------------------------

/// Contract for `specificity_of(selectors, k)`: §17, as (A, B, C).
pub open spec fn specificity_ensures(c: Complex, a: nat, b: nat, cc: nat) -> bool {
    specificity(c) == (Specificity { a, b, c: cc })
}

/// Contract for `serialize(selectors)`: CSSOM "serialize a group of selectors".
pub open spec fn serialize_ensures(list: Seq<Complex>, out: Seq<u32>) -> bool {
    out == serialize_a_group_of_selectors(list)
}

// ------------------------------------------------------------------------------------
// Statements of the theorems
// ------------------------------------------------------------------------------------

/// `theorem_parse_total`: "parse a selector" returns, which Verus's `decreases` already
/// checked of every function it calls, and what it returns is a selector: one or more
/// well-formed complex selectors. Proven in `super::lemmas`.
pub open spec fn parse_total(source: Seq<u32>) -> bool {
    match parse_a_selector(source) {
        Some(list) => list.len() > 0 && list_wf(list, list.len() as int),
        None => true,
    }
}

/// `theorem_match_total`: in a well-formed document, the algorithm the exec code runs
/// gives the spec's answer for every well-formed complex selector and node, within the
/// work bound. Proven in `super::lemmas`.
pub open spec fn match_total(doc: Document, c: Complex, x: NodeId) -> bool {
    (match_requires(doc, x) && complex_wf(c)) ==> match_work_ensures(
        doc,
        c,
        x,
        dp_match(doc, c, x).0,
        dp_match(doc, c, x).1,
    )
}

/// `theorem_specificity_monotone`: adding a simple selector to a compound selector, or a
/// compound selector to a complex one, never makes it less specific. Proven in
/// `super::lemmas`.
pub open spec fn specificity_monotone(compound: Seq<Simple>, s: Simple, c: Complex, more: Seq<Simple>) -> bool {
    &&& not_more_specific(
        compound_specificity(compound, compound.len() as int),
        compound_specificity(compound.push(s), compound.len() as int + 1),
    )
    &&& not_more_specific(
        specificity(c),
        specificity(
            Complex { compounds: c.compounds.push(more), combinators: c.combinators },
        ),
    )
}

/// `theorem_where_zero`: §17 "The specificity of a :where() pseudo-class is replaced by
/// zero", whatever its argument. Proven in `super::lemmas`.
pub open spec fn where_is_zero(arg: Seq<Complex>, compound: Seq<Simple>) -> bool {
    &&& simple_specificity(Simple::Where { arg }) == zero()
    &&& compound_specificity(compound.push(Simple::Where { arg }), compound.len() as int + 1)
        == compound_specificity(compound, compound.len() as int)
}

/// `theorem_is_most_specific`: §17 "The specificity of an :is() … pseudo-class is replaced by
/// the specificity of the most specific complex selector in its selector list argument": no
/// argument is more specific than it, and it is one argument's specificity (or zero, for an
/// empty argument). Proven in `super::lemmas`.
pub open spec fn is_most_specific(arg: Seq<Complex>) -> bool {
    let s = simple_specificity(Simple::Is { arg });
    &&& forall|i: int| 0 <= i < arg.len() ==> not_more_specific(#[trigger] specificity(arg[i]), s)
    &&& (arg.len() == 0 ==> s == zero())
    &&& (arg.len() > 0 ==> exists|i: int| 0 <= i < arg.len() && s == #[trigger] specificity(arg[i]))
}

} // verus!
