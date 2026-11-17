//! The independent transcription of the grammar hooks and of the entry points on lists
//! ([`super::hooks`]) is the spec's ([`crate::parser::spec`]): "parse something
//! according to a CSS grammar" and "parse a comma-separated list according to a CSS
//! grammar" of a string, "parse a component value", "parse a list of component values"
//! and "parse a comma-separated list of component values" of a list of component
//! values, and of a list of tokens.
//!
//! A grammar is any pair of functions, the spec's and the independent one's, that agree
//! on the lists that a parser could return ([`agrees`]); the theorems then hold for
//! every grammar. [`super::equiv_anb`] proves that `<a-n-plus-b>` is one, and
//! [`theorem_parse_anb_str`] states the hook for it.

#[cfg(verus_only)]
use super::anb::*;
#[cfg(verus_only)]
use super::equiv_anb::*;
#[cfg(verus_only)]
use super::equiv_base::*;
#[cfg(verus_only)]
use super::equiv_good::*;
#[cfg(verus_only)]
use super::equiv_map::*;
#[cfg(verus_only)]
use super::equiv_parser::*;
#[cfg(verus_only)]
use super::equiv_stream::*;
#[cfg(verus_only)]
use super::equiv_tokenizer::*;
#[cfg(verus_only)]
use super::hooks::*;
#[cfg(verus_only)]
use super::parse::*;
#[cfg(verus_only)]
use super::*;
#[cfg(verus_only)]
use crate::parser::spec as ps;
#[cfg(verus_only)]
use crate::tokenizer::spec as t;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The result of a grammar, mapped.
pub open spec fn omap<T, G>(o: Option<T>, f: spec_fn(T) -> G) -> Option<G> {
    match o {
        Some(x) => Some(f(x)),
        None => None,
    }
}

/// A list of results of a grammar, mapped.
pub open spec fn omap_seq<T, G>(s: Seq<Option<T>>, f: spec_fn(T) -> G) -> Seq<Option<G>> {
    Seq::new(s.len(), |i: int| omap(s[i], f))
}

/// A grammar of the spec and one of the independent transcription agree: on a list of
/// component values with numbers that the tokenizer could have made, one matches
/// exactly when the other does, and what they match is the same under `f`.
pub open spec fn agrees<T, G>(
    gs: spec_fn(Seq<ps::ComponentValue>) -> Option<T>,
    gm: spec_fn(Seq<ICv>) -> Option<G>,
    f: spec_fn(T) -> G,
) -> bool {
    forall|v: Seq<ps::ComponentValue>| cvs_ok(v) ==> #[trigger] gm(cvs_of(v)) == omap(gs(v), f)
}

// ---------------------------------------------------------------------
// Lists of component values

/// What a list of component values is read as: the stream that "normalize" makes of it.
pub open spec fn list_stream(g: Seq<ps::ComponentValue>) -> ps::TokenStream {
    ps::TokenStream { tokens: g, source: None }
}

/// "consume a list of component values" of a stream of good items, from `idx`: all the
/// items from there on, after what was collected.
pub proof fn lemma_list_id_loop(g: Seq<ps::ComponentValue>, idx: int, acc: Seq<ps::ComponentValue>)
    requires
        all_good(g, g.len()),
        0 <= idx <= g.len(),
    ensures
        ps::list_of_component_values_loop(list_stream(g), idx, None, false, acc).0 == acc + g.subrange(idx, g.len() as int),
        ps::list_of_component_values_loop(list_stream(g), idx, None, false, acc).1 == g.len(),
    decreases g.len() - idx,
{
    let st = list_stream(g);
    if idx < g.len() {
        lemma_all_good_at(g, g.len(), idx);
        let item = g[idx];
        assert(ps::next_token(st, idx) == item);
        if let ps::ComponentValue::Token { token } = item {
            assert(!(token is Eof));
        }
        assert(!ps::is_open_bracket(item));
        assert(!ps::is_function_token(item));
        assert(!ps::is_stop(item, None::<t::Token>));
        lemma_list_id_loop(g, idx + 1, acc.push(item));
        assert(acc.push(item) + g.subrange(idx + 1, g.len() as int) =~= acc + g.subrange(idx, g.len() as int));
    } else {
        assert(g.subrange(idx, g.len() as int) =~= Seq::<ps::ComponentValue>::empty());
        assert(acc + Seq::<ps::ComponentValue>::empty() =~= acc);
    }
}

/// "parse a list of component values" of a list of good items is the list.
pub proof fn lemma_list_identity(g: Seq<ps::ComponentValue>)
    requires
        all_good(g, g.len()),
    ensures
        ps::parse_a_list_of_component_values(ps::Input::List { list: g }) == g,
{
    lemma_list_id_loop(g, 0, Seq::empty());
    assert(Seq::<ps::ComponentValue>::empty() + g.subrange(0, g.len() as int) =~= g);
}

/// "consume a component value" of a good item at `p` is the item.
pub proof fn lemma_cv_item(g: Seq<ps::ComponentValue>, p: int)
    requires
        all_good(g, g.len()),
        0 <= p < g.len(),
    ensures
        ps::consume_a_component_value(list_stream(g), p) == (g[p], p + 1),
{
    lemma_all_good_at(g, g.len(), p);
    if let ps::ComponentValue::Token { token } = g[p] {
        assert(!(token is Eof));
    }
}

/// "discard whitespace" is the independent one, on a list of good items.
pub proof fn lemma_dw_values(g: Seq<ps::ComponentValue>, p: int)
    requires
        all_good(g, g.len()),
        0 <= p,
    ensures
        ps::discard_whitespace(list_stream(g), p) == i_values_discard_whitespace(cvs_of(g), p as nat) as int,
    decreases g.len() - p,
{
    if p < g.len() {
        lemma_all_good_at(g, g.len(), p);
        lemma_ws_item(g[p]);
        if g[p] == (ps::ComponentValue::Token { token: t::Token::Whitespace }) {
            lemma_dw_values(g, p + 1);
        }
    }
}

/// An item is a `<whitespace-token>` as the mapping says.
pub proof fn lemma_ws_item(x: ps::ComponentValue)
    ensures
        (x == (ps::ComponentValue::Token { token: t::Token::Whitespace })) == (cv_of(x) == ICv::Token(ITok::Whitespace)),
{
    if let ps::ComponentValue::Token { token } = x {
        assert(tok_of(token) == ITok::Whitespace ==> token == t::Token::Whitespace);
    }
}

/// A list of good items is "empty" at `p` when `p` is at its end.
pub proof fn lemma_empty_values(g: Seq<ps::ComponentValue>, p: int)
    requires
        all_good(g, g.len()),
        0 <= p,
    ensures
        ps::is_empty(list_stream(g), p) == (p >= g.len()),
{
    if p < g.len() {
        lemma_all_good_at(g, g.len(), p);
        if let ps::ComponentValue::Token { token } = g[p] {
            assert(!(token is Eof));
        }
    }
}

/// §5.3.7 "parse a component value" of a list of component values.
pub proof fn theorem_values_parse_component_value(g: Seq<ps::ComponentValue>)
    requires
        all_good(g, g.len()),
    ensures
        match ps::parse_a_component_value(ps::Input::List { list: g }) {
            Some(v) => i_values_parse_component_value(cvs_of(g)) == IParsed::Value(cv_of(v)),
            None => i_values_parse_component_value(cvs_of(g)) == IParsed::<ICv>::SyntaxError,
        },
{
    let st = list_stream(g);
    lemma_dw_values(g, 0);
    let start = ps::discard_whitespace(st, 0);
    lemma_empty_values(g, start);
    if start < g.len() {
        lemma_cv_item(g, start);
        lemma_dw_values(g, start + 1);
        lemma_empty_values(g, ps::discard_whitespace(st, start + 1));
    }
}

/// §5.3.8 "parse a list of component values" of a list of component values.
pub proof fn theorem_values_parse_list_of_component_values(g: Seq<ps::ComponentValue>)
    requires
        all_good(g, g.len()),
    ensures
        cvs_of(ps::parse_a_list_of_component_values(ps::Input::List { list: g }))
            == i_values_parse_list_of_component_values(cvs_of(g)),
{
    lemma_list_identity(g);
}

/// The index of the first comma of a list from `p` on (its length if there is none).
pub open spec fn first_comma(vs: Seq<ICv>, p: nat) -> nat
    decreases (if vs.len() > p { vs.len() - p } else { 0 }),
{
    if p >= vs.len() {
        vs.len()
    } else if vs[p as int] == ICv::Token(ITok::Comma) {
        p
    } else {
        first_comma(vs, p + 1)
    }
}

/// An item is a `<comma-token>` as the mapping says.
pub proof fn lemma_comma_item(x: ps::ComponentValue)
    ensures
        (x == (ps::ComponentValue::Token { token: t::Token::Comma })) == (cv_of(x) == ICv::Token(ITok::Comma)),
{
    if let ps::ComponentValue::Token { token } = x {
        assert(tok_of(token) == ITok::Comma ==> token == t::Token::Comma);
    }
}

/// The first comma is at or after the start, within the list, and is a comma unless
/// it is the end.
pub proof fn lemma_first_comma(vs: Seq<ICv>, p: nat)
    requires
        p <= vs.len(),
    ensures
        p <= first_comma(vs, p) <= vs.len(),
        first_comma(vs, p) < vs.len() ==> vs[first_comma(vs, p) as int] == ICv::Token(ITok::Comma),
        forall|k: int| p <= k < first_comma(vs, p) ==> vs[k] != ICv::Token(ITok::Comma),
    decreases vs.len() - p,
{
    if p < vs.len() && vs[p as int] != ICv::Token(ITok::Comma) {
        lemma_first_comma(vs, p + 1);
    }
}

/// The mapping of lists respects what is added to them and what is cut from them.
pub proof fn lemma_cvs_concat(a: Seq<ps::ComponentValue>, b: Seq<ps::ComponentValue>)
    ensures
        cvs_of(a + b) == cvs_of(a) + cvs_of(b),
{
    assert(cvs_of(a + b) =~= cvs_of(a) + cvs_of(b));
}

/// The mapping of a part of a list is the part of the mapping.
pub proof fn lemma_cvs_sub(v: Seq<ps::ComponentValue>, i: int, j: int)
    requires
        0 <= i <= j <= v.len(),
    ensures
        cvs_of(v.subrange(i, j)) == cvs_of(v).subrange(i, j),
{
    assert(cvs_of(v.subrange(i, j)) =~= cvs_of(v).subrange(i, j));
}

/// "consume a list of component values" with a `<comma-token>` as the stop token of a
/// stream of good items: the items up to the first comma.
pub proof fn lemma_list_comma_loop(g: Seq<ps::ComponentValue>, idx: int, acc: Seq<ps::ComponentValue>)
    requires
        all_good(g, g.len()),
        0 <= idx <= g.len(),
    ensures
        ps::list_of_component_values_loop(list_stream(g), idx, Some(t::Token::Comma), false, acc).0
            == acc + g.subrange(idx, first_comma(cvs_of(g), idx as nat) as int),
        ps::list_of_component_values_loop(list_stream(g), idx, Some(t::Token::Comma), false, acc).1
            == first_comma(cvs_of(g), idx as nat) as int,
        idx <= first_comma(cvs_of(g), idx as nat) <= g.len(),
    decreases g.len() - idx,
{
    let st = list_stream(g);
    let vs = cvs_of(g);
    if idx < g.len() {
        lemma_all_good_at(g, g.len(), idx);
        let item = g[idx];
        lemma_comma_item(item);
        if let ps::ComponentValue::Token { token } = item {
            assert(!(token is Eof));
        }
        assert(!ps::is_open_bracket(item));
        assert(!ps::is_function_token(item));
        if item == (ps::ComponentValue::Token { token: t::Token::Comma }) {
            assert(first_comma(vs, idx as nat) == idx);
            assert(g.subrange(idx, idx) =~= Seq::<ps::ComponentValue>::empty());
            assert(acc + Seq::<ps::ComponentValue>::empty() =~= acc);
        } else {
            lemma_list_comma_loop(g, idx + 1, acc.push(item));
            assert(first_comma(vs, idx as nat) == first_comma(vs, (idx + 1) as nat));
            let q = first_comma(vs, idx as nat) as int;
            assert(acc.push(item) + g.subrange(idx + 1, q) =~= acc + g.subrange(idx, q));
        }
    } else {
        assert(first_comma(vs, idx as nat) == g.len());
        assert(g.subrange(idx, g.len() as int) =~= Seq::<ps::ComponentValue>::empty());
        assert(acc + Seq::<ps::ComponentValue>::empty() =~= acc);
    }
}

/// The split of a list at its commas goes to the first comma with what it collected.
pub proof fn lemma_split_run(vs: Seq<ICv>, p: nat, group: Seq<ICv>, groups: Seq<Seq<ICv>>)
    requires
        p <= vs.len(),
    ensures
        i_values_comma_split(vs, p, group, groups) == i_values_comma_split(
            vs,
            first_comma(vs, p),
            group + vs.subrange(p as int, first_comma(vs, p) as int),
            groups,
        ),
    decreases vs.len() - p,
{
    lemma_first_comma(vs, p);
    if p < vs.len() && vs[p as int] != ICv::Token(ITok::Comma) {
        lemma_first_comma(vs, p + 1);
        lemma_split_run(vs, p + 1, group + seq![vs[p as int]], groups);
        let q = first_comma(vs, p);
        assert(first_comma(vs, p + 1) == q);
        assert((group + seq![vs[p as int]]) + vs.subrange(p as int + 1, q as int) =~= group + vs.subrange(p as int, q as int));
    } else {
        assert(vs.subrange(p as int, p as int) =~= Seq::<ICv>::empty());
        assert(group + Seq::<ICv>::empty() =~= group);
    }
}

/// The loop of "parse a comma-separated list of component values" of a list of good
/// items is the independent split.
pub proof fn lemma_comma_equal(g: Seq<ps::ComponentValue>, p: int, groups: Seq<Seq<ps::ComponentValue>>)
    requires
        all_good(g, g.len()),
        0 <= p <= g.len(),
    ensures
        groups_of(ps::comma_separated_list_loop(list_stream(g), p, groups)) == i_values_comma_split(
            cvs_of(g),
            p as nat,
            seq![],
            groups_of(groups),
        ),
    decreases g.len() - p,
{
    let st = list_stream(g);
    let vs = cvs_of(g);
    lemma_empty_values(g, p);
    if p < g.len() {
        lemma_list_comma_loop(g, p, Seq::empty());
        lemma_first_comma(vs, p as nat);
        let q = first_comma(vs, p as nat) as int;
        let lst = g.subrange(p, q);
        assert(Seq::<ps::ComponentValue>::empty() + lst =~= lst);
        lemma_split_run(vs, p as nat, seq![], groups_of(groups));
        lemma_cvs_sub(g, p, q);
        assert(Seq::<ICv>::empty() + vs.subrange(p, q) =~= vs.subrange(p, q));
        if q < g.len() {
            lemma_comma_item(g[q]);
            assert(g[q] == (ps::ComponentValue::Token { token: t::Token::Comma }));
            lemma_empty_values(g, q);
            assert(ps::discard_a_token(st, q) == q + 1);
            assert(ps::moved(p, q + 1) == q + 1);
            lemma_comma_equal(g, q + 1, groups.push(lst));
            assert(groups_of(groups.push(lst)) =~= groups_of(groups).push(cvs_of(lst)));
            assert(i_values_comma_split(vs, q as nat, vs.subrange(p, q), groups_of(groups)) == i_values_comma_split(
                vs,
                (q + 1) as nat,
                seq![],
                groups_of(groups) + seq![vs.subrange(p, q)],
            ));
            assert(groups_of(groups) + seq![vs.subrange(p, q)] =~= groups_of(groups).push(cvs_of(lst)));
        } else {
            lemma_empty_values(g, q);
            assert(ps::discard_a_token(st, q) == q);
            assert(ps::moved(p, q) == q);
            lemma_comma_equal(g, q, groups.push(lst));
            assert(groups_of(groups.push(lst)) =~= groups_of(groups).push(cvs_of(lst)));
            assert(vs.subrange(p, q).len() > 0);
            assert(groups_of(groups) + seq![vs.subrange(p, q)] =~= groups_of(groups).push(cvs_of(lst)));
        }
    } else {
        assert(groups_of(groups) =~= groups_of(groups));
    }
}

/// §5.3.9 "parse a comma-separated list of component values" of a list of component
/// values.
pub proof fn theorem_values_parse_comma_separated_list(g: Seq<ps::ComponentValue>)
    requires
        all_good(g, g.len()),
    ensures
        groups_of(ps::parse_a_comma_separated_list_of_component_values(ps::Input::List { list: g }))
            == i_values_parse_comma_separated_list_of_component_values(cvs_of(g)),
{
    lemma_comma_equal(g, 0, Seq::empty());
    assert(groups_of(Seq::<Seq<ps::ComponentValue>>::empty()) =~= Seq::<Seq<ICv>>::empty());
}

// ---------------------------------------------------------------------
// The hooks, on a string

/// "If |input| contains only `<whitespace-token>`s": "discard whitespace" then "empty".
pub proof fn lemma_only_ws(toks: Seq<Lex>, p: nat)
    ensures
        i_empty(toks, i_discard_whitespace(toks, p)) == (forall|k: int|
            p <= k < toks.len() ==> #[trigger] toks[k].tok == ITok::Whitespace),
    decreases i_remaining(toks, p),
{
    if i_next(toks, p) == ITok::Whitespace {
        lemma_only_ws(toks, p + 1);
    }
}

/// The test for only whitespace of the spec, on a string, is the independent one.
pub proof fn lemma_str_only_ws(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        ({
            let (st, index) = ps::normalize(ps::Input::String { string: input });
            ps::is_empty(st, ps::discard_whitespace(st, index)) == i_input_only_whitespace(IInput::Str(ints(input)))
        }),
{
    lemma_normalize(input);
    let (st, index) = ps::normalize(ps::Input::String { string: input });
    lemma_discard_whitespace(st, 0);
    lemma_is_empty(st, ps::discard_whitespace(st, 0) as nat);
    lemma_discard_whitespace_bound(st, 0);
    lemma_only_ws(lex_of(st), 0);
}

/// §5.3.2 "parse something according to a CSS grammar" of a string.
pub proof fn theorem_parse_grammar_str<T, G>(
    input: Seq<u32>,
    gs: spec_fn(Seq<ps::ComponentValue>) -> Option<T>,
    gm: spec_fn(Seq<ICv>) -> Option<G>,
    f: spec_fn(T) -> G,
)
    requires
        code_points(input),
        agrees(gs, gm, f),
    ensures
        i_parse_grammar(IInput::Str(ints(input)), gm) == omap(
            ps::parse_something_according_to_a_css_grammar(ps::Input::String { string: input }, gs),
            f,
        ),
{
    theorem_parse_list_of_component_values_equals(input);
    lemma_parse_list_good(input);
    let list = ps::parse_a_list_of_component_values(ps::Input::String { string: input });
    lemma_all_good_item_ok(list);
    assert(cvs_ok(list));
}

/// §5.3.2 for `<a-n-plus-b>`: parsing a string "as `<a-n-plus-b>`" is the same in both.
pub proof fn theorem_parse_anb_str(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        i_parse_grammar(IInput::Str(ints(input)), |vs: Seq<ICv>| i_anb(vs)) == ps::parse_something_according_to_a_css_grammar(
            ps::Input::String { string: input },
            |v: Seq<ps::ComponentValue>| ps::a_n_plus_b(v),
        ),
{
    let gs = |v: Seq<ps::ComponentValue>| ps::a_n_plus_b(v);
    let gm = |vs: Seq<ICv>| i_anb(vs);
    let f = |x: (int, int)| x;
    assert(agrees(gs, gm, f)) by {
        assert forall|v: Seq<ps::ComponentValue>| cvs_ok(v) implies #[trigger] gm(cvs_of(v)) == omap(gs(v), f) by {
            theorem_a_n_plus_b_equals(v);
            assert(omap(gs(v), f) == gs(v));
        }
    }
    theorem_parse_grammar_str(input, gs, gm, f);
    let r = ps::parse_something_according_to_a_css_grammar(ps::Input::String { string: input }, gs);
    assert(omap(r, f) == r);
}

/// §5.3.3 "parse a comma-separated list according to a CSS grammar" of a string.
pub proof fn theorem_parse_list_grammar_str<T, G>(
    input: Seq<u32>,
    gs: spec_fn(Seq<ps::ComponentValue>) -> Option<T>,
    gm: spec_fn(Seq<ICv>) -> Option<G>,
    f: spec_fn(T) -> G,
)
    requires
        code_points(input),
        agrees(gs, gm, f),
    ensures
        i_parse_list_grammar(IInput::Str(ints(input)), gm) == omap_seq(
            ps::parse_a_comma_separated_list_according_to_a_css_grammar(ps::Input::String { string: input }, gs),
            f,
        ),
{
    lemma_normalize(input);
    lemma_str_only_ws(input);
    let (stream, index) = ps::normalize(ps::Input::String { string: input });
    if ps::is_empty(stream, ps::discard_whitespace(stream, index)) {
        assert(omap_seq(Seq::<Option<T>>::empty(), f) =~= Seq::<Option<G>>::empty());
    } else {
        theorem_parse_comma_separated_list_equals(input);
        lemma_parse_groups_good(input);
        let list = ps::parse_a_comma_separated_list_of_component_values(ps::Input::Stream { stream, index });
        assert(list == ps::parse_a_comma_separated_list_of_component_values(ps::Input::String { string: input }));
        let mine = i_parse_list_grammar(IInput::Str(ints(input)), gm);
        let theirs = ps::parse_a_comma_separated_list_according_to_a_css_grammar(ps::Input::String { string: input }, gs);
        assert(mine =~= omap_seq(theirs, f)) by {
            assert(mine.len() == list.len());
            assert forall|i: int| 0 <= i < list.len() implies mine[i] == omap_seq(theirs, f)[i] by {
                lemma_list_identity(list[i]);
                lemma_all_good_item_ok(list[i]);
                assert(cvs_ok(list[i]));
                assert(gm(cvs_of(list[i])) == omap(gs(list[i]), f));
            }
        }
    }
}

} // verus!
