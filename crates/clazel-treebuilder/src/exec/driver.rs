//! The join of the tokenizer and the tree builder (HTML §13.2.1 "Overview
//! of the parsing model"): [`parse_real`] and [`parse_fragment_real`] run
//! `clazel-html`'s tokenizer ([`ExecTokenizer::next_token`]) and feed each
//! token it emits to the tree builder's [`step`], in order.
//!
//! <https://html.spec.whatwg.org/multipage/parsing.html#overview-of-the-parsing-model>:
//! "the tree construction stage ... can affect the state of the
//! tokenization stage". Between tokens the driver applies the two ways it
//! does:
//! - a tokenizer state switch the step asked for (`Parser::tokenizer`: the
//!   RCDATA, RAWTEXT, script data and PLAINTEXT rules of §13.2.6, and step
//!   10 of §13.4's fragment parsing algorithm), and
//! - §13.2.5.42 markup declaration open state, "If there is an adjusted
//!   current node and it is not an element in the HTML namespace": the
//!   tokenizer's `in_foreign_content` flag, set from the parser after every
//!   token ([`in_foreign_content_exec`]).
//!
//! Proven here: [`parse_real`] and [`parse_fragment_real`] equal the spec's
//! `parse` and `parse_fragment` with `TokFns` instantiated by
//! `clazel-html`'s tokenizer (`spec::base::join::join_fns`, from
//! `join_start`, over the preprocessed input), for every bound on the
//! tokens from some bound on (`contract::parse_real_ensures`,
//! `contract::parse_fragment_real_ensures`); the parser has stopped at the
//! end. One call of `next_token` returns the tokens of one tokenizer step,
//! which the driver keeps in a queue and hands to [`step`] one at a time,
//! applying the switch and the flag after each, exactly as `join_fns`
//! does; the loop invariant relates the driver's state (parser, actions,
//! tokenizer, queue) to `parse_steps` after the tokens it has handled.
//! Also proven: every call meets its callee's precondition (so the
//! tokenizer and the step keep their contracts and invariants, and nothing
//! panics), and the loop ends. The conformance test
//! (`tests/conformance_tree_construction.rs`) runs the html5lib
//! tree-construction suite through these functions, so its results are
//! results of the spec's `parse` and `parse_fragment`.
//!
//! Termination: the tokenizer's measure (characters left, rank of its
//! state) goes down on every call of `next_token` that does not stop it
//! (`termination::lemma_next_token_decreases`), and a switch only ever
//! sets one of the five text states, whose rank is 0, the lowest; the
//! foreign-content flag is not part of the measure. Handing out a queued
//! token shortens the queue. Once the tokenizer has stopped, the parser is
//! fed an end-of-file token, which stops it (`theorem_eof_stops`). Nothing
//! recurses.

#[allow(unused_imports)]
use super::spec::*;
use super::stack::in_foreign_content_exec;
use super::step::{ExecContext, fragment_parser_exec, new_parser_exec, step};
use super::types::*;
use clazel_html::tokenizer::buffer::{ExecAttribute, ExecToken as Tok, ExecTokenizer};
use clazel_html::tokenizer::machine::preprocess_exec;
use clazel_html::tokenizer::spec::State;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The tokenizer state for a switch the tree builder asks for.
pub fn tokenizer_state(s: &TokenizerState) -> (r: State)
    ensures
        r == state_from(*s),
        r is Data || r is Rcdata || r is Rawtext || r is ScriptData || r is Plaintext,
{
    match s {
        TokenizerState::Data => State::Data,
        TokenizerState::Rcdata => State::Rcdata,
        TokenizerState::Rawtext => State::Rawtext,
        TokenizerState::ScriptData => State::ScriptData,
        TokenizerState::Plaintext => State::Plaintext,
    }
}

/// The list `v` in reverse order (popping it gives the first first).
fn reversed<T>(v: Vec<T>) -> (r: Vec<T>)
    ensures
        r@.len() == v@.len(),
        forall|i: int| 0 <= i < v@.len() ==> #[trigger] r@[i] == v@[v@.len() - 1 - i],
{
    let ghost v0 = v@;
    let mut v = v;
    let mut r: Vec<T> = Vec::new();
    while !v.is_empty()
        invariant
            v@.len() + r@.len() == v0.len(),
            v@ == v0.subrange(0, v@.len() as int),
            forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i] == v0[v0.len() - 1 - i],
        decreases v.len(),
    {
        if let Some(x) = v.pop() {
            r.push(x);
        }
    }
    r
}

/// A tag token's attributes, in order, as the tree builder's.
fn attrs_of(v: Vec<ExecAttribute>) -> (r: Vec<ExecTokAttr>)
    ensures
        tok_attrs_view(r@) == tok_attrs_from(clazel_html::tokenizer::buffer::attributes_view(v@)),
{
    let ghost v0 = v@;
    let mut rev = reversed(v);
    let mut r: Vec<ExecTokAttr> = Vec::new();
    while !rev.is_empty()
        invariant
            rev@.len() + r@.len() == v0.len(),
            forall|i: int| 0 <= i < rev@.len() ==> #[trigger] rev@[i] == v0[v0.len() - 1 - i],
            forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i]@ == tok_attr_from(v0[i]@),
        decreases rev.len(),
    {
        if let Some(a) = rev.pop() {
            r.push(ExecTokAttr { name: a.name, value: a.value });
        }
    }
    assert(tok_attrs_view(r@) =~= tok_attrs_from(clazel_html::tokenizer::buffer::attributes_view(v0)));
    r
}

/// A token of `clazel-html`'s tokenizer as the tree builder's: the same
/// token (§13.2.5 "the output of the tokenization step is a series of zero
/// or more of the following tokens"), field by field ([`token_from`]).
pub fn token_of(t: Tok) -> (r: ExecToken)
    ensures
        r@ == token_from(t@),
{
    match t {
        Tok::Doctype { name, public_identifier, system_identifier, force_quirks } => ExecToken::Doctype {
            name,
            public_id: public_identifier,
            system_id: system_identifier,
            force_quirks,
        },
        Tok::StartTag { tag_name, self_closing, attributes } => ExecToken::StartTag {
            name: tag_name,
            attrs: attrs_of(attributes),
            self_closing,
        },
        Tok::EndTag { tag_name, self_closing, attributes } => ExecToken::EndTag {
            name: tag_name,
            attrs: attrs_of(attributes),
            self_closing,
        },
        Tok::Comment { data } => ExecToken::Comment { data },
        Tok::ProcessingInstruction { target, data } => ExecToken::ProcessingInstruction { target, data },
        Tok::Character(c) => ExecToken::Character { c },
        Tok::EndOfFile => ExecToken::Eof,
    }
}

/// The queue of tokens a reversed list holds: its last first.
pub open spec fn queue_of(rev: Seq<Tok>) -> Seq<clazel_html::tokenizer::spec::Token> {
    Seq::new(rev.len(), |i: int| rev[rev.len() - 1 - i]@)
}

/// The spec tokenizer state the driver's tokenizer `g` and reversed queue
/// `rev` stand for.
pub open spec fn join_state(g: clazel_html::tokenizer::spec::Tokenizer, rev: Seq<Tok>) -> JoinState {
    JoinState { tokenizer: g, queue: queue_of(rev) }
}

/// The tokenizer state after a step that left the parser `p1`, from the
/// state `s1` the step's token was taken from: the switch the step asked
/// for, then the foreign-content flag (`parse_steps`, with [`join_fns`]).
pub open spec fn join_after(s1: JoinState, p1: Parser) -> JoinState {
    let s2 = match p1.tokenizer {
        Some(st) => join_set_state(s1, st),
        None => s1,
    };
    join_set_foreign(s2, in_foreign_content(p1))
}

/// One iteration of `parse_steps` with [`join_fns`] from a parser that has
/// not stopped: the next token ([`join_next`]), the step, the switch and
/// the flag ([`join_after`]).
proof fn lemma_parse_steps_unfold(env: EncFns, input: Seq<u32>, s: JoinState, p: Parser, acts: Seq<Action>, m: nat)
    requires
        !p.stopped,
    ensures
        parse_steps(env, join_fns(input), s, p, acts, m + 1) == parse_steps(
            env,
            join_fns(input),
            join_after(join_next(input, s).0, dispatch(env, p, join_next(input, s).1).0),
            dispatch(env, p, join_next(input, s).1).0,
            acts + dispatch(env, p, join_next(input, s).1).1,
            m,
        ),
{
}

/// The driver's loop invariant carries over one iteration: if from `s`,
/// `p` and `acts` every bound `m` gives what `k + m` gives from the start,
/// then from the state after one more token (`s1`, `p1`, `a`: the next
/// token's, and the step's) every `m` gives what `k + 1 + m` gives.
proof fn lemma_invariant_step(
    env: EncFns,
    input: Seq<u32>,
    s0: JoinState,
    p0: Parser,
    k: nat,
    s: JoinState,
    p: Parser,
    acts: Seq<Action>,
    s1: JoinState,
    p1: Parser,
    a: Seq<Action>,
)
    requires
        !p.stopped,
        forall|m: nat| #[trigger]
            parse_steps(env, join_fns(input), s, p, acts, m) == parse_steps(env, join_fns(input), s0, p0, seq![], k + m),
        s1 == join_next(input, s).0,
        (p1, a) == dispatch(env, p, join_next(input, s).1),
    ensures
        forall|m: nat| #[trigger]
            parse_steps(env, join_fns(input), join_after(s1, p1), p1, acts + a, m) == parse_steps(
                env,
                join_fns(input),
                s0,
                p0,
                seq![],
                (k + 1) + m,
            ),
{
    assert forall|m: nat| #[trigger]
        parse_steps(env, join_fns(input), join_after(s1, p1), p1, acts + a, m) == parse_steps(
            env,
            join_fns(input),
            s0,
            p0,
            seq![],
            (k + 1) + m,
        ) by {
        lemma_parse_steps_unfold(env, input, s, p, acts, m);
        assert(parse_steps(env, join_fns(input), s, p, acts, (m + 1) as nat) == parse_steps(
            env,
            join_fns(input),
            s0,
            p0,
            seq![],
            k + (m + 1),
        ));
        assert(k + (m + 1) == (k + 1) + m);
    }
}

/// At the end of the loop: a stopped parser, and the invariant, give the
/// whole parse for every bound from `k` on.
proof fn lemma_invariant_end(
    env: EncFns,
    input: Seq<u32>,
    s0: JoinState,
    p0: Parser,
    k: nat,
    s: JoinState,
    p: Parser,
    acts: Seq<Action>,
)
    requires
        p.stopped,
        forall|m: nat| #[trigger]
            parse_steps(env, join_fns(input), s, p, acts, m) == parse_steps(env, join_fns(input), s0, p0, seq![], k + m),
    ensures
        crate::contract::steps_settle(env, join_fns(input), s0, p0, p, acts, k),
{
    assert forall|m: nat| k <= m implies #[trigger] parse_steps(env, join_fns(input), s0, p0, seq![], m) == (p, acts) by {
        let m2 = (m - k) as nat;
        assert(parse_steps(env, join_fns(input), s, p, acts, m2) == parse_steps(env, join_fns(input), s0, p0, seq![], k + m2));
    }
}

/// The tokenizer's termination measure (`clazel-html`'s, with "stopped"
/// first) and the queue's length, compared lexicographically: `(g1, l1)`
/// is below `(g0, l0)`.
pub open spec fn measure_lt(
    input: Seq<u32>,
    g1: clazel_html::tokenizer::spec::Tokenizer,
    l1: nat,
    g0: clazel_html::tokenizer::spec::Tokenizer,
    l0: nat,
) -> bool {
    let (a1, a0) = (
        clazel_html::tokenizer::spec::stopped(input, g1),
        clazel_html::tokenizer::spec::stopped(input, g0),
    );
    let (b1, b0) = (
        clazel_html::tokenizer::termination::remaining(input, g1),
        clazel_html::tokenizer::termination::remaining(input, g0),
    );
    let (c1, c0) = (
        clazel_html::tokenizer::termination::rank(input, g1),
        clazel_html::tokenizer::termination::rank(input, g0),
    );
    (a1 && !a0) || (a1 == a0 && (b1 < b0 || (b1 == b0 && (c1 < c0 || (c1 == c0 && l1 < l0)))))
}

/// The next token for the tree builder ([`join_next`]) from the tokenizer
/// `t` (standing for `g0`) and the reversed queue `rev`: the first queued
/// one, or the first of the tokens the tokenizer's next step emits (the
/// rest queued), or end-of-file once the tokenizer has stopped. Either
/// the measure goes down or the token is end-of-file and nothing changed.
fn next_tok(t: &mut ExecTokenizer, rev: &mut Vec<Tok>, input: &[u32], Ghost(g0): Ghost<clazel_html::tokenizer::spec::Tokenizer>) -> (tok: Tok)
    requires
        clazel_html::tokenizer::contract::abstracts(g0, old(t)@),
        clazel_html::tokenizer::contract::wf(input@, g0),
    ensures
        ({
            let (s1, token) = join_next(input@, join_state(g0, old(rev)@));
            &&& clazel_html::tokenizer::contract::abstracts(s1.tokenizer, final(t)@)
            &&& clazel_html::tokenizer::contract::wf(input@, s1.tokenizer)
            &&& queue_of(final(rev)@) == s1.queue
            &&& token_from(tok@) == token
            &&& measure_lt(input@, s1.tokenizer, final(rev)@.len(), g0, old(rev)@.len()) || (tok@ is EndOfFile
                && s1.tokenizer == g0 && final(rev)@.len() == 0 && old(rev)@.len() == 0)
        }),
{
    let ghost rev0 = rev@;
    if let Some(x) = rev.pop() {
        assert(queue_of(rev@) =~= queue_of(rev0).drop_first());
        x
    } else if t.stopped(input) {
        Tok::EndOfFile
    } else {
        proof {
            clazel_html::tokenizer::termination::lemma_next_token_decreases(input@, g0);
        }
        let toks = t.next_token(input, Ghost(g0));
        let ghost g1 = clazel_html::tokenizer::spec::next_token(input@, g0).0;
        let mut r = reversed(toks);
        assert(queue_of(r@) =~= clazel_html::tokenizer::buffer::tokens_view(toks@));
        let ghost r1 = r@;
        let x = match r.pop() {
            Some(x) => {
                assert(queue_of(r@) =~= queue_of(r1).drop_first());
                x
            },
            None => Tok::EndOfFile,
        };
        *rev = r;
        x
    }
}

/// Tokenize the preprocessed `input` from the tokenizer `t` (standing for
/// the spec state `s0`, nothing queued) and feed every token to [`step`]
/// until the parser stops; the actions of every step, in order. HTML
/// §13.2.5: "When a token is emitted, it must immediately be handled by the
/// tree construction stage": the tokens one call of
/// [`ExecTokenizer::next_token`] returns are handed to [`step`] one at a
/// time, and the step's switch and the foreign-content flag are applied to
/// the tokenizer after each ([`join_fns`]). Once the tokenizer has
/// stopped, the parser is fed an end-of-file token, as [`join_next`] gives,
/// which stops it.
fn run<E: EncFnsExec>(env: &E, p: &mut ParserBuf, input: &[u32], t: ExecTokenizer, Ghost(s0): Ghost<JoinState>) -> (actions: Vec<
    ExecAction,
>)
    requires
        parser_inv(old(p)@),
        reachable_inv(old(p)@),
        clazel_html::tokenizer::contract::abstracts(s0.tokenizer, t@),
        clazel_html::tokenizer::contract::wf(input@, s0.tokenizer),
        s0.queue.len() == 0,
    ensures
        parser_inv(final(p)@),
        reachable_inv(final(p)@),
        final(p)@.stopped,
        exists|n: nat|
            crate::contract::steps_settle(env.enc(), join_fns(input@), s0, old(p)@, final(p)@, actions_view(actions@), n),
{
    hide(parse_steps);
    hide(dispatch);
    hide(join_next);
    hide(parser_inv);
    hide(reachable_inv);
    let ghost env_s = env.enc();
    let ghost p0 = p@;
    let mut t = t;
    let ghost mut g = s0.tokenizer;
    let mut rev: Vec<Tok> = Vec::new();
    let mut actions: Vec<ExecAction> = Vec::new();
    let ghost mut k: nat = 0;
    proof {
        assert(queue_of(rev@) =~= s0.queue);
        assert(join_state(g, rev@) == s0);
        assert(actions_view(actions@) =~= Seq::<Action>::empty());
    }
    loop
        invariant
            parser_inv(p@),
            reachable_inv(p@),
            clazel_html::tokenizer::contract::abstracts(g, t@),
            clazel_html::tokenizer::contract::wf(input@, g),
            env_s == env.enc(),
            forall|m: nat| #[trigger]
                parse_steps(env_s, join_fns(input@), join_state(g, rev@), p@, actions_view(actions@), m)
                    == parse_steps(env_s, join_fns(input@), s0, p0, seq![], k + m),
        ensures
            p@.stopped,
        decreases
            (if clazel_html::tokenizer::spec::stopped(input@, g) {
                0nat
            } else {
                1nat
            }),
            clazel_html::tokenizer::termination::remaining(input@, g),
            clazel_html::tokenizer::termination::rank(input@, g),
            rev@.len(),
            (if p@.stopped {
                0nat
            } else {
                1nat
            }),
    {
        if p.stopped {
            break;
        }
        let ghost js = join_state(g, rev@);
        let ghost p_old = p@;
        let ghost acts_old = actions_view(actions@);
        let tok = next_tok(&mut t, &mut rev, input, Ghost(g));
        let ghost s1 = join_next(input@, js).0;
        proof {
            g = s1.tokenizer;
            assert(join_state(g, rev@) == s1);
        }
        let mut a = step(p, env, token_of(tok));
        let ghost p1 = p@;
        let ghost av = actions_view(a@);
        actions.append(&mut a);
        proof {
            assert(actions_view(actions@) =~= acts_old + av);
        }
        // A switch the step asked for, applied before the next token.
        if let Some(s) = &p.tokenizer {
            let st = tokenizer_state(s);
            t.state = st;
            proof {
                g = clazel_html::tokenizer::spec::Tokenizer { state: st, ..g };
            }
        }
        // The flag the CDATA section rule reads.
        let f = in_foreign_content_exec(p);
        t.in_foreign_content = f;
        proof {
            g = clazel_html::tokenizer::spec::Tokenizer { in_foreign_content: f, ..g };
            assert(join_state(g, rev@) == join_after(s1, p1));
            assert(token_from(tok@) == join_next(input@, js).1);
            assert((p1, av) == dispatch(env_s, p_old, join_next(input@, js).1));
            lemma_invariant_step(env_s, input@, s0, p0, k, js, p_old, acts_old, s1, p1, av);
            k = k + 1;
            if tok@ is EndOfFile {
                crate::theorems::eof::theorem_eof_stops(env_s, p_old);
            }
        }
    }
    proof {
        lemma_invariant_end(env_s, input@, s0, p0, k, join_state(g, rev@), p@, actions_view(actions@));
    }
    actions
}

/// The document a parser builds from `input` (code points), with the URL,
/// scripting flag and confidence of [`new_parser_exec`], and the actions it
/// asked for, in order: the spec's `parse` with `clazel-html`'s tokenizer.
/// HTML §13.2.3.5 preprocesses the input stream; the tokenizer starts in
/// the data state (§13.2.5.1).
pub fn parse_real<E: EncFnsExec>(env: &E, input: &[u32], url: Vec<u32>, scripting: bool, tentative: bool) -> (r: (
    ParserBuf,
    Vec<ExecAction>,
))
    ensures
        parser_inv(r.0@),
        reachable_inv(r.0@),
        r.0@.stopped,
        crate::contract::parse_real_ensures(env.enc(), input@, url@, scripting, tentative, r.0@.doc, actions_view(r.1@)),
{
    let ghost u = url@;
    let ghost raw = input@;
    let input = preprocess_exec(input);
    let mut p = new_parser_exec(url, scripting, tentative);
    let ghost p0 = p@;
    // The parser starts with an empty stack of open elements, so not in
    // foreign content: the tokenizer's flag starts false, as `join_start`'s.
    let t = ExecTokenizer::new(State::Data, None);
    proof {
        assert(clazel_html::tokenizer::contract::abstracts(join_start().tokenizer, t@));
    }
    let actions = run(env, &mut p, input.as_slice(), t, Ghost(join_start()));
    proof {
        let tf = join_fns(input@);
        let n = choose|n: nat| crate::contract::steps_settle(env.enc(), tf, join_start(), p0, p@, actions_view(actions@), n);
        assert(crate::contract::parse_real_from(env.enc(), raw, u, scripting, tentative, n, p@.doc, actions_view(actions@)));
    }
    (p, actions)
}

/// §13.4 the HTML fragment parsing algorithm over `input` (code points)
/// with the context element `ctx`: the parser, the fragment's id (step 23
/// returns its children) and the actions: the spec's `parse_fragment` with
/// `clazel-html`'s tokenizer. Step 10's tokenizer state is
/// [`fragment_parser_exec`]'s (the data state if none), and step 13's
/// "start the parser and let it run until it has consumed all the
/// characters" is the driver's loop.
pub fn parse_fragment_real<E: EncFnsExec>(env: &E, input: &[u32], ctx: ExecContext, scripting: bool) -> (r: (
    ParserBuf,
    usize,
    Vec<ExecAction>,
))
    ensures
        parser_inv(r.0@),
        reachable_inv(r.0@),
        r.0@.stopped,
        crate::contract::parse_fragment_real_ensures(env.enc(), input@, ctx@, scripting, r.0@.doc, r.1, actions_view(r.2@)),
{
    let ghost c = ctx@;
    let ghost raw = input@;
    let input = preprocess_exec(input);
    let (mut p, fragment, st) = fragment_parser_exec(ctx, scripting);
    let ghost p0 = p@;
    let start = match &st {
        Some(s) => tokenizer_state(s),
        None => State::Data,
    };
    let mut t = ExecTokenizer::new(start, None);
    t.in_foreign_content = in_foreign_content_exec(&p);
    let ghost tf = join_fns(input@);
    let ghost s1 = match st {
        Some(x) => (tf.set_state)(join_start(), x),
        None => join_start(),
    };
    let ghost s2 = (tf.set_foreign)(s1, in_foreign_content(p0));
    proof {
        assert(s2.tokenizer =~= t@);
        assert(clazel_html::tokenizer::contract::abstracts(s2.tokenizer, t@));
    }
    let actions = run(env, &mut p, input.as_slice(), t, Ghost(s2));
    proof {
        let n = choose|n: nat| crate::contract::steps_settle(env.enc(), tf, s2, p0, p@, actions_view(actions@), n);
        assert(crate::contract::parse_fragment_real_from(env.enc(), raw, c, scripting, n, p@.doc, fragment, actions_view(actions@)));
    }
    (p, fragment, actions)
}

} // verus!
