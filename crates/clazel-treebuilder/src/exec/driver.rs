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
//! This is the exec counterpart of the spec's `parse_steps` with
//! `TokFns` instantiated by `clazel-html`'s tokenizer. Proven here: every
//! call meets its callee's precondition (so the tokenizer and the step keep
//! their contracts and invariants, and nothing panics), and the loop ends.
//! Not proven: that the result equals the spec's `parse` (the tokenizer
//! emits a list of tokens per call where `TokFns::next` gives one; a switch
//! is only ever asked for after a start tag, which a tokenizer step emits
//! alone, so the two agree, but that is not a theorem here). The
//! conformance test (`tests/conformance_tree_construction.rs`) runs the
//! html5lib tree-construction suite through these functions.
//!
//! Termination: the tokenizer's measure (characters left, rank of its
//! state) goes down on every call of `next_token` that does not stop it
//! (`termination::lemma_next_token_decreases`), and a switch only ever
//! sets one of the five text states, whose rank is 0, the lowest; the
//! foreign-content flag is not part of the measure. Nothing recurses.

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
fn reversed<T>(v: Vec<T>) -> (r: Vec<T>) {
    let mut v = v;
    let mut r: Vec<T> = Vec::new();
    while v.len() > 0
        decreases v.len(),
    {
        match v.pop() {
            Some(x) => r.push(x),
            None => break,
        }
    }
    r
}

/// A tag token's attributes, in order, as the tree builder's.
fn attrs_of(v: Vec<ExecAttribute>) -> (r: Vec<ExecTokAttr>) {
    let mut rev = reversed(v);
    let mut r: Vec<ExecTokAttr> = Vec::new();
    while rev.len() > 0
        decreases rev.len(),
    {
        match rev.pop() {
            Some(a) => r.push(ExecTokAttr { name: a.name, value: a.value }),
            None => break,
        }
    }
    r
}

/// A token of `clazel-html`'s tokenizer as the tree builder's: the same
/// token (§13.2.5 "the output of the tokenization step is a series of zero
/// or more of the following tokens"), field by field.
pub fn token_of(t: Tok) -> (r: ExecToken) {
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

/// Tokenize the preprocessed `input` from `start` and feed every token to
/// [`step`] until the tokenizer or the parser stops; the actions of every
/// step, in order.
fn run<E: EncFnsExec>(env: &E, p: &mut ParserBuf, input: &[u32], start: State) -> (actions: Vec<ExecAction>)
    requires
        parser_inv(old(p)@),
        reachable_inv(old(p)@),
    ensures
        parser_inv(final(p)@),
        reachable_inv(final(p)@),
{
    let mut t = ExecTokenizer::new(start, None);
    t.in_foreign_content = in_foreign_content_exec(p);
    let ghost mut g = t@;
    proof {
        assert(clazel_html::tokenizer::contract::abstracts(g, t@));
    }
    let mut actions: Vec<ExecAction> = Vec::new();
    loop
        invariant
            parser_inv(p@),
            reachable_inv(p@),
            clazel_html::tokenizer::contract::abstracts(g, t@),
            clazel_html::tokenizer::contract::wf(input@, g),
        decreases
            clazel_html::tokenizer::termination::remaining(input@, g),
            clazel_html::tokenizer::termination::rank(input@, g),
    {
        if p.stopped || t.stopped(input) {
            break;
        }
        let ghost g0 = g;
        proof {
            clazel_html::tokenizer::termination::lemma_next_token_decreases(input@, g0);
        }
        let toks = t.next_token(input, Ghost(g0));
        proof {
            g = clazel_html::tokenizer::spec::next_token(input@, g0).0;
        }
        let ghost g1 = g;
        let mut rev = reversed(toks);
        while rev.len() > 0
            invariant
                parser_inv(p@),
                reachable_inv(p@),
                clazel_html::tokenizer::contract::abstracts(g, t@),
                clazel_html::tokenizer::contract::wf(input@, g1),
                !clazel_html::tokenizer::spec::stopped(input@, g1)
                    ==> clazel_html::tokenizer::termination::decreases_ok(input@, g0, g1),
                g.pos == g1.pos,
                g.done == g1.done,
                g.state == g1.state || g.state is Data || g.state is Rcdata || g.state is Rawtext
                    || g.state is ScriptData || g.state is Plaintext,
            decreases rev.len(),
        {
            let tok = match rev.pop() {
                Some(x) => x,
                None => break,
            };
            let mut a = step(p, env, token_of(tok));
            actions.append(&mut a);
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
            }
        }
        if t.stopped(input) {
            break;
        }
    }
    actions
}

/// The document a parser builds from `input` (code points), with the URL,
/// scripting flag and confidence of [`new_parser_exec`], and the actions it
/// asked for, in order. HTML §13.2.3.5 preprocesses the input stream; the
/// tokenizer starts in the data state (§13.2.5.1).
pub fn parse_real<E: EncFnsExec>(env: &E, input: &[u32], url: Vec<u32>, scripting: bool, tentative: bool) -> (r: (
    ParserBuf,
    Vec<ExecAction>,
))
    ensures
        parser_inv(r.0@),
        reachable_inv(r.0@),
{
    let input = preprocess_exec(input);
    let mut p = new_parser_exec(url, scripting, tentative);
    let actions = run(env, &mut p, input.as_slice(), State::Data);
    (p, actions)
}

/// §13.4 the HTML fragment parsing algorithm over `input` (code points)
/// with the context element `ctx`: the parser, the fragment's id (step 23
/// returns its children) and the actions. Step 10's tokenizer state is
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
{
    let input = preprocess_exec(input);
    let (mut p, fragment, st) = fragment_parser_exec(ctx, scripting);
    let start = match st {
        Some(s) => tokenizer_state(&s),
        None => State::Data,
    };
    let actions = run(env, &mut p, input.as_slice(), start);
    (p, fragment, actions)
}

} // verus!
