//! HTML §13.2.1 "Overview of the parsing model": the tokenizer the tree
//! builder is joined to. [`join_fns`] instantiates [`super::dispatch::TokFns`]
//! with `clazel-html`'s tokenizer (its spec, `clazel_html::tokenizer::spec`,
//! which `clazel-html` proves its executable tokenizer equal to), so that
//! `parse(env, join_fns(input), join_start(), …)` is the whole parser over
//! the preprocessed `input`.
//!
//! <https://html.spec.whatwg.org/multipage/parsing.html#overview-of-the-parsing-model>:
//! "the tree construction stage ... can affect the state of the
//! tokenization stage"; §13.2.5: "When a token is emitted, it must
//! immediately be handled by the tree construction stage. The tree
//! construction stage can affect the state of the tokenization stage, and
//! can insert additional characters into the stream."
//!
//! Modelling choices:
//! - **One state step can emit several tokens** (the standard's "emit a
//!   U+003C LESS-THAN SIGN character token, a U+002F SOLIDUS character
//!   token, and a character token for each of the characters in the
//!   temporary buffer"). `clazel-html`'s one-token face
//!   (`tokenizer::spec::next_token`) runs state steps until one emits
//!   tokens and returns all of them. [`JoinState`] keeps the tokens of that
//!   step not yet handed to the tree builder in a queue, and [`join_next`]
//!   hands them out one at a time, in order, before the tokenizer runs
//!   another step. This is the standard's order: each token is handled as
//!   it is emitted, and the tokenizer's next step starts after the
//!   current step's tokens are all emitted.
//! - **A switch or the foreign-content flag set between two tokens of one
//!   step** ([`join_set_state`], [`join_set_foreign`]) changes the
//!   tokenizer's state and leaves the queue as it is: in the standard the
//!   rest of the step's tokens are already decided when the first is
//!   handled (the step's actions run in order and the state is read only
//!   when the next input character is consumed), so the change takes
//!   effect from the next step, as here. So nothing depends on whether
//!   the queue is empty when a switch happens.
//! - **After the end-of-file token** the tokenizer has stopped
//!   (`tokenizer::spec::stopped`), and [`join_next`] gives an end-of-file
//!   token again: the stream of tokens has ended. The tree builder stops
//!   parsing at the first end-of-file token (`theorem_eof_stops`), so it
//!   never takes a second one.
//! - **Tokens** are converted field by field ([`token_from`]): the two
//!   token types have the same kinds and fields, under different names.

#[allow(unused_imports)]
use super::spec::*;
use clazel_html::tokenizer::spec as tk;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A token attribute of `clazel-html`'s as the tree builder's: "a name and
/// a value".
pub open spec fn tok_attr_from(a: tk::Attribute) -> TokAttr {
    TokAttr { name: a.name, value: a.value }
}

/// Every attribute of a tag token, in order.
pub open spec fn tok_attrs_from(s: Seq<tk::Attribute>) -> Seq<TokAttr> {
    s.map_values(|a: tk::Attribute| tok_attr_from(a))
}

/// A token of `clazel-html`'s tokenizer as the tree builder's: the same
/// token (§13.2.5 "the output of the tokenization step is a series of zero
/// or more of the following tokens"), field by field.
pub open spec fn token_from(t: tk::Token) -> Token {
    match t {
        tk::Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
            name,
            public_id: public_identifier,
            system_id: system_identifier,
            force_quirks,
        },
        tk::Token::StartTag { tag_name, self_closing, attributes } => Token::StartTag {
            name: tag_name,
            attrs: tok_attrs_from(attributes),
            self_closing,
        },
        tk::Token::EndTag { tag_name, self_closing, attributes } => Token::EndTag {
            name: tag_name,
            attrs: tok_attrs_from(attributes),
            self_closing,
        },
        tk::Token::Comment { data } => Token::Comment { data },
        tk::Token::ProcessingInstruction { target, data } => Token::ProcessingInstruction { target, data },
        tk::Token::Character(c) => Token::Character { c },
        tk::Token::EndOfFile => Token::Eof,
    }
}

/// The tokenizer state a switch the tree builder asks for names: "switch
/// the tokenizer to the RCDATA state" and so on (§13.2.6.2, §13.2.6.4.4,
/// §13.2.6.4.7, §13.4 step 10).
pub open spec fn state_from(s: TokenizerState) -> tk::State {
    match s {
        TokenizerState::Data => tk::State::Data,
        TokenizerState::Rcdata => tk::State::Rcdata,
        TokenizerState::Rawtext => tk::State::Rawtext,
        TokenizerState::ScriptData => tk::State::ScriptData,
        TokenizerState::Plaintext => tk::State::Plaintext,
    }
}

/// The tokenizer as the tree builder sees it: `clazel-html`'s tokenizer
/// state, and the tokens its last step emitted that the tree builder has
/// not handled yet, in order.
pub struct JoinState {
    /// The tokenizer's state.
    pub tokenizer: tk::Tokenizer,
    /// The tokens emitted and not yet handed out, first first.
    pub queue: Seq<tk::Token>,
}

/// The next token: the first queued one, or else the first of the tokens
/// the tokenizer's next step emits (the rest are queued), or an
/// end-of-file token once the tokenizer has stopped.
pub open spec fn join_next(input: Seq<u32>, s: JoinState) -> (JoinState, Token) {
    if s.queue.len() > 0 {
        (JoinState { queue: s.queue.drop_first(), ..s }, token_from(s.queue[0]))
    } else {
        let (t, toks) = tk::next_token(input, s.tokenizer);
        if toks.len() > 0 {
            (JoinState { tokenizer: t, queue: toks.drop_first() }, token_from(toks[0]))
        } else {
            // Only when the tokenizer has stopped.
            (JoinState { tokenizer: t, queue: seq![] }, Token::Eof)
        }
    }
}

/// "Switch the tokenizer to the … state".
pub open spec fn join_set_state(s: JoinState, st: TokenizerState) -> JoinState {
    JoinState { tokenizer: tk::Tokenizer { state: state_from(st), ..s.tokenizer }, ..s }
}

/// §13.2.5.42 markup declaration open state: "If there is an adjusted
/// current node and it is not an element in the HTML namespace", the
/// tokenizer's `in_foreign_content` flag.
pub open spec fn join_set_foreign(s: JoinState, f: bool) -> JoinState {
    JoinState { tokenizer: tk::Tokenizer { in_foreign_content: f, ..s.tokenizer }, ..s }
}

/// [`TokFns`] instantiated by `clazel-html`'s tokenizer over the
/// preprocessed `input` (§13.2.3.5).
pub open spec fn join_fns(input: Seq<u32>) -> TokFns<JoinState> {
    TokFns {
        next: |s: JoinState| join_next(input, s),
        set_state: |s: JoinState, st: TokenizerState| join_set_state(s, st),
        set_foreign: |s: JoinState, f: bool| join_set_foreign(s, f),
    }
}

/// The tokenizer before the first token: in the data state (§13.2.5.1:
/// "The state machine must start in the data state"), no start tag
/// emitted yet, at the start of the input, nothing queued.
pub open spec fn join_start() -> JoinState {
    JoinState { tokenizer: tk::initial(tk::State::Data, None), queue: seq![] }
}

} // verus!
