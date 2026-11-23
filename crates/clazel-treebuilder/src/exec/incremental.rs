//! An incremental driver (Phase 7 item 7.15): the same proven tokenizer and
//! step as [`super::driver`], over an input stream that a script can edit
//! at the insertion point, and that pauses whenever the step asks for an
//! action.
//!
//! <https://html.spec.whatwg.org/multipage/parsing.html#overview-of-the-parsing-model>
//! (HTML §13.2.1†). Phase 4's design (phase-4.md, "Looking ahead"): "Phase 7
//! acts on [`ScriptReady`], pauses the parser, runs the script and resumes,
//! and `document.write` becomes an edit of the input sequence at the
//! insertion point. The spec is not restructured then: a driver is." This
//! module is that driver; what runs the script is the caller's
//! (`clazel-web`'s `scripting`), which is where §13.2.6.4.8's end tag
//! steps, the script nesting level, the parser pause flag and "the end"
//! (§13.2.7†) are.
//!
//! What it holds, by the standard's names:
//! - the **input stream** (§13.2.3†), preprocessed (§13.2.3.5†) as it
//!   arrives: the document's bytes decoded, and each `document.write`'s
//!   text inserted at the insertion point;
//! - the **insertion point** (§13.2.1†: "a position (just before a
//!   character or just before the end of the input stream) in the input
//!   stream", or undefined): [`Incremental::insertion_point`];
//! - whether the input stream ends with the **explicit "EOF" character**:
//!   [`Incremental::close`]. A document parser's input is closed from the
//!   start (the renderer has the whole response), and a script-created
//!   parser's (`document.open`) is closed by `document.close`;
//! - the tokenizer, the tokens of its last step not yet given to the tree
//!   builder, and the parser.
//!
//! [`Incremental::pump`] runs the loop of [`super::driver`]'s `run` (each
//! token to [`step`] in order, the tokenizer switch and the foreign-content
//! flag applied after each), with three differences:
//! - it returns after any step that asked for actions
//!   ([`Pause::Actions`]): "prepare the script element" runs between that
//!   token and the next, as §13.2.6.4.8 says;
//! - the tokenizer is stepped one state at a time, and is not stepped at or
//!   past the insertion point, nor at the end of an input stream that is not
//!   closed ([`Pause::InsertionPoint`]): `document.write`'s "stopping when the
//!   tokenizer reaches the insertion point", and a script-created parser's
//!   tokenizer that "will wait for an explicit end-of-file token";
//! - it returns [`Pause::Stopped`] once the parser has stopped.
//!
//! Proven: every call meets its callee's precondition (the tokenizer's and
//! the step's contracts, so nothing panics), the invariant [`Incremental::inv`]
//! is kept by every method, every [`Incremental::pump`] ends, and the parser
//! after a pump is the parser before given some tokens by the spec's step
//! (`contract::incremental_pump_ensures`, through
//! `contract::dispatch_seq`).
//!
//! Modelling choices and what is not proven (each listed):
//! - **Not proven equal to `parse`.** With `document.write`, the input is
//!   edited while it is read and the spec's `parse` has no counterpart.
//!   Without it (a closed input, no insertion point, every pause resumed)
//!   the tokens are the ones `driver::run` gives; that is not proven, but
//!   the html5lib tree-construction suite runs through this driver too
//!   (`tests/conformance_tree_construction.rs`), as evidence.
//! - **A tokenizer step that looks ahead** (the markup declaration open
//!   state, named character references) reads the characters after the
//!   insertion point, which in the standard it would wait for. They are the
//!   characters that follow anyway unless a later `document.write` inserts
//!   before them; a step that consumed past the insertion point moves the
//!   insertion point with it ([`Incremental::insert`] inserts at the later
//!   of the two), so no character is skipped.
//! - **Newline normalization** (§13.2.3.5†) is applied to each inserted text
//!   on its own: a CR at the end of one `document.write` and an LF at the
//!   start of the next are two newlines, not one.
//! - **The explicit "EOF" character** is at the end of the input stream:
//!   `document.close` puts it there, and nothing else inserts one.

use super::driver::{reversed, token_of, tokenizer_state};
#[allow(unused_imports)]
use super::spec::*;
use super::stack::in_foreign_content_exec;
use super::step::{new_parser_exec, step};
use super::types::*;
use clazel_html::tokenizer::buffer::{ExecToken as Tok, ExecTokenizer};
use clazel_html::tokenizer::machine::{preprocess_exec, step_exec};
use clazel_html::tokenizer::spec::State;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Why [`Incremental::pump`] returned.
pub enum Pause {
    /// The last token's step asked for these actions (never empty), in
    /// order: "prepare the script element" ([`ExecAction::ScriptReady`]),
    /// "change the encoding", "stop parsing".
    Actions(Vec<ExecAction>),
    /// The tokenizer reached the insertion point, or the end of an input
    /// stream that has no explicit "EOF" character yet, with every token
    /// given to the tree builder.
    InsertionPoint,
    /// The parser has stopped.
    Stopped,
}

/// The actions a [`Pause`] carries, as the spec's.
pub open spec fn pause_actions(r: &Pause) -> Seq<Action> {
    match r {
        Pause::Actions(a) => actions_view(a@),
        _ => seq![],
    }
}

/// The kind of a [`Pause`], as `contract::incremental_pump_ensures` numbers
/// them.
pub open spec fn pause_kind(r: &Pause) -> nat {
    match r {
        Pause::Actions(_) => 0,
        Pause::InsertionPoint => 1,
        Pause::Stopped => 2,
    }
}

/// The tokens given so far witness `contract::incremental_pump_ensures`.
proof fn lemma_pumped(env: EncFns, before: Parser, after: Parser, tokens: Seq<Token>, r: &Pause)
    requires
        crate::contract::dispatch_seq(env, before, tokens) == (after, pause_actions(r)),
        r is Actions ==> pause_actions(r).len() > 0,
        r is InsertionPoint ==> !after.stopped,
        r is Stopped ==> after.stopped,
    ensures
        crate::contract::incremental_pump_ensures(env, before, after, pause_actions(r), pause_kind(r)),
{
    assert(exists|t: Seq<Token>| #[trigger] crate::contract::dispatch_seq(env, before, t) == (after, pause_actions(r)));
}

/// An HTML parser over an input stream that grows at its insertion point.
pub struct Incremental {
    /// The tree builder's state, with the document.
    parser: ParserBuf,
    /// The tokenizer.
    tokenizer: ExecTokenizer,
    /// The spec tokenizer the exec one stands for.
    g: Ghost<clazel_html::tokenizer::spec::Tokenizer>,
    /// The tokens of the tokenizer's last step not yet given to the tree
    /// builder, last first (popping gives the next).
    queue: Vec<Tok>,
    /// The input stream, preprocessed.
    input: Vec<u32>,
    /// The insertion point: an index into `input`, or undefined.
    insertion_point: Option<usize>,
    /// The input stream ends with the explicit "EOF" character.
    closed: bool,
}

impl View for Incremental {
    type V = Parser;

    closed spec fn view(&self) -> Parser {
        self.parser@
    }
}

impl Incremental {
    /// What every method keeps: the parser is reachable (the step's
    /// precondition), the exec tokenizer stands for a spec one whose
    /// position is within the input, and the insertion point is too.
    pub closed spec fn inv(&self) -> bool {
        &&& parser_inv(self.parser@)
        &&& reachable_inv(self.parser@)
        &&& clazel_html::tokenizer::contract::abstracts(self.g@, self.tokenizer@)
        &&& clazel_html::tokenizer::contract::wf(self.input@, self.g@)
        &&& match self.insertion_point {
            Some(ip) => ip <= self.input@.len(),
            None => true,
        }
    }

    /// A parser for a document at `url` (§13.2.4's initial state, with the
    /// scripting flag and the confidence), over `input`, which is the whole
    /// input stream if `closed` (a document's response) and its start
    /// otherwise. The insertion point is undefined; the tokenizer starts in
    /// the data state (§13.2.5.1).
    pub fn new(url: Vec<u32>, scripting: bool, tentative: bool, input: &[u32], closed: bool) -> (r: Incremental)
        ensures
            r.inv(),
            crate::contract::incremental_new_ensures(url@, scripting, tentative, r@),
    {
        let input = preprocess_exec(input);
        let parser = new_parser_exec(url, scripting, tentative);
        // The parser's stack of open elements is empty, so not in foreign
        // content: the tokenizer's flag starts false.
        let tokenizer = ExecTokenizer::new(State::Data, None);
        let ghost g = clazel_html::tokenizer::spec::initial(State::Data, None);
        proof {
            assert(clazel_html::tokenizer::contract::abstracts(g, tokenizer@));
        }
        Incremental {
            parser,
            tokenizer,
            g: Ghost(g),
            queue: Vec::new(),
            input,
            insertion_point: None,
            closed,
        }
    }

    /// The tree builder's state, with the document (read only: only the
    /// parser changes it).
    pub fn parser(&self) -> (r: &ParserBuf)
        ensures
            r@ == self@,
    {
        &self.parser
    }

    /// The tree builder's state, with the document, when the parser is done
    /// with (HTML §13.2.7† "the end" has run, or `document.open` aborted
    /// it).
    pub fn into_parser(self) -> (r: ParserBuf)
        ensures
            r@ == self@,
    {
        self.parser
    }

    /// Whether the parser has stopped.
    pub fn stopped(&self) -> (r: bool)
        ensures
            r == self@.stopped,
    {
        self.parser.stopped
    }

    /// The insertion point: `Some(i)` is just before the input stream's
    /// `i`th character (or its end), `None` is undefined.
    pub fn insertion_point(&self) -> Option<usize> {
        self.insertion_point
    }

    /// Whether the input stream ends with the explicit "EOF" character.
    pub fn is_closed(&self) -> bool {
        self.closed
    }

    /// Sets the insertion point, as §13.2.6.4.8's "let the insertion point
    /// have the value of the old insertion point" does. A point past the
    /// end of the input stream is taken as its end.
    pub fn set_insertion_point(&mut self, ip: Option<usize>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self)@ == old(self)@,
    {
        self.insertion_point = match ip {
            Some(i) => {
                if i <= self.input.len() {
                    Some(i)
                } else {
                    Some(self.input.len())
                }
            },
            None => None,
        };
    }

    /// "Let the insertion point be just before the next input character"
    /// (§13.2.6.4.8, end tag "script", step 5; §13.2.6.4.8 step 10.9;
    /// `document.open` step 17's "just before the end of the input stream"
    /// for an empty stream).
    pub fn set_insertion_point_to_next(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self)@ == old(self)@,
    {
        self.insertion_point = Some(self.tokenizer.pos);
    }

    /// Puts the explicit "EOF" character at the end of the input stream
    /// (`document.close` step 4).
    pub fn close(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self)@ == old(self)@,
    {
        self.closed = true;
    }

    /// "Insert input into the input stream just before the insertion point"
    /// and leave the insertion point after it (`document.write` step 7: the
    /// insertion point stays just before the character that followed it).
    /// `text` is preprocessed (§13.2.3.5) on its own. Returns false and
    /// changes nothing if the insertion point is undefined, or if the input
    /// stream would be longer than `usize` can count.
    pub fn insert(&mut self, text: &[u32]) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self)@ == old(self)@,
    {
        let ip = match self.insertion_point {
            Some(ip) => ip,
            None => return false,
        };
        // A tokenizer step that looked ahead may have consumed past the
        // insertion point (modelling choices): insert after what it read.
        let at = if ip < self.tokenizer.pos {
            self.tokenizer.pos
        } else {
            ip
        };
        let text = preprocess_exec(text);
        let len = self.input.len();
        if len.checked_add(text.len()).is_none() {
            return false;
        }
        let end = match at.checked_add(text.len()) {
            Some(e) => e,
            None => return false,
        };
        let mut text = text;
        let mut rest = self.input.split_off(at);
        self.input.append(&mut text);
        self.input.append(&mut rest);
        self.insertion_point = Some(end);
        true
    }

    /// One tokenizer step (one state's rules, §13.2.5†), its tokens queued.
    fn advance(&mut self)
        requires
            old(self).inv(),
            old(self).queue@.len() == 0,
            !clazel_html::tokenizer::spec::stopped(old(self).input@, old(self).g@),
        ensures
            final(self).inv(),
            final(self)@ == old(self)@,
            final(self).input@ == old(self).input@,
            clazel_html::tokenizer::termination::decreases_ok(final(self).input@, old(self).g@, final(self).g@),
    {
        let ghost g = self.g@;
        proof {
            clazel_html::tokenizer::termination::lemma_step_decreases(self.input@, g);
        }
        let mut out: Vec<Tok> = Vec::new();
        step_exec(&self.input, &mut self.tokenizer, &mut out, Ghost(g));
        self.g = Ghost(clazel_html::tokenizer::spec::step(self.input@, g).0);
        self.queue = reversed(out);
    }

    /// Gives `tok` to the tree builder ([`step`]), then applies the
    /// tokenizer switch the step asked for and the foreign-content flag, as
    /// `driver::run` does after each token.
    fn feed<E: EncFnsExec>(&mut self, env: &E, tok: Tok) -> (actions: Vec<ExecAction>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            (final(self)@, actions_view(actions@)) == dispatch(env.enc(), old(self)@, token_from(tok@)),
            final(self).input@ == old(self).input@,
            final(self).queue@ == old(self).queue@,
            final(self).g@.pos == old(self).g@.pos,
            final(self).g@.done == old(self).g@.done,
            clazel_html::tokenizer::termination::rank(final(self).input@, final(self).g@)
                <= clazel_html::tokenizer::termination::rank(old(self).input@, old(self).g@),
    {
        let et = token_of(tok);
        let actions = step(&mut self.parser, env, et);
        // A switch the step asked for, applied before the next token: one of
        // the five text states, whose rank is the lowest.
        if let Some(s) = &self.parser.tokenizer {
            let st = tokenizer_state(s);
            self.tokenizer.state = st;
            self.g = Ghost(clazel_html::tokenizer::spec::Tokenizer { state: st, ..self.g@ });
        }
        // The flag the CDATA section rule reads.
        let f = in_foreign_content_exec(&self.parser);
        self.tokenizer.in_foreign_content = f;
        self.g = Ghost(clazel_html::tokenizer::spec::Tokenizer { in_foreign_content: f, ..self.g@ });
        actions
    }

    /// Runs the tokenizer and the tree builder until a step asks for
    /// actions, the tokenizer reaches the insertion point (or the end of an
    /// input stream not yet closed), or the parser stops; see [`Pause`].
    pub fn pump<E: EncFnsExec>(&mut self, env: &E) -> (r: Pause)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            crate::contract::incremental_pump_ensures(env.enc(), old(self)@, final(self)@, pause_actions(&r), pause_kind(&r)),
    {
        hide(dispatch);
        hide(parser_inv);
        hide(reachable_inv);
        let ghost env_s = env.enc();
        let ghost p0 = self@;
        let ghost mut tokens: Seq<Token> = seq![];
        let ghost input0 = self.input@;
        proof {
            assert(crate::contract::dispatch_seq(env_s, p0, tokens) == (self@, Seq::<Action>::empty()));
        }
        loop
            invariant
                self.inv(),
                env_s == env.enc(),
                p0 == old(self)@,
                self.input@ == input0,
                crate::contract::dispatch_seq(env_s, p0, tokens) == (self@, Seq::<Action>::empty()),
            decreases
                (if clazel_html::tokenizer::spec::stopped(self.input@, self.g@) {
                    0nat
                } else {
                    1nat
                }),
                clazel_html::tokenizer::termination::remaining(self.input@, self.g@),
                clazel_html::tokenizer::termination::rank(self.input@, self.g@),
                self.queue@.len(),
                (if self@.stopped {
                    0nat
                } else {
                    1nat
                }),
        {
            if self.parser.stopped {
                proof {
                    lemma_pumped(env_s, p0, self@, tokens, &Pause::Stopped);
                }
                return Pause::Stopped;
            }
            let tok = match self.queue.pop() {
                Some(x) => x,
                None => {
                    if self.tokenizer.stopped(&self.input) {
                        Tok::EndOfFile
                    } else {
                        let at_limit = match self.insertion_point {
                            Some(ip) => self.tokenizer.pos >= ip,
                            None => !self.closed && self.tokenizer.pos >= self.input.len(),
                        };
                        if at_limit {
                            proof {
                                lemma_pumped(env_s, p0, self@, tokens, &Pause::InsertionPoint);
                            }
                            return Pause::InsertionPoint;
                        }
                        self.advance();
                        continue;
                    }
                },
            };
            let ghost p_old = self@;
            let ghost tk = token_from(tok@);
            let actions = self.feed(env, tok);
            proof {
                let tokens2 = tokens.push(tk);
                assert(tokens2.drop_last() =~= tokens);
                assert(actions_view(actions@) =~= Seq::<Action>::empty() + actions_view(actions@));
                tokens = tokens2;
                if tk is Eof {
                    reveal(dispatch);
                    crate::theorems::eof::theorem_eof_stops(env_s, p_old);
                }
            }
            if !actions.is_empty() {
                let r = Pause::Actions(actions);
                proof {
                    lemma_pumped(env_s, p0, self@, tokens, &r);
                }
                return r;
            }
            proof {
                assert(actions_view(actions@) =~= Seq::<Action>::empty());
            }
        }
    }
}

} // verus!
