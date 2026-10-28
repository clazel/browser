//! The executable tokenizer's state and tokens, their views as the spec's
//! [`Tokenizer`] and [`Token`], and the actions the states share, each
//! proven to do what its spec function does.

#[allow(unused_imports)]
use super::spec::*;
pub use crate::charref::exec::at32;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An attribute, viewed as [`Attribute`].
pub struct ExecAttribute {
    /// name
    pub name: Vec<u32>,
    /// value
    pub value: Vec<u32>,
}

impl View for ExecAttribute {
    type V = Attribute;

    open spec fn view(&self) -> Attribute {
        Attribute { name: self.name@, value: self.value@ }
    }
}

/// The views of a list of attributes.
pub open spec fn attributes_view(v: Seq<ExecAttribute>) -> Seq<Attribute> {
    v.map_values(|a: ExecAttribute| a@)
}

/// A token, viewed as [`Token`].
pub enum ExecToken {
    /// A DOCTYPE token.
    Doctype {
        /// name (`None` is missing)
        name: Option<Vec<u32>>,
        /// public identifier
        public_identifier: Option<Vec<u32>>,
        /// system identifier
        system_identifier: Option<Vec<u32>>,
        /// force-quirks flag
        force_quirks: bool,
    },
    /// A start tag token.
    StartTag {
        /// tag name
        tag_name: Vec<u32>,
        /// self-closing flag
        self_closing: bool,
        /// attributes
        attributes: Vec<ExecAttribute>,
    },
    /// An end tag token.
    EndTag {
        /// tag name
        tag_name: Vec<u32>,
        /// self-closing flag
        self_closing: bool,
        /// attributes
        attributes: Vec<ExecAttribute>,
    },
    /// A comment token.
    Comment {
        /// data
        data: Vec<u32>,
    },
    /// A processing instruction token.
    ProcessingInstruction {
        /// target
        target: Vec<u32>,
        /// data
        data: Vec<u32>,
    },
    /// A character token.
    Character(u32),
    /// The end-of-file token.
    EndOfFile,
}

/// The view of an optional string.
pub open spec fn opt_view(o: Option<Vec<u32>>) -> Option<Seq<u32>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

impl View for ExecToken {
    type V = Token;

    open spec fn view(&self) -> Token {
        match self {
            ExecToken::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
                name: opt_view(*name),
                public_identifier: opt_view(*public_identifier),
                system_identifier: opt_view(*system_identifier),
                force_quirks: *force_quirks,
            },
            ExecToken::StartTag { tag_name, self_closing, attributes } => Token::StartTag {
                tag_name: tag_name@,
                self_closing: *self_closing,
                attributes: attributes_view(attributes@),
            },
            ExecToken::EndTag { tag_name, self_closing, attributes } => Token::EndTag {
                tag_name: tag_name@,
                self_closing: *self_closing,
                attributes: attributes_view(attributes@),
            },
            ExecToken::Comment { data } => Token::Comment { data: data@ },
            ExecToken::ProcessingInstruction { target, data } => Token::ProcessingInstruction {
                target: target@,
                data: data@,
            },
            ExecToken::Character(c) => Token::Character(*c),
            ExecToken::EndOfFile => Token::EndOfFile,
        }
    }
}

/// The views of a list of tokens.
pub open spec fn tokens_view(v: Seq<ExecToken>) -> Seq<Token> {
    v.map_values(|t: ExecToken| t@)
}

/// The tokenizer's state, viewed as [`Tokenizer`] (with the character
/// reference code capped, `super::contract::abstracts`).
pub struct ExecTokenizer {
    /// The state machine's state.
    pub state: State,
    /// the return state
    pub return_state: ReturnState,
    /// the temporary buffer
    pub temporary_buffer: Vec<u32>,
    /// the character reference code, capped at 0x110000
    pub character_reference_code: u32,
    /// the current token
    pub current: ExecToken,
    /// the current attribute
    pub current_attribute: ExecAttribute,
    /// whether the current attribute is on the token
    pub attribute_status: AttributeStatus,
    /// the last start tag emitted
    pub last_start_tag: Option<Vec<u32>>,
    /// set by the tree builder: the adjusted current node is not in the
    /// HTML namespace
    pub in_foreign_content: bool,
    /// the next input character's position
    pub pos: usize,
    /// an end-of-file token was emitted
    pub done: bool,
}

impl View for ExecTokenizer {
    type V = Tokenizer;

    open spec fn view(&self) -> Tokenizer {
        Tokenizer {
            state: self.state,
            return_state: self.return_state,
            temporary_buffer: self.temporary_buffer@,
            character_reference_code: self.character_reference_code as nat,
            current: self.current@,
            current_attribute: self.current_attribute@,
            attribute_status: self.attribute_status,
            last_start_tag: opt_view(self.last_start_tag),
            in_foreign_content: self.in_foreign_content,
            pos: self.pos as nat,
            done: self.done,
        }
    }
}

/// A copy of a list of code points.
pub fn copy(v: &Vec<u32>) -> (r: Vec<u32>)
    ensures
        r@ == v@,
{
    let mut r: Vec<u32> = Vec::with_capacity(v.len());
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            r@ == v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        r.push(at32(v.as_slice(), i));
        // Never saturates: i < v.len().
        i = i.saturating_add(1);
    }
    assert(r@ =~= v@);
    r
}

/// A list of code points holding `s`.
pub fn from_slice(s: &[u32]) -> (r: Vec<u32>)
    ensures
        r@ == s@,
{
    let mut r: Vec<u32> = Vec::with_capacity(s.len());
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            r@ == s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        r.push(at32(s, i));
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(r@ =~= s@);
    r
}

/// Append `s` to `v`.
pub fn extend(v: &mut Vec<u32>, s: &Vec<u32>)
    ensures
        final(v)@ == old(v)@ + s@,
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v@ == old(v)@ + s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        v.push(at32(s.as_slice(), i));
        assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i as int).push(s@[i as int]));
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
}

/// Whether two lists of code points are equal.
pub fn eq_codes(a: &Vec<u32>, b: &Vec<u32>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        if at32(a.as_slice(), i) != at32(b.as_slice(), i) {
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    assert(a@ =~= b@);
    true
}

/// Push a token's exec form, keeping the view in step.
pub fn push_token(out: &mut Vec<ExecToken>, t: ExecToken)
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@).push(t@),
        tokens_view(final(out)@) == tokens_view(old(out)@) + seq![t@],
{
    out.push(t);
    assert(tokens_view(out@) =~= tokens_view(old(out)@).push(t@));
    assert(tokens_view(old(out)@).push(t@) =~= tokens_view(old(out)@) + seq![t@]);
}

/// Push a character token.
pub fn push_char(out: &mut Vec<ExecToken>, c: u32)
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@).push(ch(c)),
        tokens_view(final(out)@) == tokens_view(old(out)@) + seq![ch(c)],
{
    push_token(out, ExecToken::Character(c));
}

/// Push one character token per code point of `s`.
pub fn push_chars(out: &mut Vec<ExecToken>, s: &Vec<u32>)
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@) + chars(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            tokens_view(out@) == tokens_view(old(out)@) + chars(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        push_char(out, at32(s.as_slice(), i));
        assert(chars(s@.subrange(0, i + 1)) =~= chars(s@.subrange(0, i as int)).push(ch(s@[i as int])));
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
}

/// What a state's exec function requires: the exec tokenizer stands for
/// the spec tokenizer `st`, which is well formed and has not stopped.
pub open spec fn pre(input: Seq<u32>, st: Tokenizer, v: Tokenizer) -> bool {
    super::contract::abstracts(st, v) && super::contract::wf(input, st) && !stopped(input, st)
}

/// What a state's exec function ensures: it did what the spec step `s`
/// says, to the tokenizer and to the output.
pub open spec fn post(s: Step, v: Tokenizer, before: Seq<ExecToken>, after: Seq<ExecToken>) -> bool {
    super::contract::abstracts(s.0, v) && tokens_view(after) =~= tokens_view(before) + s.1
}

} // verus!
