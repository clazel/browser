//! The exec parse state, tokens, actions and outcomes, each with a view to
//! the spec type of the same role ([`Parser`], [`Token`], [`Tok`],
//! [`Action`], [`Outcome`]), and the copies and comparisons of the spec's
//! enums (which have no `Clone` or `PartialEq`).

use super::names::*;
#[allow(unused_imports)]
use super::spec::*;
use clazel_dom::exec::{Arena, ExecAttr};
#[cfg(verus_only)]
use clazel_dom::exec::{attrs_view, opt_str_view};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Copies and comparisons of the spec's enums

/// A copy of a namespace.
pub fn copy_ns(n: &Namespace) -> (r: Namespace)
    ensures
        r == *n,
{
    match n {
        Namespace::Html => Namespace::Html,
        Namespace::MathMl => Namespace::MathMl,
        Namespace::Svg => Namespace::Svg,
        Namespace::XLink => Namespace::XLink,
        Namespace::Xml => Namespace::Xml,
        Namespace::Xmlns => Namespace::Xmlns,
    }
}

/// Whether two namespaces are equal.
pub fn ns_eq(a: &Namespace, b: &Namespace) -> (r: bool)
    ensures
        r == (*a == *b),
{
    matches!(
        (a, b),
        (Namespace::Html, Namespace::Html) | (Namespace::MathMl, Namespace::MathMl) | (Namespace::Svg, Namespace::Svg) | (
            Namespace::XLink,
            Namespace::XLink,
        ) | (Namespace::Xml, Namespace::Xml) | (Namespace::Xmlns, Namespace::Xmlns)
    )
}

/// Whether two optional namespaces are equal.
pub fn opt_ns_eq(a: &Option<Namespace>, b: &Option<Namespace>) -> (r: bool)
    ensures
        r == (*a == *b),
{
    match (a, b) {
        (Some(x), Some(y)) => ns_eq(x, y),
        (None, None) => true,
        _ => false,
    }
}

/// A copy of an optional namespace.
pub fn copy_opt_ns(n: &Option<Namespace>) -> (r: Option<Namespace>)
    ensures
        r == *n,
{
    let mut r = None;
    if let Some(x) = n {
        r = Some(copy_ns(x));
    }
    r
}

/// A copy of an insertion mode.
pub fn copy_mode(m: &Mode) -> (r: Mode)
    ensures
        r == *m,
{
    match m {
        Mode::Initial => Mode::Initial,
        Mode::BeforeHtml => Mode::BeforeHtml,
        Mode::BeforeHead => Mode::BeforeHead,
        Mode::InHead => Mode::InHead,
        Mode::InHeadNoscript => Mode::InHeadNoscript,
        Mode::AfterHead => Mode::AfterHead,
        Mode::InBody => Mode::InBody,
        Mode::Text => Mode::Text,
        Mode::InTable => Mode::InTable,
        Mode::InTableText => Mode::InTableText,
        Mode::InCaption => Mode::InCaption,
        Mode::InColumnGroup => Mode::InColumnGroup,
        Mode::InTableBody => Mode::InTableBody,
        Mode::InRow => Mode::InRow,
        Mode::InCell => Mode::InCell,
        Mode::InTemplate => Mode::InTemplate,
        Mode::AfterBody => Mode::AfterBody,
        Mode::InFrameset => Mode::InFrameset,
        Mode::AfterFrameset => Mode::AfterFrameset,
        Mode::AfterAfterBody => Mode::AfterAfterBody,
        Mode::AfterAfterFrameset => Mode::AfterAfterFrameset,
    }
}

/// A copy of a code point string.
pub fn copy_str(s: &[u32]) -> (r: Vec<u32>)
    ensures
        r@ == s@,
{
    vstd::slice::slice_to_vec(s)
}

/// A copy of an optional code point string.
pub fn copy_opt_str(s: &Option<Vec<u32>>) -> (r: Option<Vec<u32>>)
    ensures
        opt_str_view(r) == opt_str_view(*s),
{
    let mut r = None;
    if let Some(v) = s {
        r = Some(copy_str(v.as_slice()));
    }
    r
}

/// Whether two optional strings are equal.
pub fn opt_str_eq(a: &Option<Vec<u32>>, b: &Option<Vec<u32>>) -> (r: bool)
    ensures
        r == (opt_str_view(*a) == opt_str_view(*b)),
{
    match (a, b) {
        (Some(x), Some(y)) => u32s_eq(x.as_slice(), y.as_slice()),
        (None, None) => true,
        _ => false,
    }
}

/// A copy of an attribute.
pub fn copy_attr(a: &ExecAttr) -> (r: ExecAttr)
    ensures
        r@ == a@,
{
    ExecAttr {
        namespace: copy_opt_ns(&a.namespace),
        prefix: copy_opt_str(&a.prefix),
        local_name: copy_str(a.local_name.as_slice()),
        value: copy_str(a.value.as_slice()),
    }
}

/// Whether two attributes are equal.
pub fn attr_eq(a: &ExecAttr, b: &ExecAttr) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    opt_ns_eq(&a.namespace, &b.namespace) && opt_str_eq(&a.prefix, &b.prefix) && u32s_eq(
        a.local_name.as_slice(),
        b.local_name.as_slice(),
    ) && u32s_eq(a.value.as_slice(), b.value.as_slice())
}

/// A copy of an attribute list.
pub fn copy_attrs(s: &[ExecAttr]) -> (r: Vec<ExecAttr>)
    ensures
        attrs_view(r@) == attrs_view(s@),
{
    let mut out: Vec<ExecAttr> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] out@[j])@ == s@[j]@,
        decreases s.len() - i,
    {
        if let Some(a) = s.get(i) {
            out.push(copy_attr(a));
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(attrs_view(out@) =~= attrs_view(s@));
    }
    out
}

// ---------------------------------------------------------------------
// Tokens

/// A token's attribute ([`TokAttr`]).
pub struct ExecTokAttr {
    /// The attribute's name.
    pub name: Vec<u32>,
    /// The attribute's value.
    pub value: Vec<u32>,
}

impl View for ExecTokAttr {
    type V = TokAttr;

    open spec fn view(&self) -> TokAttr {
        TokAttr { name: self.name@, value: self.value@ }
    }
}

/// The view of a token's attribute list.
pub open spec fn tok_attrs_view(s: Seq<ExecTokAttr>) -> Seq<TokAttr> {
    s.map_values(|a: ExecTokAttr| a@)
}

/// A token as the tokenizer emits it ([`Token`]).
pub enum ExecToken {
    /// A DOCTYPE token.
    Doctype {
        /// "name"
        name: Option<Vec<u32>>,
        /// "public identifier"
        public_id: Option<Vec<u32>>,
        /// "system identifier"
        system_id: Option<Vec<u32>>,
        /// "force-quirks flag"
        force_quirks: bool,
    },
    /// A start tag token.
    StartTag {
        /// "tag name"
        name: Vec<u32>,
        /// "list of attributes"
        attrs: Vec<ExecTokAttr>,
        /// "self-closing flag"
        self_closing: bool,
    },
    /// An end tag token.
    EndTag {
        /// "tag name"
        name: Vec<u32>,
        /// "list of attributes"
        attrs: Vec<ExecTokAttr>,
        /// "self-closing flag"
        self_closing: bool,
    },
    /// A comment token.
    Comment {
        /// "data"
        data: Vec<u32>,
    },
    /// A processing instruction token.
    ProcessingInstruction {
        /// "target"
        target: Vec<u32>,
        /// "data"
        data: Vec<u32>,
    },
    /// A character token.
    Character {
        /// The code point.
        c: u32,
    },
    /// The end-of-file token.
    Eof,
}

impl View for ExecToken {
    type V = Token;

    open spec fn view(&self) -> Token {
        match self {
            ExecToken::Doctype { name, public_id, system_id, force_quirks } => Token::Doctype {
                name: opt_str_view(*name),
                public_id: opt_str_view(*public_id),
                system_id: opt_str_view(*system_id),
                force_quirks: *force_quirks,
            },
            ExecToken::StartTag { name, attrs, self_closing } => Token::StartTag {
                name: name@,
                attrs: tok_attrs_view(attrs@),
                self_closing: *self_closing,
            },
            ExecToken::EndTag { name, attrs, self_closing } => Token::EndTag {
                name: name@,
                attrs: tok_attrs_view(attrs@),
                self_closing: *self_closing,
            },
            ExecToken::Comment { data } => Token::Comment { data: data@ },
            ExecToken::ProcessingInstruction { target, data } => Token::ProcessingInstruction { target: target@, data: data@ },
            ExecToken::Character { c } => Token::Character { c: *c },
            ExecToken::Eof => Token::Eof,
        }
    }
}

/// A tag token as the tree builder handles it ([`TagTok`]).
pub struct ExecTagTok {
    /// "tag name"
    pub name: Vec<u32>,
    /// `tag_of(name)`
    pub tag: Tag,
    /// The token's attributes.
    pub attrs: Vec<ExecAttr>,
    /// "self-closing flag"
    pub self_closing: bool,
}

impl View for ExecTagTok {
    type V = TagTok;

    open spec fn view(&self) -> TagTok {
        TagTok { name: self.name@, tag: self.tag, attrs: attrs_view(self.attrs@), self_closing: self.self_closing }
    }
}

/// A copy of a tag token.
pub fn copy_tagtok(t: &ExecTagTok) -> (r: ExecTagTok)
    ensures
        r@ == t@,
{
    ExecTagTok {
        name: copy_str(t.name.as_slice()),
        tag: copy_tag(&t.tag),
        attrs: copy_attrs(t.attrs.as_slice()),
        self_closing: t.self_closing,
    }
}

/// A token as the tree builder handles it ([`Tok`]).
pub enum ExecTok {
    /// A DOCTYPE token.
    Doctype {
        /// "name"
        name: Option<Vec<u32>>,
        /// "public identifier"
        public_id: Option<Vec<u32>>,
        /// "system identifier"
        system_id: Option<Vec<u32>>,
        /// "force-quirks flag"
        force_quirks: bool,
    },
    /// A start tag token.
    Start(ExecTagTok),
    /// An end tag token.
    End(ExecTagTok),
    /// A comment token.
    Comment(Vec<u32>),
    /// A processing instruction token: target, data.
    Pi(Vec<u32>, Vec<u32>),
    /// A character token.
    Char(u32),
    /// The end-of-file token.
    Eof,
}

impl View for ExecTok {
    type V = Tok;

    open spec fn view(&self) -> Tok {
        match self {
            ExecTok::Doctype { name, public_id, system_id, force_quirks } => Tok::Doctype {
                name: opt_str_view(*name),
                public_id: opt_str_view(*public_id),
                system_id: opt_str_view(*system_id),
                force_quirks: *force_quirks,
            },
            ExecTok::Start(t) => Tok::Start(t@),
            ExecTok::End(t) => Tok::End(t@),
            ExecTok::Comment(d) => Tok::Comment(d@),
            ExecTok::Pi(t, d) => Tok::Pi(t@, d@),
            ExecTok::Char(c) => Tok::Char(*c),
            ExecTok::Eof => Tok::Eof,
        }
    }
}

/// The token's attributes as DOM attributes, moving the strings
/// ([`tok_attrs`]).
pub fn tok_attrs_exec(attrs: Vec<ExecTokAttr>) -> (r: Vec<ExecAttr>)
    ensures
        attrs_view(r@) == tok_attrs(tok_attrs_view(attrs@)),
{
    let ghost orig = attrs@;
    let mut attrs = attrs;
    let mut out: Vec<ExecAttr> = Vec::new();
    let mut i: usize = 0;
    while i < attrs.len()
        invariant
            attrs@.len() == orig.len(),
            i <= attrs@.len(),
            out@.len() == i,
            forall|j: int| i <= j < orig.len() ==> #[trigger] attrs@[j] == orig[j],
            forall|j: int| 0 <= j < i ==> (#[trigger] out@[j])@ == tok_attr(orig[j]@),
        decreases attrs@.len() - i,
    {
        let mut tmp = ExecTokAttr { name: Vec::new(), value: Vec::new() };
        attrs.set_and_swap(i, &mut tmp);
        out.push(ExecAttr { namespace: None, prefix: None, local_name: tmp.name, value: tmp.value });
        // Never saturates: i < attrs.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(attrs_view(out@) =~= tok_attrs(tok_attrs_view(orig)));
    }
    out
}

/// [`classify`]: the tree builder's view of a token, moving its strings.
pub fn classify_exec(t: ExecToken) -> (r: ExecTok)
    ensures
        r@ == classify(t@),
{
    match t {
        ExecToken::Doctype { name, public_id, system_id, force_quirks } => ExecTok::Doctype {
            name,
            public_id,
            system_id,
            force_quirks,
        },
        ExecToken::StartTag { name, attrs, self_closing } => {
            let tag = tag_of_exec(name.as_slice());
            ExecTok::Start(ExecTagTok { name, tag, attrs: tok_attrs_exec(attrs), self_closing })
        },
        ExecToken::EndTag { name, attrs, self_closing } => {
            let tag = tag_of_exec(name.as_slice());
            ExecTok::End(ExecTagTok { name, tag, attrs: tok_attrs_exec(attrs), self_closing })
        },
        ExecToken::Comment { data } => ExecTok::Comment(data),
        ExecToken::ProcessingInstruction { target, data } => ExecTok::Pi(target, data),
        ExecToken::Character { c } => ExecTok::Char(c),
        ExecToken::Eof => ExecTok::Eof,
    }
}

// ---------------------------------------------------------------------
// Elements, the list of active formatting elements, actions

/// An element on the stack or in the list ([`Elem`]).
pub struct ExecElem {
    /// The element's node.
    pub id: usize,
    /// Its namespace.
    pub ns: Namespace,
    /// `tag_of(name)`.
    pub tag: Tag,
    /// Its local name.
    pub name: Vec<u32>,
    /// An HTML integration point by its `encoding` attribute.
    pub annotation_html: bool,
}

impl View for ExecElem {
    type V = Elem;

    open spec fn view(&self) -> Elem {
        Elem { id: self.id, ns: self.ns, tag: self.tag, name: self.name@, annotation_html: self.annotation_html }
    }
}

/// A copy of an element record.
pub fn copy_elem(e: &ExecElem) -> (r: ExecElem)
    ensures
        r@ == e@,
{
    ExecElem {
        id: e.id,
        ns: copy_ns(&e.ns),
        tag: copy_tag(&e.tag),
        name: copy_str(e.name.as_slice()),
        annotation_html: e.annotation_html,
    }
}

/// The view of a sequence of element records.
pub open spec fn elems_view(s: Seq<ExecElem>) -> Seq<Elem> {
    s.map_values(|e: ExecElem| e@)
}

/// The view of an optional element record.
pub open spec fn opt_elem_view(e: Option<ExecElem>) -> Option<Elem> {
    match e {
        Some(x) => Some(x@),
        None => None,
    }
}

/// An entry of the list of active formatting elements ([`Fmt`]).
pub enum ExecFmt {
    /// A marker.
    Marker,
    /// An element and its token.
    Entry {
        /// The element.
        elem: ExecElem,
        /// "the token for which it was created".
        token: ExecTagTok,
    },
}

impl View for ExecFmt {
    type V = Fmt;

    open spec fn view(&self) -> Fmt {
        match self {
            ExecFmt::Marker => Fmt::Marker,
            ExecFmt::Entry { elem, token } => Fmt::Entry { elem: elem@, token: token@ },
        }
    }
}

/// The view of the list of active formatting elements.
pub open spec fn fmts_view(s: Seq<ExecFmt>) -> Seq<Fmt> {
    s.map_values(|f: ExecFmt| f@)
}

/// What the step asks of its driver ([`Action`]).
pub enum ExecAction {
    /// "change the encoding" to this encoding id.
    ChangeEncoding(u64),
    /// "prepare the script element" for this node.
    ScriptReady(usize),
    /// "stop parsing".
    StopParsing,
}

impl View for ExecAction {
    type V = Action;

    open spec fn view(&self) -> Action {
        match self {
            ExecAction::ChangeEncoding(e) => Action::ChangeEncoding(*e as nat),
            ExecAction::ScriptReady(n) => Action::ScriptReady(*n),
            ExecAction::StopParsing => Action::StopParsing,
        }
    }
}

/// The view of a sequence of actions.
pub open spec fn actions_view(s: Seq<ExecAction>) -> Seq<Action> {
    s.map_values(|a: ExecAction| a@)
}

/// A copy of a tokenizer state.
pub fn copy_tokenizer_state(s: &TokenizerState) -> (r: TokenizerState)
    ensures
        r == *s,
{
    match s {
        TokenizerState::Data => TokenizerState::Data,
        TokenizerState::Rcdata => TokenizerState::Rcdata,
        TokenizerState::Rawtext => TokenizerState::Rawtext,
        TokenizerState::ScriptData => TokenizerState::ScriptData,
        TokenizerState::Plaintext => TokenizerState::Plaintext,
    }
}

// ---------------------------------------------------------------------
// The parser

/// The parser's state ([`Parser`]), with the document as a `clazel-dom`
/// arena. Every field is public: the insertion modes set the flags and the
/// mode directly, and use this module's helpers for the stack, the list
/// and the document.
pub struct ParserBuf {
    /// The document.
    pub arena: Arena,
    /// "insertion mode".
    pub mode: Mode,
    /// "original insertion mode".
    pub original_mode: Mode,
    /// "stack of template insertion modes".
    pub template_modes: Vec<Mode>,
    /// "stack of open elements".
    pub open: Vec<ExecElem>,
    /// "list of active formatting elements".
    pub formatting: Vec<ExecFmt>,
    /// "head element pointer".
    pub head: Option<usize>,
    /// "form element pointer".
    pub form: Option<usize>,
    /// "fragment context element".
    pub context: Option<ExecElem>,
    /// The scripting flag.
    pub scripting: bool,
    /// "frameset-ok flag".
    pub frameset_ok: bool,
    /// "foster parenting".
    pub foster: bool,
    /// "pending table character tokens".
    pub pending_table_text: Vec<u32>,
    /// Ignore a next LF.
    pub skip_lf: bool,
    /// A tokenizer state switch.
    pub tokenizer: Option<TokenizerState>,
    /// The confidence is tentative.
    pub tentative: bool,
    /// "insertion target redirection map".
    pub redirect: Option<(usize, usize)>,
    /// The parser has stopped.
    pub stopped: bool,
    /// Actions of the current step.
    pub actions: Vec<ExecAction>,
}

impl View for ParserBuf {
    type V = Parser;

    open spec fn view(&self) -> Parser {
        Parser {
            doc: self.arena@,
            mode: self.mode,
            original_mode: self.original_mode,
            template_modes: self.template_modes@,
            open: elems_view(self.open@),
            formatting: fmts_view(self.formatting@),
            head: self.head,
            form: self.form,
            context: opt_elem_view(self.context),
            scripting: self.scripting,
            frameset_ok: self.frameset_ok,
            foster: self.foster,
            pending_table_text: self.pending_table_text@,
            skip_lf: self.skip_lf,
            tokenizer: self.tokenizer,
            tentative: self.tentative,
            redirect: self.redirect,
            stopped: self.stopped,
            actions: actions_view(self.actions@),
        }
    }
}

/// What one application of a set of rules leaves to do with the token
/// ([`Outcome`]), the parser being the one the rules mutated in place.
pub enum ExecOutcome {
    /// The token is handled.
    Done,
    /// "Reprocess the token".
    Reprocess(ExecTok),
    /// "Process the token using the rules for the m insertion mode".
    Using(Mode, ExecTok),
}

/// The spec outcome of an exec outcome whose parser is `p`.
pub open spec fn outcome_view(o: ExecOutcome, p: Parser) -> Outcome {
    match o {
        ExecOutcome::Done => Outcome::Done(p),
        ExecOutcome::Reprocess(t) => Outcome::Reprocess(p, t@),
        ExecOutcome::Using(m, t) => Outcome::Using(m, p, t@),
    }
}

// ---------------------------------------------------------------------
// Encoding functions

/// The view of an optional encoding id.
pub open spec fn opt_enc_view(r: Option<u64>) -> Option<nat> {
    match r {
        Some(e) => Some(e as nat),
        None => None,
    }
}

/// The exec counterpart of [`EncFns`]: methods equal to the spec functions
/// of [`EncFnsExec::enc`] (joined later to `clazel-encoding`).
pub trait EncFnsExec {
    /// The spec the methods implement.
    spec fn enc(&self) -> EncFns;

    /// [`EncFns::get_an_encoding`].
    fn get_an_encoding(&self, label: &[u32]) -> (r: Option<u64>)
        ensures
            opt_enc_view(r) == (self.enc().get_an_encoding)(label@),
    ;

    /// [`EncFns::extract_from_meta`].
    fn extract_from_meta(&self, content: &[u32]) -> (r: Option<Vec<u32>>)
        ensures
            opt_str_view(r) == (self.enc().extract_from_meta)(content@),
    ;
}

} // verus!
