//! HTML §13.2.4 "Parse state" (the insertion mode, the stack of open
//! elements, the list of active formatting elements, the element pointers
//! and the other flags), the tokens the tree builder consumes (§13.2.5's
//! token kinds), the actions it returns, and the algorithms §13.2.4 defines
//! over that state. The modelling choices are listed in [`super`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Tokens (§13.2.5)

/// A token's attribute as the tokenizer emits it: a name and a value.
pub struct TokAttr {
    /// The attribute's name.
    pub name: Seq<u32>,
    /// The attribute's value.
    pub value: Seq<u32>,
}

/// A token as the tokenizer emits it (§13.2.5: "DOCTYPE, start tag, end
/// tag, comment, character, end-of-file", and processing instruction). A
/// missing DOCTYPE name or identifier is `None` ("marked as missing, which
/// is a distinct state from the empty string"). The shape is that of
/// `clazel-html`'s token, so the join maps one to the other field by field.
pub enum Token {
    /// A DOCTYPE token.
    Doctype {
        /// "name"
        name: Option<Seq<u32>>,
        /// "public identifier"
        public_id: Option<Seq<u32>>,
        /// "system identifier"
        system_id: Option<Seq<u32>>,
        /// "force-quirks flag" (on is `true`)
        force_quirks: bool,
    },
    /// A start tag token.
    StartTag {
        /// "tag name"
        name: Seq<u32>,
        /// "list of attributes"
        attrs: Seq<TokAttr>,
        /// "self-closing flag" (set is `true`)
        self_closing: bool,
    },
    /// An end tag token.
    EndTag {
        /// "tag name"
        name: Seq<u32>,
        /// "list of attributes" (a parse error; never read)
        attrs: Seq<TokAttr>,
        /// "self-closing flag" (a parse error; never read)
        self_closing: bool,
    },
    /// A comment token, with its data.
    Comment {
        /// "data"
        data: Seq<u32>,
    },
    /// A processing instruction token, with its target and data.
    ProcessingInstruction {
        /// "target"
        target: Seq<u32>,
        /// "data"
        data: Seq<u32>,
    },
    /// A character token, with its character.
    Character {
        /// The code point.
        c: u32,
    },
    /// The end-of-file token.
    Eof,
}

/// A start or end tag as the tree builder handles it: its name, the name's
/// [`Tag`], its attributes (as DOM attributes with no namespace, until
/// "adjust foreign attributes" gives some one), and its self-closing flag.
pub struct TagTok {
    /// "tag name"
    pub name: Seq<u32>,
    /// `tag_of(name)`
    pub tag: Tag,
    /// The token's attributes.
    pub attrs: Seq<Attr>,
    /// "self-closing flag"
    pub self_closing: bool,
}

/// A token as the tree builder handles it ([`classify`] of a [`Token`]).
pub enum Tok {
    /// A DOCTYPE token.
    Doctype {
        /// "name"
        name: Option<Seq<u32>>,
        /// "public identifier"
        public_id: Option<Seq<u32>>,
        /// "system identifier"
        system_id: Option<Seq<u32>>,
        /// "force-quirks flag"
        force_quirks: bool,
    },
    /// A start tag token.
    Start(TagTok),
    /// An end tag token.
    End(TagTok),
    /// A comment token.
    Comment(Seq<u32>),
    /// A processing instruction token: target, data.
    Pi(Seq<u32>, Seq<u32>),
    /// A character token.
    Char(u32),
    /// The end-of-file token.
    Eof,
}

/// A token attribute as a DOM attribute with no namespace and no prefix.
pub open spec fn tok_attr(a: TokAttr) -> Attr {
    Attr { namespace: None, prefix: None, local_name: a.name, value: a.value }
}

/// Every attribute of a token, as DOM attributes.
pub open spec fn tok_attrs(s: Seq<TokAttr>) -> Seq<Attr> {
    s.map_values(|a: TokAttr| tok_attr(a))
}

/// A tag token as the tree builder handles it.
pub open spec fn tag_tok(name: Seq<u32>, attrs: Seq<TokAttr>, self_closing: bool) -> TagTok {
    TagTok { name, tag: tag_of(name), attrs: tok_attrs(attrs), self_closing }
}

/// The tree builder's view of a token.
pub open spec fn classify(t: Token) -> Tok {
    match t {
        Token::Doctype { name, public_id, system_id, force_quirks } => Tok::Doctype { name, public_id, system_id, force_quirks },
        Token::StartTag { name, attrs, self_closing } => Tok::Start(tag_tok(name, attrs, self_closing)),
        Token::EndTag { name, attrs, self_closing } => Tok::End(tag_tok(name, attrs, self_closing)),
        Token::Comment { data } => Tok::Comment(data),
        Token::ProcessingInstruction { target, data } => Tok::Pi(target, data),
        Token::Character { c } => Tok::Char(c),
        Token::Eof => Tok::Eof,
    }
}

/// A start tag token for `tag`, no attributes (the tokens the rules
/// "insert an HTML element for a … start tag token with no attributes").
pub open spec fn start_tag_named(name: Seq<u32>) -> TagTok {
    TagTok { name, tag: tag_of(name), attrs: seq![], self_closing: false }
}

// ---------------------------------------------------------------------
// Infra and string helpers

/// Infra "ASCII whitespace": U+0009 TAB, U+000A LF, U+000C FF, U+000D CR,
/// or U+0020 SPACE.
pub open spec fn is_ascii_whitespace(c: u32) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

/// Infra "ASCII lowercase" of a code point.
pub open spec fn ascii_lower(c: u32) -> u32 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u32
    } else {
        c
    }
}

/// Infra "ASCII lowercase" of a string.
pub open spec fn ascii_lowercase(s: Seq<u32>) -> Seq<u32> {
    s.map_values(|c: u32| ascii_lower(c))
}

/// Infra "ASCII case-insensitive" match.
pub open spec fn ascii_ci_eq(a: Seq<u32>, b: Seq<u32>) -> bool {
    ascii_lowercase(a) == ascii_lowercase(b)
}

/// The value of the first attribute of `attrs` whose namespace is null and
/// whose local name is `name`, if any.
pub open spec fn attr_value(attrs: Seq<Attr>, name: Seq<u32>) -> Option<Seq<u32>>
    decreases attrs.len(),
{
    if attrs.len() == 0 {
        None
    } else if attrs[0].namespace is None && attrs[0].local_name == name {
        Some(attrs[0].value)
    } else {
        attr_value(attrs.drop_first(), name)
    }
}

/// The token has an attribute named `name`.
pub open spec fn has_attr(t: TagTok, name: Seq<u32>) -> bool {
    attr_value(t.attrs, name) is Some
}

// ---------------------------------------------------------------------
// The insertion mode (§13.2.4.1)

/// "The insertion mode is a state variable": "initial", then the twenty
/// modes §13.2.4.1 lists. (The standard at the pinned commit has 21 modes;
/// "in select" and "in select in table" no longer exist.)
pub enum Mode {
    /// "initial"
    Initial,
    /// "before html"
    BeforeHtml,
    /// "before head"
    BeforeHead,
    /// "in head"
    InHead,
    /// "in head noscript"
    InHeadNoscript,
    /// "after head"
    AfterHead,
    /// "in body"
    InBody,
    /// "text"
    Text,
    /// "in table"
    InTable,
    /// "in table text"
    InTableText,
    /// "in caption"
    InCaption,
    /// "in column group"
    InColumnGroup,
    /// "in table body"
    InTableBody,
    /// "in row"
    InRow,
    /// "in cell"
    InCell,
    /// "in template"
    InTemplate,
    /// "after body"
    AfterBody,
    /// "in frameset"
    InFrameset,
    /// "after frameset"
    AfterFrameset,
    /// "after after body"
    AfterAfterBody,
    /// "after after frameset"
    AfterAfterFrameset,
}

/// The tokenizer states the tree builder switches to (§13.2.6.2, the "in
/// body" `plaintext` rule, the "text" mode's `script` rule, and §13.4 step
/// 10).
pub enum TokenizerState {
    /// "data state"
    Data,
    /// "RCDATA state"
    Rcdata,
    /// "RAWTEXT state"
    Rawtext,
    /// "script data state"
    ScriptData,
    /// "PLAINTEXT state"
    Plaintext,
}

// ---------------------------------------------------------------------
// Elements on the stack and in the list

/// An element the parser created (or the fragment context element), as the
/// stack of open elements and the list of active formatting elements hold
/// it: its node, namespace, local name and the name's [`Tag`], and whether
/// it is an HTML integration point because of its start tag's `encoding`
/// attribute (§13.2.6, the `annotation-xml` cases). Namespace and local name
/// never change after creation, so these are the node's own.
pub struct Elem {
    /// The element's node.
    pub id: NodeId,
    /// Its namespace.
    pub ns: Namespace,
    /// `tag_of(name)`.
    pub tag: Tag,
    /// Its local name.
    pub name: Seq<u32>,
    /// A MathML `annotation-xml` element whose start tag token had an
    /// `encoding` attribute whose value was an ASCII case-insensitive match
    /// for "text/html" or "application/xhtml+xml".
    pub annotation_html: bool,
}

/// The element is an HTML element whose name is `tag`.
pub open spec fn is_html(e: Elem, tag: Tag) -> bool {
    e.ns == Namespace::Html && e.tag == tag
}

/// The element is a MathML element whose name is `tag`.
pub open spec fn is_mathml(e: Elem, tag: Tag) -> bool {
    e.ns == Namespace::MathMl && e.tag == tag
}

/// The element is an SVG element whose name is `tag`.
pub open spec fn is_svg(e: Elem, tag: Tag) -> bool {
    e.ns == Namespace::Svg && e.tag == tag
}

/// An entry of the list of active formatting elements (§13.2.4.3): a marker,
/// or an element "associated with the token for which it was created".
pub enum Fmt {
    /// A marker.
    Marker,
    /// An element and its token.
    Entry {
        /// The element.
        elem: Elem,
        /// "the token for which it was created".
        token: TagTok,
    },
}

/// What the step asks of its driver (Phase 4 "Looking ahead": the parser is
/// a transducer). The parser takes no further step for any of them.
pub enum Action {
    /// §13.2.3.4 "change the encoding" to the encoding (the id
    /// [`EncFns::get_an_encoding`] gives).
    ChangeEncoding(nat),
    /// "prepare the script element" for this node (§13.2.6.4.8, a `script`
    /// end tag in the "text" mode). Phase 4 ignores it; Phase 7 runs it.
    ScriptReady(NodeId),
    /// §13.2.7 "stop parsing", or the node limit was reached.
    StopParsing,
}

/// The functions of other standards the tree builder calls, as parameters
/// (joined later to `clazel-encoding` and `clazel-html`): Encoding §4.2
/// "get an encoding" from a label (an encoding's id, or failure), and HTML
/// §2.6.? "extracting a character encoding from a meta element" from a
/// `content` attribute's value (a label, or nothing).
pub struct EncFns {
    /// Encoding §4.2 "get an encoding".
    pub get_an_encoding: spec_fn(Seq<u32>) -> Option<nat>,
    /// HTML "algorithm for extracting a character encoding from a meta
    /// element".
    pub extract_from_meta: spec_fn(Seq<u32>) -> Option<Seq<u32>>,
}

// ---------------------------------------------------------------------
// The parser (§13.2.4)

/// An insertion location (§13.2.6.1): "a target parent (a Node) and a
/// reference child (a Node or null)".
pub struct Location {
    /// "target parent"
    pub parent: NodeId,
    /// "reference child"
    pub child: Option<NodeId>,
}

/// The parser's state: §13.2.4's parse state, the document it builds, and
/// what the step hands its driver.
pub struct Parser {
    /// The document the parser is associated with.
    pub doc: Document,
    /// §13.2.4.1 "insertion mode".
    pub mode: Mode,
    /// §13.2.4.1 "original insertion mode".
    pub original_mode: Mode,
    /// §13.2.4.1 "stack of template insertion modes"; the last is current.
    pub template_modes: Seq<Mode>,
    /// §13.2.4.2 "stack of open elements"; `open[0]` is the topmost (the
    /// `html` element) and the last is the current node.
    pub open: Seq<Elem>,
    /// §13.2.4.3 "list of active formatting elements"; the last is the most
    /// recently added.
    pub formatting: Seq<Fmt>,
    /// §13.2.4.4 "head element pointer".
    pub head: Option<NodeId>,
    /// §13.2.4.4 "form element pointer".
    pub form: Option<NodeId>,
    /// §13.2.4.5 "fragment context element".
    pub context: Option<Elem>,
    /// §13.2.4.5 "scripting mode" is not Disabled ("the scripting flag" of
    /// the rules that read it).
    pub scripting: bool,
    /// §13.2.4.5 "frameset-ok flag": "ok" is `true`.
    pub frameset_ok: bool,
    /// §13.2.6.1 "foster parenting" enabled.
    pub foster: bool,
    /// §13.2.6.4.10 "pending table character tokens".
    pub pending_table_text: Seq<u32>,
    /// The rules for `pre`, `listing` and `textarea`: "If the next token is a
    /// U+000A LINE FEED (LF) character token, then ignore that token and move
    /// on to the next one."
    pub skip_lf: bool,
    /// A tokenizer state switch this step asks for (applied by the driver
    /// before the next token).
    pub tokenizer: Option<TokenizerState>,
    /// §13.2.3 "confidence" is tentative (`false`: certain).
    pub tentative: bool,
    /// §13.2.4.5 "insertion target redirection map": with no sanitizer, its
    /// only entry is §13.4 step 15's, the fragment case's (root, fragment).
    pub redirect: Option<(NodeId, NodeId)>,
    /// The parser has stopped (§13.2.7, or the node limit).
    pub stopped: bool,
    /// Actions of the current step, in order.
    pub actions: Seq<Action>,
}

// ---------------------------------------------------------------------
// §13.2.4.2 the stack of open elements

/// "The current node is the bottommost node in this stack of open
/// elements."
pub open spec fn current_node(p: Parser) -> Elem {
    p.open.last()
}

/// "The adjusted current node is the parser's fragment context element if
/// that element is non-null and the stack of open elements has only one
/// element in it (fragment case); otherwise, the adjusted current node is
/// the current node."
pub open spec fn adjusted_current_node(p: Parser) -> Elem {
    if p.context is Some && p.open.len() == 1 {
        p.context->Some_0
    } else {
        current_node(p)
    }
}

/// The *special* category (§13.2.4.2).
pub open spec fn is_special(e: Elem) -> bool {
    match e.ns {
        Namespace::Html => match e.tag {
            Tag::Address | Tag::Applet | Tag::Area | Tag::Article | Tag::Aside | Tag::Base | Tag::Basefont | Tag::Bgsound
            | Tag::Blockquote | Tag::Body | Tag::Br | Tag::Button | Tag::Caption | Tag::Center | Tag::Col | Tag::Colgroup
            | Tag::Dd | Tag::Details | Tag::Dir | Tag::Div | Tag::Dl | Tag::Dt | Tag::Embed | Tag::Fieldset | Tag::Figcaption
            | Tag::Figure | Tag::Footer | Tag::Form | Tag::Frame | Tag::Frameset | Tag::H1 | Tag::H2 | Tag::H3 | Tag::H4
            | Tag::H5 | Tag::H6 | Tag::Head | Tag::Header | Tag::Hgroup | Tag::Hr | Tag::Html | Tag::Iframe | Tag::Img
            | Tag::Input | Tag::Keygen | Tag::Li | Tag::Link | Tag::Listing | Tag::Main | Tag::Marquee | Tag::Menu
            | Tag::Meta | Tag::Nav | Tag::Noembed | Tag::Noframes | Tag::Noscript | Tag::Object | Tag::Ol | Tag::P
            | Tag::Param | Tag::Plaintext | Tag::Pre | Tag::Script | Tag::Search | Tag::Section | Tag::Select
            | Tag::Source | Tag::Style | Tag::Summary | Tag::Table | Tag::Tbody | Tag::Td | Tag::Template | Tag::Textarea
            | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Title | Tag::Tr | Tag::Track | Tag::Ul | Tag::Wbr | Tag::Xmp => true,
            _ => false,
        },
        Namespace::MathMl => match e.tag {
            Tag::Mi | Tag::Mo | Tag::Mn | Tag::Ms | Tag::Mtext | Tag::AnnotationXml => true,
            _ => false,
        },
        Namespace::Svg => match e.tag {
            Tag::Foreignobject | Tag::Desc | Tag::Title => true,
            _ => false,
        },
        _ => false,
    }
}

/// The *formatting* category (§13.2.4.2): HTML a, b, big, code, em, font,
/// i, nobr, s, small, strike, strong, tt, u.
pub open spec fn is_formatting_tag(t: Tag) -> bool {
    match t {
        Tag::A | Tag::B | Tag::Big | Tag::Code | Tag::Em | Tag::Font | Tag::I | Tag::Nobr | Tag::S | Tag::Small
        | Tag::Strike | Tag::Strong | Tag::Tt | Tag::U => true,
        _ => false,
    }
}

/// The four scopes of §13.2.4.2.
pub enum Scope {
    /// "has an element in scope"
    Default,
    /// "has an element in list item scope"
    ListItem,
    /// "has an element in button scope"
    Button,
    /// "has an element in table scope"
    Table,
}

/// The element types of a scope's list (§13.2.4.2).
pub open spec fn in_scope_list(e: Elem, s: Scope) -> bool {
    let default = match e.ns {
        // applet, caption, html, table, td, th, marquee, object, select,
        // template
        Namespace::Html => match e.tag {
            Tag::Applet | Tag::Caption | Tag::Html | Tag::Table | Tag::Td | Tag::Th | Tag::Marquee | Tag::Object
            | Tag::Select | Tag::Template => true,
            _ => false,
        },
        // MathML mi, mo, mn, ms, mtext, annotation-xml
        Namespace::MathMl => match e.tag {
            Tag::Mi | Tag::Mo | Tag::Mn | Tag::Ms | Tag::Mtext | Tag::AnnotationXml => true,
            _ => false,
        },
        // SVG foreignObject, desc, title
        Namespace::Svg => match e.tag {
            Tag::Foreignobject | Tag::Desc | Tag::Title => true,
            _ => false,
        },
        _ => false,
    };
    match s {
        Scope::Default => default,
        // "All the element types listed above …", "ol in the HTML namespace",
        // "ul in the HTML namespace"
        Scope::ListItem => default || is_html(e, Tag::Ol) || is_html(e, Tag::Ul),
        // "…", "button in the HTML namespace"
        Scope::Button => default || is_html(e, Tag::Button),
        // "html", "table", "template", each in the HTML namespace
        Scope::Table => is_html(e, Tag::Html) || is_html(e, Tag::Table) || is_html(e, Tag::Template),
    }
}

/// "Have an element target node in a specific scope", with the target
/// given by `is_target`, from the entry at index `i - 1` up: "1. Initialize
/// node to be the current node … 2. If node is target node, terminate in a
/// match state. 3. Otherwise, if node is one of the element types in list,
/// terminate in a failure state. 4. Otherwise, set node to the previous
/// entry in the stack of open elements and return to step 2." (Step 4's
/// note says the loop always ends at the `html` element; an empty remainder
/// is a failure, which never happens on a well-formed stack.)
pub open spec fn in_scope_from(open: Seq<Elem>, i: int, target: spec_fn(Elem) -> bool, s: Scope) -> bool
    decreases i,
{
    if i <= 0 {
        false
    } else if target(open[i - 1]) {
        // 2.
        true
    } else if in_scope_list(open[i - 1], s) {
        // 3.
        false
    } else {
        // 4.
        in_scope_from(open, i - 1, target, s)
    }
}

/// "The stack of open elements has a `tag` element (in the HTML namespace)
/// in scope `s`", the form most rules use ("has a p element in button
/// scope").
pub open spec fn has_in_scope(p: Parser, tag: Tag, s: Scope) -> bool {
    in_scope_from(p.open, p.open.len() as int, |e: Elem| is_html(e, tag), s)
}

/// "The stack of open elements has the element `id` in scope `s`".
pub open spec fn has_node_in_scope(p: Parser, id: NodeId, s: Scope) -> bool {
    in_scope_from(p.open, p.open.len() as int, |e: Elem| e.id == id, s)
}

/// The stack has one of the HTML elements h1 to h6 in scope.
pub open spec fn has_heading_in_scope(p: Parser) -> bool {
    in_scope_from(
        p.open,
        p.open.len() as int,
        |e: Elem| e.ns == Namespace::Html && (e.tag == Tag::H1 || e.tag == Tag::H2 || e.tag == Tag::H3 || e.tag == Tag::H4 || e.tag == Tag::H5 || e.tag == Tag::H6),
        Scope::Default,
    )
}

/// The index of the last entry of `open` satisfying `f` among the first
/// `i`, or -1.
pub open spec fn last_index_where(open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool) -> int
    decreases i,
{
    if i <= 0 {
        -1
    } else if f(open[i - 1]) {
        i - 1
    } else {
        last_index_where(open, i - 1, f)
    }
}

/// The stack has an element satisfying `f`.
pub open spec fn open_has(p: Parser, f: spec_fn(Elem) -> bool) -> bool {
    last_index_where(p.open, p.open.len() as int, f) >= 0
}

/// The stack has an HTML element named `tag` ("there is a template element
/// on the stack of open elements").
pub open spec fn open_has_html(p: Parser, tag: Tag) -> bool {
    open_has(p, |e: Elem| is_html(e, tag))
}

/// The index of `id` on the stack, or -1.
pub open spec fn open_index_of(p: Parser, id: NodeId) -> int {
    last_index_where(p.open, p.open.len() as int, |e: Elem| e.id == id)
}

/// "Pop the current node off the stack of open elements." The standard
/// never pops an empty stack (the `html` element stays on it until parsing
/// stops); popping an empty stack is stated to change nothing, so that
/// `pop` is defined for every parser.
pub open spec fn pop(p: Parser) -> Parser {
    if p.open.len() == 0 {
        p
    } else {
        Parser { open: p.open.drop_last(), ..p }
    }
}

/// "Push element onto the stack of open elements so that it is the new
/// current node."
pub open spec fn push(p: Parser, e: Elem) -> Parser {
    if p.stopped {
        p
    } else {
        Parser { open: p.open.push(e), ..p }
    }
}

/// "Pop elements from the stack of open elements until an HTML element
/// whose name is `tag` has been popped from the stack." (Pops everything if
/// there is none; every rule that says this has first checked there is
/// one.)
pub open spec fn pop_until_popped(p: Parser, tag: Tag) -> Parser
    decreases p.open.len(),
{
    if p.open.len() == 0 {
        p
    } else if is_html(current_node(p), tag) {
        pop(p)
    } else {
        pop_until_popped(pop(p), tag)
    }
}

/// "Pop elements from the stack of open elements until an HTML element
/// whose name is h1 to h6 has been popped."
pub open spec fn pop_until_heading_popped(p: Parser) -> Parser
    decreases p.open.len(),
{
    if p.open.len() == 0 {
        p
    } else if is_heading(current_node(p)) {
        pop(p)
    } else {
        pop_until_heading_popped(pop(p))
    }
}

/// An HTML h1, h2, h3, h4, h5 or h6 element.
pub open spec fn is_heading(e: Elem) -> bool {
    e.ns == Namespace::Html && (e.tag == Tag::H1 || e.tag == Tag::H2 || e.tag == Tag::H3 || e.tag == Tag::H4 || e.tag == Tag::H5
        || e.tag == Tag::H6)
}

/// "Pop elements from the stack of open elements until `id` has been
/// popped."
pub open spec fn pop_until_node_popped(p: Parser, id: NodeId) -> Parser
    decreases p.open.len(),
{
    if p.open.len() == 0 {
        p
    } else if current_node(p).id == id {
        pop(p)
    } else {
        pop_until_node_popped(pop(p), id)
    }
}

/// Pop while the current node satisfies `f` (the "clear the stack back
/// to a … context" algorithms: "while the current node is not …, pop").
pub open spec fn pop_while(p: Parser, f: spec_fn(Elem) -> bool) -> Parser
    decreases p.open.len(),
{
    if p.open.len() == 0 {
        p
    } else if f(current_node(p)) {
        pop_while(pop(p), f)
    } else {
        p
    }
}

/// Remove the entry at index `i` from the stack ("remove node from the
/// stack of open elements").
pub open spec fn remove_open_at(p: Parser, i: int) -> Parser {
    Parser { open: p.open.remove(i), ..p }
}

// ---------------------------------------------------------------------
// §13.2.4.1 reset the insertion mode appropriately

/// "Reset the insertion mode appropriately", from step 3 with `node` the
/// entry at index `i` (and `last` computed at step 3).
pub open spec fn reset_from(p: Parser, i: int) -> Mode
    decreases i,
{
    if i < 0 {
        // Unreachable: step 15 returns when node is the first node.
        Mode::InBody
    } else {
        // 3. "Loop: If node is the first node in the stack of open elements,
        // then set last to true, and, if the parser's fragment context
        // element is non-null, then set node to that element."
        let last = i == 0;
        let node = if last && p.context is Some {
            p.context->Some_0
        } else {
            p.open[i]
        };
        if is_html(node, Tag::Td) && !last || is_html(node, Tag::Th) && !last {
            // 4.
            Mode::InCell
        } else if is_html(node, Tag::Tr) {
            // 5.
            Mode::InRow
        } else if is_html(node, Tag::Tbody) || is_html(node, Tag::Thead) || is_html(node, Tag::Tfoot) {
            // 6.
            Mode::InTableBody
        } else if is_html(node, Tag::Caption) {
            // 7.
            Mode::InCaption
        } else if is_html(node, Tag::Colgroup) {
            // 8.
            Mode::InColumnGroup
        } else if is_html(node, Tag::Table) {
            // 9.
            Mode::InTable
        } else if is_html(node, Tag::Template) {
            // 10. "the current template insertion mode"
            p.template_modes.last()
        } else if is_html(node, Tag::Head) && !last {
            // 11.
            Mode::InHead
        } else if is_html(node, Tag::Body) {
            // 12.
            Mode::InBody
        } else if is_html(node, Tag::Frameset) {
            // 13.
            Mode::InFrameset
        } else if is_html(node, Tag::Html) {
            // 14.1, 14.2
            if p.head is None {
                Mode::BeforeHead
            } else {
                Mode::AfterHead
            }
        } else if last {
            // 15.
            Mode::InBody
        } else {
            // 16. "Let node now be the node before node in the stack of open
            // elements." 17. "Return to the step labeled loop."
            reset_from(p, i - 1)
        }
    }
}

/// §13.2.4.1 "reset the insertion mode appropriately": "1. Let last be
/// false. 2. Let node be the last node in the stack of open elements." then
/// [`reset_from`].
pub open spec fn reset_insertion_mode(p: Parser) -> Parser {
    Parser { mode: reset_from(p, p.open.len() - 1), ..p }
}

// ---------------------------------------------------------------------
// §13.2.4.3 the list of active formatting elements

/// Two lists of attributes are the same up to order: each attribute of one
/// is paired with an identical one of the other ("two elements have the
/// same attributes if all their parsed attributes can be paired such that
/// the two attributes in each pair have identical names, namespaces, and
/// values (the order of the attributes does not matter)"). The tokenizer
/// drops duplicate names, so each list has distinct names and pairing is
/// equality as multisets.
pub open spec fn same_attributes(a: Seq<Attr>, b: Seq<Attr>) -> bool {
    a.to_multiset() == b.to_multiset()
}

/// Entries after the last marker, if any, or anywhere if there are no
/// markers: the index after the last marker among the first `i` entries
/// (0 if none).
pub open spec fn after_last_marker(f: Seq<Fmt>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else if f[i - 1] is Marker {
        i
    } else {
        after_last_marker(f, i - 1)
    }
}

/// The entry is an element with the same tag name, namespace and (token)
/// attributes as `e` created for `t`.
pub open spec fn same_family(x: Fmt, e: Elem, t: TagTok) -> bool {
    match x {
        Fmt::Marker => false,
        Fmt::Entry { elem, token } => elem.name == e.name && elem.ns == e.ns && same_attributes(token.attrs, t.attrs),
    }
}

/// The indices `j` in `from..i` of entries in `e`'s family, in order.
pub open spec fn family_indices(f: Seq<Fmt>, from: int, i: int, e: Elem, t: TagTok) -> Seq<int>
    decreases i - from,
{
    if i <= from {
        seq![]
    } else {
        let rest = family_indices(f, from, i - 1, e, t);
        if same_family(f[i - 1], e, t) {
            rest.push(i - 1)
        } else {
            rest
        }
    }
}

/// §13.2.4.3 "push onto the list of active formatting elements" element
/// `e`, created for token `t`.
pub open spec fn push_formatting(p: Parser, e: Elem, t: TagTok) -> Parser {
    if p.stopped {
        p
    } else {
        let f = p.formatting;
        // 1. "If there are already three elements in the list of active
        // formatting elements after the last marker, if any, or anywhere in
        // the list if there are no markers, that have the same tag name,
        // namespace, and attributes as element, then remove the earliest such
        // element from the list of active formatting elements."
        let fam = family_indices(f, after_last_marker(f, f.len() as int), f.len() as int, e, t);
        let f1 = if fam.len() >= 3 {
            f.remove(fam[0])
        } else {
            f
        };
        // 2. "Add element to the list of active formatting elements."
        Parser { formatting: f1.push(Fmt::Entry { elem: e, token: t }), ..p }
    }
}

/// Insert a marker at the end of the list ("insert a marker at the end of
/// the list of active formatting elements").
pub open spec fn push_marker(p: Parser) -> Parser {
    Parser { formatting: p.formatting.push(Fmt::Marker), ..p }
}

/// The entry is an element that is in the stack of open elements.
pub open spec fn fmt_on_stack(p: Parser, x: Fmt) -> bool {
    match x {
        Fmt::Marker => false,
        Fmt::Entry { elem, .. } => open_index_of(p, elem.id) >= 0,
    }
}

/// §13.2.4.3 "clear the list of active formatting elements up to the last
/// marker": "1. Let entry be the last … entry … 2. Remove entry … 3. If
/// entry was a marker, then stop … 4. Go to step 1."
pub open spec fn clear_to_last_marker(p: Parser) -> Parser
    decreases p.formatting.len(),
{
    if p.formatting.len() == 0 {
        p
    } else {
        // 1., 2.
        let entry = p.formatting.last();
        let q = Parser { formatting: p.formatting.drop_last(), ..p };
        if entry is Marker {
            // 3.
            q
        } else {
            // 4.
            clear_to_last_marker(q)
        }
    }
}

/// The index of the last element entry for `id` in the list, or -1.
pub open spec fn fmt_index_of(f: Seq<Fmt>, i: int, id: NodeId) -> int
    decreases i,
{
    if i <= 0 {
        -1
    } else if f[i - 1] is Entry && f[i - 1]->Entry_elem.id == id {
        i - 1
    } else {
        fmt_index_of(f, i - 1, id)
    }
}

/// The element `id` is in the list of active formatting elements.
pub open spec fn in_formatting(p: Parser, id: NodeId) -> bool {
    fmt_index_of(p.formatting, p.formatting.len() as int, id) >= 0
}

// ---------------------------------------------------------------------
// §13.2.4.4 and §13.2.4.5

/// "An HTML parser is parsing template contents if there is a template
/// element on the stack of open elements, or the parser's fragment context
/// element is a template element."
pub open spec fn parsing_template_contents(p: Parser) -> bool {
    open_has_html(p, Tag::Template) || (p.context is Some && is_html(p.context->Some_0, Tag::Template))
}

/// The adjusted current node is not an element in the HTML namespace: the
/// flag the tokenizer's CDATA section rule reads (`in_foreign_content`; the
/// tokenizer sees no tree, Phase 4 item 4.6).
pub open spec fn in_foreign_content(p: Parser) -> bool {
    p.open.len() > 0 && adjusted_current_node(p).ns != Namespace::Html
}

} // verus!
