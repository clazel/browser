//! HTML §13.2.6 "the tree construction dispatcher", "reprocess the token"
//! and "using the rules for", the one-token step `dispatch`, the whole
//! parser `parse` (driven by an abstract tokenizer, [`TokFns`]) and §13.4
//! the HTML fragment parsing algorithm. The modelling choices are listed in
//! [`super`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What one application of a set of rules leaves to do with the token.
pub enum Outcome {
    /// The token is handled.
    Done(Parser),
    /// "Reprocess the token" (possibly changed, as for `image`): process it
    /// again with the rules of the current insertion mode in HTML content.
    Reprocess(Parser, Tok),
    /// "Process the token using the rules for the m insertion mode": the
    /// rules of `m`, leaving the insertion mode as it is.
    Using(Mode, Parser, Tok),
}

/// Which rules handle the token.
pub enum Rules {
    /// The rules of an insertion mode in HTML content (§13.2.6.4).
    Html(Mode),
    /// The rules for parsing tokens in foreign content (§13.2.6.5).
    Foreign,
}

/// The element is a MathML text integration point (§13.2.6): MathML mi,
/// mo, mn, ms or mtext.
pub open spec fn is_mathml_text_integration_point(e: Elem) -> bool {
    e.ns == Namespace::MathMl && (e.tag == Tag::Mi || e.tag == Tag::Mo || e.tag == Tag::Mn || e.tag == Tag::Ms || e.tag == Tag::Mtext)
}

/// The element is an HTML integration point (§13.2.6): a MathML
/// annotation-xml element whose start tag token had an `encoding` attribute
/// matching "text/html" or "application/xhtml+xml", or an SVG
/// foreignObject, desc or title element.
pub open spec fn is_html_integration_point(e: Elem) -> bool {
    (is_mathml(e, Tag::AnnotationXml) && e.annotation_html) || is_svg(e, Tag::Foreignobject) || is_svg(e, Tag::Desc) || is_svg(
        e,
        Tag::Title,
    )
}

/// §13.2.6 the tree construction dispatcher: which rules handle a token as
/// it is emitted.
pub open spec fn dispatcher(p: Parser, t: Tok) -> Rules {
    let a = adjusted_current_node(p);
    if p.open.len() == 0
    // "If the stack of open elements is empty"
    || a.ns == Namespace::Html
    // "If the adjusted current node is an element in the HTML namespace"
    || (is_mathml_text_integration_point(a) && t is Start && t->Start_0.tag != Tag::Mglyph && t->Start_0.tag != Tag::Malignmark)
    // "If the adjusted current node is a MathML text integration point and
    // the token is a start tag whose tag name is neither "mglyph" nor
    // "malignmark""
    || (is_mathml_text_integration_point(a) && t is Char)
    // "If the adjusted current node is a MathML text integration point and
    // the token is a character token"
    || (is_mathml(a, Tag::AnnotationXml) && t is Start && t->Start_0.tag == Tag::Svg)
    // "If the adjusted current node is a MathML annotation-xml element and
    // the token is a start tag whose tag name is "svg""
    || (is_html_integration_point(a) && t is Start)
    // "If the adjusted current node is an HTML integration point and the
    // token is a start tag"
    || (is_html_integration_point(a) && t is Char)
    // "If the adjusted current node is an HTML integration point and the
    // token is a character token"
    || t is Eof
    // "If the token is an end-of-file token"
    {
        // "Process the token according to the rules given in the section
        // corresponding to the current insertion mode in HTML content."
        Rules::Html(p.mode)
    } else {
        // "Otherwise: Process the token according to the rules given in the
        // section for parsing tokens in foreign content."
        Rules::Foreign
    }
}

/// The rules of insertion mode `m` (§13.2.6.4.1 to §13.2.6.4.21).
pub open spec fn mode_rules(env: EncFns, m: Mode, p: Parser, t: Tok) -> Outcome {
    match m {
        Mode::Initial => mode_initial(env, p, t),
        Mode::BeforeHtml => mode_before_html(env, p, t),
        Mode::BeforeHead => mode_before_head(env, p, t),
        Mode::InHead => mode_in_head(env, p, t),
        Mode::InHeadNoscript => mode_in_head_noscript(env, p, t),
        Mode::AfterHead => mode_after_head(env, p, t),
        Mode::InBody => mode_in_body(env, p, t),
        Mode::Text => mode_text(env, p, t),
        Mode::InTable => mode_in_table(env, p, t),
        Mode::InTableText => mode_in_table_text(env, p, t),
        Mode::InCaption => mode_in_caption(env, p, t),
        Mode::InColumnGroup => mode_in_column_group(env, p, t),
        Mode::InTableBody => mode_in_table_body(env, p, t),
        Mode::InRow => mode_in_row(env, p, t),
        Mode::InCell => mode_in_cell(env, p, t),
        Mode::InTemplate => mode_in_template(env, p, t),
        Mode::AfterBody => mode_after_body(env, p, t),
        Mode::InFrameset => mode_in_frameset(env, p, t),
        Mode::AfterFrameset => mode_after_frameset(env, p, t),
        Mode::AfterAfterBody => mode_after_after_body(env, p, t),
        Mode::AfterAfterFrameset => mode_after_after_frameset(env, p, t),
    }
}

/// Apply a set of rules to the token.
pub open spec fn apply_rules(env: EncFns, r: Rules, p: Parser, t: Tok) -> Outcome {
    match r {
        Rules::Html(m) => mode_rules(env, m, p, t),
        Rules::Foreign => foreign_content(env, p, t),
    }
}

/// Apply rules until the token is handled, with at most `fuel` applications;
/// `None` if the fuel runs out. "Reprocess the token" applies the rules of
/// the (new) current insertion mode in HTML content; "using the rules for
/// m" applies m's rules. Parsing stopped by the token's rules ends the
/// loop.
pub open spec fn run(env: EncFns, p: Parser, t: Tok, r: Rules, fuel: nat) -> Option<Parser>
    decreases fuel,
{
    if fuel == 0 {
        None
    } else {
        match apply_rules(env, r, p, t) {
            Outcome::Done(q) => Some(q),
            Outcome::Reprocess(q, t2) => if q.stopped {
                Some(q)
            } else {
                run(env, q, t2, Rules::Html(q.mode), (fuel - 1) as nat)
            },
            Outcome::Using(m, q, t2) => if q.stopped {
                Some(q)
            } else {
                run(env, q, t2, Rules::Html(m), (fuel - 1) as nat)
            },
        }
    }
}

/// The number of rule applications one token is given (see the modelling
/// choices; `theorem_dispatch_total` proves it is never exhausted).
pub open spec fn fuel_bound(p: Parser) -> nat {
    4 * (p.open.len() + p.template_modes.len() + 8)
}

/// The tree construction stage for one token: the dispatcher, then
/// reprocessing as the rules say.
pub open spec fn tree_construction(env: EncFns, p: Parser, t: Tok) -> Parser {
    match run(env, p, t, dispatcher(p, t), fuel_bound(p)) {
        Some(q) => q,
        // Never (`theorem_dispatch_total`); stop parsing if it were.
        None => stop_parsing(p),
    }
}

/// The one-token step (Phase 4 item 4.9): the token is handled by the tree
/// construction stage, and the step returns the new state and the actions
/// for the driver, in order. A step of a stopped parser does nothing. The
/// state's `tokenizer` field is the tokenizer state switch the step asks
/// for, if any.
pub open spec fn dispatch(env: EncFns, p: Parser, token: Token) -> (Parser, Seq<Action>) {
    let p0 = Parser { actions: seq![], tokenizer: None, ..p };
    if p0.stopped {
        (p0, seq![])
    } else if p0.skip_lf {
        // "If the next token is a U+000A LINE FEED (LF) character token, then
        // ignore that token and move on to the next one."
        let p1 = Parser { skip_lf: false, ..p0 };
        if token == (Token::Character { c: 0x0A }) {
            (p1, seq![])
        } else {
            let q = tree_construction(env, p1, classify(token));
            (q, q.actions)
        }
    } else {
        let q = tree_construction(env, p0, classify(token));
        (q, q.actions)
    }
}

// ---------------------------------------------------------------------
// The whole parser

/// The tokenizer as the tree builder drives it: one token at a time, with
/// the state switches of §13.2.6 and the foreign-content flag. `S` is the
/// tokenizer's state, opaque here; `clazel-html`'s tokenizer instantiates
/// these at the join.
#[verifier::reject_recursive_types(S)]
pub struct TokFns<S> {
    /// The next token, and the state after it.
    pub next: spec_fn(S) -> (S, Token),
    /// "Switch the tokenizer to the … state".
    pub set_state: spec_fn(S, TokenizerState) -> S,
    /// Set whether the adjusted current node is not an HTML element (read by
    /// the CDATA section rule of the markup declaration open state).
    pub set_foreign: spec_fn(S, bool) -> S,
}

/// At most `n` more tokens through `dispatch`, accumulating the actions.
/// When `n` runs out the parser stops (`parse_requires` gives `n` as the
/// tokenizer's bound on the tokens it emits, end-of-file included, so this
/// never happens).
pub open spec fn parse_steps<S>(env: EncFns, tf: TokFns<S>, s: S, p: Parser, acts: Seq<Action>, n: nat) -> (Parser, Seq<Action>)
    decreases n,
{
    if p.stopped {
        (p, acts)
    } else if n == 0 {
        let q = stop_parsing(p);
        (q, acts + q.actions)
    } else {
        let (s1, token) = (tf.next)(s);
        let (p1, a) = dispatch(env, p, token);
        let s2 = match p1.tokenizer {
            Some(st) => (tf.set_state)(s1, st),
            None => s1,
        };
        let s3 = (tf.set_foreign)(s2, in_foreign_content(p1));
        parse_steps(env, tf, s3, p1, acts + a, (n - 1) as nat)
    }
}

/// A new parser for a new document with the given URL (§13.2.4: every
/// initial value), its scripting flag and encoding confidence.
pub open spec fn new_parser(url: Seq<u32>, scripting: bool, tentative: bool) -> Parser {
    Parser {
        doc: dom::new_document(url),
        mode: Mode::Initial,
        original_mode: Mode::Initial,
        template_modes: seq![],
        open: seq![],
        formatting: seq![],
        head: None,
        form: None,
        context: None,
        scripting,
        frameset_ok: true,
        foster: false,
        pending_table_text: seq![],
        skip_lf: false,
        tokenizer: None,
        tentative,
        redirect: None,
        stopped: false,
        actions: seq![],
    }
}

/// The whole parser: a new document from the tokenizer's tokens, with at
/// most `n` tokens, and every action in order.
pub open spec fn parse<S>(env: EncFns, tf: TokFns<S>, s0: S, url: Seq<u32>, scripting: bool, tentative: bool, n: nat) -> (Document, Seq<Action>) {
    let (p, acts) = parse_steps(env, tf, s0, new_parser(url, scripting, tentative), seq![], n);
    (p.doc, acts)
}

// ---------------------------------------------------------------------
// §13.4 Parsing HTML fragments

/// The fragment parsing algorithm's context element, as a test or Phase 7
/// gives it: its namespace, local name and attributes, and its node
/// document's mode. (The context element's ancestors are not modelled: it
/// is created in the fragment's arena with no parent; see [`super`].)
pub struct Context {
    /// The context element's namespace.
    pub ns: Namespace,
    /// Its local name.
    pub name: Seq<u32>,
    /// Its attributes.
    pub attrs: Seq<Attr>,
    /// Its node document's mode.
    pub mode: DocumentMode,
}

/// The fragment parser's state before its first token, with the
/// fragment's id and the tokenizer state of step 10 (`None`: the data
/// state).
pub open spec fn fragment_parser(ctx: Context, scripting: bool) -> (Parser, NodeId, Option<TokenizerState>) {
    // 1. to 3.: context is the given element (no shadow roots).
    // 4. "Let document be a Document node whose type is "html"." 5. to 7.:
    // its mode is the context document's mode if quirks or limited-quirks.
    let d0 = dom::set_mode(dom::new_document(seq![]), ctx.mode);
    // The context element, in the same arena with no parent.
    let ctx_tok = TagTok { name: ctx.name, tag: tag_of(ctx.name), attrs: ctx.attrs, self_closing: false };
    let (d1, ctx_id) = dom::create_node(
        d0,
        NodeKind::Element {
            namespace: Some(ctx.ns),
            prefix: None,
            local_name: ctx.name,
            attributes: ctx.attrs,
            template_contents: None,
            form_owner: None,
        },
    );
    // 17. "Create a start tag token whose name is the local name of context
    // and whose attributes are the attributes of context." (Its use is the
    // annotation-xml test, kept in the element.)
    let ctx_el = Elem {
        id: ctx_id,
        ns: ctx.ns,
        tag: ctx_tok.tag,
        name: ctx.name,
        annotation_html: annotation_html(ctx.ns, ctx_tok),
    };
    // 10. The tokenizer state, switching on context (HTML elements).
    let st = if ctx.ns != Namespace::Html {
        None
    } else {
        match ctx_tok.tag {
            Tag::Title | Tag::Textarea => Some(TokenizerState::Rcdata),
            Tag::Style | Tag::Xmp | Tag::Iframe | Tag::Noembed | Tag::Noframes => Some(TokenizerState::Rawtext),
            Tag::Script => Some(TokenizerState::ScriptData),
            Tag::Noscript => if scripting {
                Some(TokenizerState::Rawtext)
            } else {
                None
            },
            Tag::Plaintext => Some(TokenizerState::Plaintext),
            _ => None,
        }
    };
    // 11. "Let root be the result of creating an element given document,
    // "html", the HTML namespace, …"
    let html = seq![0x68u32, 0x74, 0x6d, 0x6c];
    let (d2, root) = dom::create_node(
        d1,
        NodeKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: html,
            attributes: seq![],
            template_contents: None,
            form_owner: None,
        },
    );
    // 12. "Append root to document."
    let d3 = dom::append(d2, 0, root);
    // 14. "Let fragment be the result of creating a document fragment given
    // … target's node document." (The same arena; see [`super`].)
    let (d4, fragment) = dom::create_node(d3, NodeKind::DocumentFragment { host: None });
    // 9. "Create a new HTML parser whose … scripting mode is scriptingMode,
    // and fragment context element is context" (8.: Disabled when the
    // context document's scripting is disabled: the flag passed).
    let p0 = Parser {
        doc: d4,
        context: Some(ctx_el),
        // 13. "Set up the HTML parser's stack of open elements so that it
        // contains just the single element root."
        open: seq![Elem { id: root, ns: Namespace::Html, tag: Tag::Html, name: html, annotation_html: false }],
        // 15. "Set the parser's insertion target redirection map[root] to
        // (fragment, null)."
        redirect: Some((root, fragment)),
        // 16. "If context is a template element, then push "in template"
        // onto the stack of template insertion modes …"
        template_modes: if is_html(ctx_el, Tag::Template) {
            seq![Mode::InTemplate]
        } else {
            seq![]
        },
        // 20. "The encoding confidence is irrelevant."
        tentative: false,
        ..new_parser(seq![], scripting, false)
    };
    let p1 = Parser { doc: d4, ..p0 };
    // 18. "Reset the parser's insertion mode appropriately."
    let p2 = reset_insertion_mode(p1);
    // 19. "Set the HTML parser's form element pointer to the nearest node to
    // context that is a form element (… including the element itself …)":
    // the context has no ancestors here.
    let p3 = if is_html(ctx_el, Tag::Form) {
        Parser { form: Some(ctx_id), ..p2 }
    } else {
        p2
    };
    (p3, fragment, st)
}

/// §13.4 "HTML fragment parsing algorithm": the fragment's arena, the
/// fragment's id (step 23 returns it; its children are the result), and
/// the actions. Steps 20 and 21 run the parser over the tokenizer's tokens;
/// 22, "adopt fragment into target's node document", changes nothing in one
/// arena.
pub open spec fn parse_fragment<S>(env: EncFns, tf: TokFns<S>, s0: S, ctx: Context, scripting: bool, n: nat) -> (Document, NodeId, Seq<Action>) {
    let (p, fragment, st) = fragment_parser(ctx, scripting);
    let s1 = match st {
        Some(x) => (tf.set_state)(s0, x),
        None => s0,
    };
    let s2 = (tf.set_foreign)(s1, in_foreign_content(p));
    let (q, acts) = parse_steps(env, tf, s2, p, seq![], n);
    (q.doc, fragment, acts)
}

} // verus!
