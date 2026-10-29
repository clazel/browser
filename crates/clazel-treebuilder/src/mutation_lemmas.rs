//! Concrete instances of the proven theorems, used as the kill certificates
//! of `mutations.json` (`xtask/src/mutate.rs`). Each lemma states what a
//! theorem says about one small concrete parser and token; a certificate
//! evaluates the mutated spec there (`compute_only`) and shows that it
//! contradicts the lemma.
//!
//! - [`ml_kept`]: one rule application whose outcome reprocesses the token
//!   (or uses another mode's rules) without a decrease of the ranking of
//!   `theorem_dispatch_total`. [`ml_ranked`] is the per-mode lemmas
//!   (`termination::lemma_rules_edges`) at a parser satisfying `modes_ok`,
//!   so `ml_kept` is false at every such parser; the `ml_*_ranked` lemmas
//!   instantiate it at the scenarios the mutations break.
//! - [`ml_change_encoding_certain`], [`ml_stop_parsing_stops`] and
//!   [`ml_script_ready_running_only`]: the per-step lemmas of
//!   `theorem_actions_ordered` (`theorems::frame_modes`,
//!   `theorems::frame_base`) at a concrete parser.
//!
//! The parsers ([`ml_parser`]): a new document (no nodes are inserted, so
//! the element ids are placeholders), the given insertion mode, stack of
//! open elements and stack of template insertion modes, an empty list of
//! active formatting elements, the original insertion mode "in body", a
//! tentative confidence, running.
//!
//! No `by (compute_only)` here: the facts that a mutation changes come from
//! the theorems, and only the certificates evaluate the (mutated) spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Concrete parsers and tokens

/// Encoding functions that recognise nothing.
pub open spec fn ml_env() -> EncFns {
    EncFns { get_an_encoding: |l: Seq<u32>| None::<nat>, extract_from_meta: |c: Seq<u32>| None::<Seq<u32>> }
}

/// An HTML element with the tag `tag` (no name; the rules the scenarios
/// reach compare tags only).
pub open spec fn ml_elem(tag: Tag) -> Elem {
    Elem { id: 0, ns: Namespace::Html, tag, name: seq![], annotation_html: false }
}

/// A running parser in insertion mode `mode`, with stack `open` and
/// template insertion modes `tm` (see the module comment).
pub open spec fn ml_parser(mode: Mode, open: Seq<Elem>, tm: Seq<Mode>) -> Parser {
    Parser {
        doc: clazel_dom::spec::new_document(seq![]),
        mode,
        original_mode: Mode::InBody,
        template_modes: tm,
        open,
        formatting: seq![],
        head: None,
        form: None,
        context: None,
        scripting: false,
        frameset_ok: true,
        foster: false,
        pending_table_text: seq![],
        skip_lf: false,
        tokenizer: None,
        tentative: true,
        redirect: None,
        stopped: false,
        actions: seq![],
    }
}

/// The stack `html`, `body`.
pub open spec fn ml_open_body() -> Seq<Elem> {
    seq![ml_elem(Tag::Html), ml_elem(Tag::Body)]
}

/// The stack `html`, `table`.
pub open spec fn ml_open_table() -> Seq<Elem> {
    seq![ml_elem(Tag::Html), ml_elem(Tag::Table)]
}

/// The stack `html`, `template`, and one template insertion mode.
pub open spec fn ml_template_parser() -> Parser {
    ml_parser(Mode::InTemplate, seq![ml_elem(Tag::Html), ml_elem(Tag::Template)], seq![Mode::InTemplate])
}

/// The character token "x" (not whitespace: the "anything else" entries).
pub open spec fn ml_x() -> Tok {
    Tok::Char(0x78)
}

/// A start tag token for `tag`, without attributes.
pub open spec fn ml_start(tag: Tag) -> Tok {
    Tok::Start(TagTok { name: seq![], tag, attrs: seq![], self_closing: false })
}

/// An end tag token for `tag`.
pub open spec fn ml_end(tag: Tag) -> Tok {
    Tok::End(TagTok { name: seq![], tag, attrs: seq![], self_closing: false })
}

// ---------------------------------------------------------------------
// theorem_dispatch_total: every edge decreases the ranking

/// The outcome `o` of applying `r` to `p` and `t` reprocesses the token,
/// or uses another mode's rules, on a running parser, without the rank
/// decreasing (`termination::decreases_to`): what `edge_ok` rules out.
pub open spec fn ml_rank_kept(r: Rules, p: Parser, t: Tok, o: Outcome) -> bool {
    match o {
        Outcome::Done(_) => false,
        Outcome::Reprocess(q, t2) => !q.stopped && !crate::termination::decreases_to(r, p, t, Rules::Html(q.mode), q, t2),
        Outcome::Using(m, q, t2) => !q.stopped && !crate::termination::decreases_to(r, p, t, Rules::Html(m), q, t2),
    }
}

/// [`ml_rank_kept`] for the rules of insertion mode `m`.
pub open spec fn ml_kept(m: Mode, p: Parser, t: Tok) -> bool {
    ml_rank_kept(Rules::Html(m), p, t, apply_rules(ml_env(), Rules::Html(m), p, t))
}

/// `termination::lemma_rules_edges`: no edge keeps the rank.
pub proof fn ml_ranked(r: Rules, p: Parser, t: Tok)
    requires
        crate::termination::modes_ok(p),
        crate::termination::rules_ok(r, p),
    ensures
        !ml_rank_kept(r, p, t, apply_rules(ml_env(), r, p, t)),
{
    crate::termination::lemma_rules_edges(ml_env(), r, p, t);
}

/// [`ml_ranked`] at an [`ml_parser`] in its own insertion mode.
pub proof fn ml_ranked_at(m: Mode, open: Seq<Elem>, tm: Seq<Mode>, t: Tok)
    requires
        crate::termination::templates_in(open, open.len() as int) <= tm.len(),
        forall|i: int| 0 <= i < tm.len() ==> crate::termination::template_mode_ok(#[trigger] tm[i]),
        m == Mode::InTemplate ==> tm.len() > 0,
    ensures
        !ml_kept(m, ml_parser(m, open, tm), t),
{
    hide(apply_rules);
    ml_ranked(Rules::Html(m), ml_parser(m, open, tm), t);
}

/// "initial", a character: the rank decreases.
pub proof fn ml_initial_ranked()
    ensures
        !ml_kept(Mode::Initial, ml_parser(Mode::Initial, seq![], seq![]), ml_x()),
{
    hide(apply_rules);
    ml_ranked_at(Mode::Initial, seq![], seq![], ml_x());
}

/// "before html", a character.
pub proof fn ml_before_html_ranked()
    ensures
        !ml_kept(Mode::BeforeHtml, ml_parser(Mode::BeforeHtml, seq![], seq![]), ml_x()),
{
    hide(apply_rules);
    ml_ranked_at(Mode::BeforeHtml, seq![], seq![], ml_x());
}

/// "before head", a character.
pub proof fn ml_before_head_ranked()
    ensures
        !ml_kept(Mode::BeforeHead, ml_parser(Mode::BeforeHead, seq![ml_elem(Tag::Html)], seq![]), ml_x()),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 2);
    ml_ranked_at(Mode::BeforeHead, seq![ml_elem(Tag::Html)], seq![], ml_x());
}

/// "in head", a character.
pub proof fn ml_in_head_ranked()
    ensures
        !ml_kept(Mode::InHead, ml_parser(Mode::InHead, seq![ml_elem(Tag::Html), ml_elem(Tag::Head)], seq![]), ml_x()),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 3);
    ml_ranked_at(Mode::InHead, seq![ml_elem(Tag::Html), ml_elem(Tag::Head)], seq![], ml_x());
}

/// "in head noscript", a character.
pub proof fn ml_in_head_noscript_ranked()
    ensures
        !ml_kept(
            Mode::InHeadNoscript,
            ml_parser(Mode::InHeadNoscript, seq![ml_elem(Tag::Html), ml_elem(Tag::Head), ml_elem(Tag::Noscript)], seq![]),
            ml_x(),
        ),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 4);
    ml_ranked_at(Mode::InHeadNoscript, seq![ml_elem(Tag::Html), ml_elem(Tag::Head), ml_elem(Tag::Noscript)], seq![], ml_x());
}

/// "after head", a character.
pub proof fn ml_after_head_ranked()
    ensures
        !ml_kept(Mode::AfterHead, ml_parser(Mode::AfterHead, seq![ml_elem(Tag::Html)], seq![]), ml_x()),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 2);
    ml_ranked_at(Mode::AfterHead, seq![ml_elem(Tag::Html)], seq![], ml_x());
}

/// "in body", an `html` end tag.
pub proof fn ml_in_body_html_end_ranked()
    ensures
        !ml_kept(Mode::InBody, ml_parser(Mode::InBody, ml_open_body(), seq![]), ml_end(Tag::Html)),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 3);
    ml_ranked_at(Mode::InBody, ml_open_body(), seq![], ml_end(Tag::Html));
}

/// "in body", an `image` start tag.
pub proof fn ml_in_body_image_ranked()
    ensures
        !ml_kept(Mode::InBody, ml_parser(Mode::InBody, ml_open_body(), seq![]), ml_start(Tag::Image)),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 3);
    ml_ranked_at(Mode::InBody, ml_open_body(), seq![], ml_start(Tag::Image));
}

/// "text", end of file.
pub proof fn ml_text_eof_ranked()
    ensures
        !ml_kept(
            Mode::Text,
            ml_parser(Mode::Text, seq![ml_elem(Tag::Html), ml_elem(Tag::Body), ml_elem(Tag::Script)], seq![]),
            Tok::Eof,
        ),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 4);
    ml_ranked_at(Mode::Text, seq![ml_elem(Tag::Html), ml_elem(Tag::Body), ml_elem(Tag::Script)], seq![], Tok::Eof);
}

/// "in table", a `table` start tag.
pub proof fn ml_in_table_ranked()
    ensures
        !ml_kept(Mode::InTable, ml_parser(Mode::InTable, ml_open_table(), seq![]), ml_start(Tag::Table)),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 3);
    ml_ranked_at(Mode::InTable, ml_open_table(), seq![], ml_start(Tag::Table));
}

/// "in caption", a `table` end tag.
pub proof fn ml_in_caption_ranked()
    ensures
        !ml_kept(Mode::InCaption, ml_parser(Mode::InCaption, ml_open_table().push(ml_elem(Tag::Caption)), seq![]), ml_end(Tag::Table)),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 4);
    ml_ranked_at(Mode::InCaption, ml_open_table().push(ml_elem(Tag::Caption)), seq![], ml_end(Tag::Table));
}

/// "in column group", a character.
pub proof fn ml_in_column_group_ranked()
    ensures
        !ml_kept(Mode::InColumnGroup, ml_parser(Mode::InColumnGroup, ml_open_table().push(ml_elem(Tag::Colgroup)), seq![]), ml_x()),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 4);
    ml_ranked_at(Mode::InColumnGroup, ml_open_table().push(ml_elem(Tag::Colgroup)), seq![], ml_x());
}

/// "in table body", a `caption` start tag.
pub proof fn ml_in_table_body_ranked()
    ensures
        !ml_kept(Mode::InTableBody, ml_parser(Mode::InTableBody, ml_open_table().push(ml_elem(Tag::Tbody)), seq![]), ml_start(Tag::Caption)),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 4);
    ml_ranked_at(Mode::InTableBody, ml_open_table().push(ml_elem(Tag::Tbody)), seq![], ml_start(Tag::Caption));
}

/// "in row", a `table` end tag.
pub proof fn ml_in_row_ranked()
    ensures
        !ml_kept(
            Mode::InRow,
            ml_parser(Mode::InRow, ml_open_table().push(ml_elem(Tag::Tbody)).push(ml_elem(Tag::Tr)), seq![]),
            ml_end(Tag::Table),
        ),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 5);
    ml_ranked_at(Mode::InRow, ml_open_table().push(ml_elem(Tag::Tbody)).push(ml_elem(Tag::Tr)), seq![], ml_end(Tag::Table));
}

/// "in cell", a `td` start tag.
pub proof fn ml_in_cell_ranked()
    ensures
        !ml_kept(
            Mode::InCell,
            ml_parser(Mode::InCell, ml_open_table().push(ml_elem(Tag::Tbody)).push(ml_elem(Tag::Tr)).push(ml_elem(Tag::Td)), seq![]),
            ml_start(Tag::Td),
        ),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 6);
    ml_ranked_at(
        Mode::InCell,
        ml_open_table().push(ml_elem(Tag::Tbody)).push(ml_elem(Tag::Tr)).push(ml_elem(Tag::Td)),
        seq![],
        ml_start(Tag::Td),
    );
}

/// "in template", a start tag `tag`.
pub proof fn ml_in_template_ranked(tag: Tag)
    ensures
        !ml_kept(Mode::InTemplate, ml_template_parser(), ml_start(tag)),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 3);
    let tm = seq![Mode::InTemplate];
    assert(crate::termination::template_mode_ok(tm[0]));
    ml_ranked_at(Mode::InTemplate, seq![ml_elem(Tag::Html), ml_elem(Tag::Template)], tm, ml_start(tag));
}

/// "after body", a character.
pub proof fn ml_after_body_ranked()
    ensures
        !ml_kept(Mode::AfterBody, ml_parser(Mode::AfterBody, ml_open_body(), seq![]), ml_x()),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 3);
    ml_ranked_at(Mode::AfterBody, ml_open_body(), seq![], ml_x());
}

/// "after after body", a character.
pub proof fn ml_after_after_body_ranked()
    ensures
        !ml_kept(Mode::AfterAfterBody, ml_parser(Mode::AfterAfterBody, ml_open_body(), seq![]), ml_x()),
{
    hide(apply_rules);
    reveal_with_fuel(crate::termination::templates_in, 3);
    ml_ranked_at(Mode::AfterAfterBody, ml_open_body(), seq![], ml_x());
}

// ---------------------------------------------------------------------
// theorem_actions_ordered: the per-step lemmas

/// `theorems::frame_modes::lemma_change_the_encoding`: changing the
/// encoding (a new `ChangeEncoding` action) leaves the confidence certain.
pub proof fn ml_change_encoding_certain()
    ensures
        !change_the_encoding(ml_parser(Mode::InHead, seq![], seq![]), 0).tentative,
{
    let p = ml_parser(Mode::InHead, seq![], seq![]);
    let q = change_the_encoding(p, 0);
    crate::theorems::frame_modes::lemma_change_the_encoding(p, 0);
    assert(q.actions[0] is ChangeEncoding);
}

/// `theorems::frame_base::lemma_stop_parsing` (`grows`): stopping a running
/// parser adds `StopParsing`, and so leaves it stopped.
pub proof fn ml_stop_parsing_stops()
    ensures
        stop_parsing(ml_parser(Mode::InBody, ml_open_body(), seq![])).stopped,
{
    let p = ml_parser(Mode::InBody, ml_open_body(), seq![]);
    crate::theorems::frame_base::lemma_stop_parsing(p);
    assert(stop_parsing(p).actions.len() != p.actions.len() || stop_parsing(p).stopped);
}

/// A stopped parser in the "text" mode, with a `script` element current.
pub open spec fn ml_stopped_text() -> Parser {
    Parser {
        stopped: true,
        ..ml_parser(Mode::Text, seq![ml_elem(Tag::Html), ml_elem(Tag::Body), ml_elem(Tag::Script)], seq![])
    }
}

/// `theorems::frame_modes::lemma_text_script_end` (`step_ok`): a stopped
/// parser adds no action, so the `script` end tag readies no script.
pub proof fn ml_script_ready_running_only()
    ensures
        text_script_end(ml_stopped_text()).actions.len() == 0,
{
    crate::theorems::frame_modes::lemma_text_script_end(ml_stopped_text());
}

// ---------------------------------------------------------------------
// The W3C transcription (`independent`): its equivalence lemmas at
// concrete parsers, for the modes whose rules a mutation changes. The
// certificates of these kills evaluate the mutated spec at the parser
// below and contradict `independent::equivalence::lemma_<mode>` there (the
// W3C text says otherwise on that input, and the lemma's precondition
// holds).

/// A document whose node 1 is an `html` element, the Document's child
/// (inserting into an element, unlike into the Document, checks no
/// quantified condition, so `compute_only` evaluates it).
pub open spec fn ml_doc_html() -> clazel_dom::spec::Document {
    clazel_dom::spec::Document {
        nodes: seq![
            clazel_dom::spec::Node {
                kind: NodeKind::Document { mode: DocumentMode::NoQuirks, url: seq![], base_url: seq![] },
                parent: None,
                children: seq![1],
                wrapper: None,
            },
            clazel_dom::spec::Node {
                kind: NodeKind::Element {
                    namespace: Some(Namespace::Html),
                    prefix: None,
                    local_name: seq![0x68u32, 0x74, 0x6d, 0x6c],
                    attributes: seq![],
                    template_contents: None,
                    form_owner: None,
                },
                parent: Some(0),
                children: seq![],
                wrapper: None,
            },
        ],
    }
}

/// [`ml_parser`] over [`ml_doc_html`].
pub open spec fn ml_parser_html(mode: Mode, open: Seq<Elem>) -> Parser {
    Parser { doc: ml_doc_html(), ..ml_parser(mode, open, seq![]) }
}

/// An HTML element named `name`, tagged by its name (the lemmas for the
/// table modes compare "the same tag name" and need tagged records); its
/// node is [`ml_doc_html`]'s element.
pub open spec fn ml_named(name: Seq<u32>) -> Elem {
    Elem { id: 1, ns: Namespace::Html, tag: tag_of(name), name, annotation_html: false }
}

/// A start tag token named `name`, tagged by its name, without attributes.
pub open spec fn ml_named_start(name: Seq<u32>) -> Tok {
    Tok::Start(TagTok { name, tag: tag_of(name), attrs: seq![], self_closing: false })
}

/// An end tag token named `name`, tagged by its name.
pub open spec fn ml_named_end(name: Seq<u32>) -> Tok {
    Tok::End(TagTok { name, tag: tag_of(name), attrs: seq![], self_closing: false })
}

/// The stack `html`, `table`, `tbody`, `tr` of named elements, with
/// `rest` after it.
pub open spec fn ml_named_row(rest: Seq<Elem>) -> Seq<Elem> {
    seq![
        ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c]),
        ml_named(seq![0x74u32, 0x61, 0x62, 0x6c, 0x65]),
        ml_named(seq![0x74u32, 0x62, 0x6f, 0x64, 0x79]),
        ml_named(seq![0x74u32, 0x72]),
    ] + rest
}

// ---------------------------------------------------------------------
// The certificates' facts: for each mode, the W3C transcription evaluated
// at the parser and token (`compute_only`), carried over to the spec by
// the equivalence lemma. A mutant that computes otherwise contradicts it.

/// What `independent::equivalence::lemma_before_html` gives at the certificate
/// input of `before-html-html-wrong-mode`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_before_html()
    ensures
        crate::independent::w3c_mode_before_html(ml_env(), ml_parser(Mode::BeforeHtml, seq![], seq![]), ml_start(Tag::Html)) == mode_before_html(ml_env(), ml_parser(Mode::BeforeHtml, seq![], seq![]), ml_start(Tag::Html)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_before_html(ml_env(), ml_parser(Mode::BeforeHtml, seq![], seq![]), ml_start(Tag::Html));
}

pub proof fn ml_w3c_before_html()
    ensures
        !(mode_before_html(ml_env(), ml_parser(Mode::BeforeHtml, seq![], seq![]), ml_start(Tag::Html))->Done_0.mode == Mode::BeforeHtml),
{
    assert(!(crate::independent::w3c_mode_before_html(ml_env(), ml_parser(Mode::BeforeHtml, seq![], seq![]), ml_start(Tag::Html))->Done_0.mode == Mode::BeforeHtml)) by (compute_only);
    ml_w3c_eq_before_html();
}

/// What `independent::equivalence::lemma_before_head` gives at the certificate
/// input of `before-head-pointer-not-set`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_before_head()
    ensures
        crate::independent::w3c_mode_before_head(ml_env(), ml_parser_html(Mode::BeforeHead, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c])]), ml_start(Tag::Head)) == mode_before_head(ml_env(), ml_parser_html(Mode::BeforeHead, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c])]), ml_start(Tag::Head)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_before_head(ml_env(), ml_parser_html(Mode::BeforeHead, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c])]), ml_start(Tag::Head));
}

pub proof fn ml_w3c_before_head()
    ensures
        !(mode_before_head(ml_env(), ml_parser_html(Mode::BeforeHead, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c])]), ml_start(Tag::Head))->Done_0.head is None),
{
    assert(!(crate::independent::w3c_mode_before_head(ml_env(), ml_parser_html(Mode::BeforeHead, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c])]), ml_start(Tag::Head))->Done_0.head is None)) by (compute_only);
    ml_w3c_eq_before_head();
}

/// What `independent::equivalence::lemma_in_head` gives at the certificate
/// input of `in-head-head-not-popped`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_in_head()
    ensures
        crate::independent::w3c_mode_in_head(ml_env(), ml_parser(Mode::InHead, seq![ml_elem(Tag::Html), ml_elem(Tag::Head)], seq![]), ml_x()) == mode_in_head(ml_env(), ml_parser(Mode::InHead, seq![ml_elem(Tag::Html), ml_elem(Tag::Head)], seq![]), ml_x()),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_in_head(ml_env(), ml_parser(Mode::InHead, seq![ml_elem(Tag::Html), ml_elem(Tag::Head)], seq![]), ml_x());
}

pub proof fn ml_w3c_in_head()
    ensures
        !(mode_in_head(ml_env(), ml_parser(Mode::InHead, seq![ml_elem(Tag::Html), ml_elem(Tag::Head)], seq![]), ml_x())->Reprocess_0.open.len() == 2),
{
    assert(!(crate::independent::w3c_mode_in_head(ml_env(), ml_parser(Mode::InHead, seq![ml_elem(Tag::Html), ml_elem(Tag::Head)], seq![]), ml_x())->Reprocess_0.open.len() == 2)) by (compute_only);
    ml_w3c_eq_in_head();
}

/// What `independent::equivalence::lemma_in_head_noscript` gives at the certificate
/// input of `in-head-noscript-end-not-popped`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_in_head_noscript()
    ensures
        crate::independent::w3c_mode_in_head_noscript(ml_env(), ml_parser(Mode::InHeadNoscript, seq![ml_elem(Tag::Html), ml_elem(Tag::Head), ml_elem(Tag::Noscript)], seq![]), ml_end(Tag::Noscript)) == mode_in_head_noscript(ml_env(), ml_parser(Mode::InHeadNoscript, seq![ml_elem(Tag::Html), ml_elem(Tag::Head), ml_elem(Tag::Noscript)], seq![]), ml_end(Tag::Noscript)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_in_head_noscript(ml_env(), ml_parser(Mode::InHeadNoscript, seq![ml_elem(Tag::Html), ml_elem(Tag::Head), ml_elem(Tag::Noscript)], seq![]), ml_end(Tag::Noscript));
}

pub proof fn ml_w3c_in_head_noscript()
    ensures
        !(mode_in_head_noscript(ml_env(), ml_parser(Mode::InHeadNoscript, seq![ml_elem(Tag::Html), ml_elem(Tag::Head), ml_elem(Tag::Noscript)], seq![]), ml_end(Tag::Noscript))->Done_0.open.len() == 3),
{
    assert(!(crate::independent::w3c_mode_in_head_noscript(ml_env(), ml_parser(Mode::InHeadNoscript, seq![ml_elem(Tag::Html), ml_elem(Tag::Head), ml_elem(Tag::Noscript)], seq![]), ml_end(Tag::Noscript))->Done_0.open.len() == 3)) by (compute_only);
    ml_w3c_eq_in_head_noscript();
}

/// What `independent::equivalence::lemma_after_head` gives at the certificate
/// input of `after-head-body-frameset-ok`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_after_head()
    ensures
        crate::independent::w3c_mode_after_head(ml_env(), ml_parser(Mode::AfterHead, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Body)) == mode_after_head(ml_env(), ml_parser(Mode::AfterHead, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Body)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_after_head(ml_env(), ml_parser(Mode::AfterHead, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Body));
}

pub proof fn ml_w3c_after_head()
    ensures
        !(mode_after_head(ml_env(), ml_parser(Mode::AfterHead, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Body))->Done_0.frameset_ok),
{
    assert(!(crate::independent::w3c_mode_after_head(ml_env(), ml_parser(Mode::AfterHead, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Body))->Done_0.frameset_ok)) by (compute_only);
    ml_w3c_eq_after_head();
}

/// What `independent::equivalence::lemma_text` gives at the certificate
/// input of `text-end-tag-not-popped`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_text()
    ensures
        crate::independent::w3c_mode_text(ml_env(), ml_parser(Mode::Text, seq![ml_elem(Tag::Html), ml_elem(Tag::Body), ml_elem(Tag::Style)], seq![]), ml_end(Tag::Style)) == mode_text(ml_env(), ml_parser(Mode::Text, seq![ml_elem(Tag::Html), ml_elem(Tag::Body), ml_elem(Tag::Style)], seq![]), ml_end(Tag::Style)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_text(ml_env(), ml_parser(Mode::Text, seq![ml_elem(Tag::Html), ml_elem(Tag::Body), ml_elem(Tag::Style)], seq![]), ml_end(Tag::Style));
}

pub proof fn ml_w3c_text()
    ensures
        !(mode_text(ml_env(), ml_parser(Mode::Text, seq![ml_elem(Tag::Html), ml_elem(Tag::Body), ml_elem(Tag::Style)], seq![]), ml_end(Tag::Style))->Done_0.open.len() == 3),
{
    assert(!(crate::independent::w3c_mode_text(ml_env(), ml_parser(Mode::Text, seq![ml_elem(Tag::Html), ml_elem(Tag::Body), ml_elem(Tag::Style)], seq![]), ml_end(Tag::Style))->Done_0.open.len() == 3)) by (compute_only);
    ml_w3c_eq_text();
}

/// What `independent::equivalence::lemma_in_caption` gives at the certificate
/// input of `in-caption-markers-kept`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_in_caption()
    ensures
        crate::independent::w3c_mode_in_caption(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser(Mode::InCaption, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Caption)], seq![]) }, ml_end(Tag::Caption)) == mode_in_caption(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser(Mode::InCaption, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Caption)], seq![]) }, ml_end(Tag::Caption)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_in_caption(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser(Mode::InCaption, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Caption)], seq![]) }, ml_end(Tag::Caption));
}

pub proof fn ml_w3c_in_caption()
    ensures
        !(mode_in_caption(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser(Mode::InCaption, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Caption)], seq![]) }, ml_end(Tag::Caption))->Done_0.formatting.len() == 1),
{
    assert(!(crate::independent::w3c_mode_in_caption(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser(Mode::InCaption, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Caption)], seq![]) }, ml_end(Tag::Caption))->Done_0.formatting.len() == 1)) by (compute_only);
    ml_w3c_eq_in_caption();
}

/// What `independent::equivalence::lemma_in_column_group` gives at the certificate
/// input of `in-column-group-end-not-popped`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_in_column_group()
    ensures
        crate::independent::w3c_mode_in_column_group(ml_env(), ml_parser(Mode::InColumnGroup, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Colgroup)], seq![]), ml_end(Tag::Colgroup)) == mode_in_column_group(ml_env(), ml_parser(Mode::InColumnGroup, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Colgroup)], seq![]), ml_end(Tag::Colgroup)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_in_column_group(ml_env(), ml_parser(Mode::InColumnGroup, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Colgroup)], seq![]), ml_end(Tag::Colgroup));
}

pub proof fn ml_w3c_in_column_group()
    ensures
        !(mode_in_column_group(ml_env(), ml_parser(Mode::InColumnGroup, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Colgroup)], seq![]), ml_end(Tag::Colgroup))->Done_0.open.len() == 3),
{
    assert(!(crate::independent::w3c_mode_in_column_group(ml_env(), ml_parser(Mode::InColumnGroup, seq![ml_elem(Tag::Html), ml_elem(Tag::Table), ml_elem(Tag::Colgroup)], seq![]), ml_end(Tag::Colgroup))->Done_0.open.len() == 3)) by (compute_only);
    ml_w3c_eq_in_column_group();
}

/// What `independent::equivalence::lemma_in_table_body` gives at the certificate
/// input of `in-table-body-tr-wrong-mode`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_in_table_body()
    ensures
        crate::independent::w3c_mode_in_table_body(ml_env(), ml_parser_html(Mode::InTableBody, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c]), ml_named(seq![0x74u32, 0x61, 0x62, 0x6c, 0x65]), ml_named(seq![0x74u32, 0x62, 0x6f, 0x64, 0x79])]), ml_named_start(seq![0x74u32, 0x72])) == mode_in_table_body(ml_env(), ml_parser_html(Mode::InTableBody, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c]), ml_named(seq![0x74u32, 0x61, 0x62, 0x6c, 0x65]), ml_named(seq![0x74u32, 0x62, 0x6f, 0x64, 0x79])]), ml_named_start(seq![0x74u32, 0x72])),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_in_table_body(ml_env(), ml_parser_html(Mode::InTableBody, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c]), ml_named(seq![0x74u32, 0x61, 0x62, 0x6c, 0x65]), ml_named(seq![0x74u32, 0x62, 0x6f, 0x64, 0x79])]), ml_named_start(seq![0x74u32, 0x72]));
}

pub proof fn ml_w3c_in_table_body()
    ensures
        !(mode_in_table_body(ml_env(), ml_parser_html(Mode::InTableBody, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c]), ml_named(seq![0x74u32, 0x61, 0x62, 0x6c, 0x65]), ml_named(seq![0x74u32, 0x62, 0x6f, 0x64, 0x79])]), ml_named_start(seq![0x74u32, 0x72]))->Done_0.mode == Mode::InTableBody),
{
    assert(!(crate::independent::w3c_mode_in_table_body(ml_env(), ml_parser_html(Mode::InTableBody, seq![ml_named(seq![0x68u32, 0x74, 0x6d, 0x6c]), ml_named(seq![0x74u32, 0x61, 0x62, 0x6c, 0x65]), ml_named(seq![0x74u32, 0x62, 0x6f, 0x64, 0x79])]), ml_named_start(seq![0x74u32, 0x72]))->Done_0.mode == Mode::InTableBody)) by (compute_only);
    ml_w3c_eq_in_table_body();
}

/// What `independent::equivalence::lemma_in_row` gives at the certificate
/// input of `in-row-cell-no-marker`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_in_row()
    ensures
        crate::independent::w3c_mode_in_row(ml_env(), ml_parser_html(Mode::InRow, ml_named_row(seq![])), ml_named_start(seq![0x74u32, 0x64])) == mode_in_row(ml_env(), ml_parser_html(Mode::InRow, ml_named_row(seq![])), ml_named_start(seq![0x74u32, 0x64])),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_in_row(ml_env(), ml_parser_html(Mode::InRow, ml_named_row(seq![])), ml_named_start(seq![0x74u32, 0x64]));
}

pub proof fn ml_w3c_in_row()
    ensures
        !(mode_in_row(ml_env(), ml_parser_html(Mode::InRow, ml_named_row(seq![])), ml_named_start(seq![0x74u32, 0x64]))->Done_0.formatting.len() == 0),
{
    assert(!(crate::independent::w3c_mode_in_row(ml_env(), ml_parser_html(Mode::InRow, ml_named_row(seq![])), ml_named_start(seq![0x74u32, 0x64]))->Done_0.formatting.len() == 0)) by (compute_only);
    ml_w3c_eq_in_row();
}

/// What `independent::equivalence::lemma_in_cell` gives at the certificate
/// input of `in-cell-end-not-popped`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_in_cell()
    ensures
        crate::independent::w3c_mode_in_cell(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser_html(Mode::InCell, ml_named_row(seq![ml_named(seq![0x74u32, 0x64])])) }, ml_named_end(seq![0x74u32, 0x64])) == mode_in_cell(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser_html(Mode::InCell, ml_named_row(seq![ml_named(seq![0x74u32, 0x64])])) }, ml_named_end(seq![0x74u32, 0x64])),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_in_cell(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser_html(Mode::InCell, ml_named_row(seq![ml_named(seq![0x74u32, 0x64])])) }, ml_named_end(seq![0x74u32, 0x64]));
}

pub proof fn ml_w3c_in_cell()
    ensures
        !(mode_in_cell(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser_html(Mode::InCell, ml_named_row(seq![ml_named(seq![0x74u32, 0x64])])) }, ml_named_end(seq![0x74u32, 0x64]))->Done_0.open.len() == 5),
{
    assert(!(crate::independent::w3c_mode_in_cell(ml_env(), Parser { formatting: seq![Fmt::Marker], ..ml_parser_html(Mode::InCell, ml_named_row(seq![ml_named(seq![0x74u32, 0x64])])) }, ml_named_end(seq![0x74u32, 0x64]))->Done_0.open.len() == 5)) by (compute_only);
    ml_w3c_eq_in_cell();
}

/// What `independent::equivalence::lemma_in_template` gives at the certificate
/// input of `in-template-col-wrong-mode`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_in_template()
    ensures
        crate::independent::w3c_mode_in_template(ml_env(), ml_template_parser(), ml_start(Tag::Col)) == mode_in_template(ml_env(), ml_template_parser(), ml_start(Tag::Col)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_in_template(ml_env(), ml_template_parser(), ml_start(Tag::Col));
}

pub proof fn ml_w3c_in_template()
    ensures
        !(mode_in_template(ml_env(), ml_template_parser(), ml_start(Tag::Col))->Reprocess_0.mode == Mode::InTable),
{
    assert(!(crate::independent::w3c_mode_in_template(ml_env(), ml_template_parser(), ml_start(Tag::Col))->Reprocess_0.mode == Mode::InTable)) by (compute_only);
    ml_w3c_eq_in_template();
}

/// What `independent::equivalence::lemma_after_body` gives at the certificate
/// input of `after-body-html-end-wrong-mode`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_after_body()
    ensures
        crate::independent::w3c_mode_after_body(ml_env(), ml_parser(Mode::AfterBody, ml_open_body(), seq![]), ml_end(Tag::Html)) == mode_after_body(ml_env(), ml_parser(Mode::AfterBody, ml_open_body(), seq![]), ml_end(Tag::Html)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_after_body(ml_env(), ml_parser(Mode::AfterBody, ml_open_body(), seq![]), ml_end(Tag::Html));
}

pub proof fn ml_w3c_after_body()
    ensures
        !(mode_after_body(ml_env(), ml_parser(Mode::AfterBody, ml_open_body(), seq![]), ml_end(Tag::Html))->Done_0.mode == Mode::AfterBody),
{
    assert(!(crate::independent::w3c_mode_after_body(ml_env(), ml_parser(Mode::AfterBody, ml_open_body(), seq![]), ml_end(Tag::Html))->Done_0.mode == Mode::AfterBody)) by (compute_only);
    ml_w3c_eq_after_body();
}

/// What `independent::equivalence::lemma_in_frameset` gives at the certificate
/// input of `in-frameset-root-popped`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_in_frameset()
    ensures
        crate::independent::w3c_mode_in_frameset(ml_env(), Parser { context: Some(ml_elem(Tag::Html)), ..ml_parser(Mode::InFrameset, seq![ml_elem(Tag::Html)], seq![]) }, ml_end(Tag::Frameset)) == mode_in_frameset(ml_env(), Parser { context: Some(ml_elem(Tag::Html)), ..ml_parser(Mode::InFrameset, seq![ml_elem(Tag::Html)], seq![]) }, ml_end(Tag::Frameset)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_in_frameset(ml_env(), Parser { context: Some(ml_elem(Tag::Html)), ..ml_parser(Mode::InFrameset, seq![ml_elem(Tag::Html)], seq![]) }, ml_end(Tag::Frameset));
}

pub proof fn ml_w3c_in_frameset()
    ensures
        !(mode_in_frameset(ml_env(), Parser { context: Some(ml_elem(Tag::Html)), ..ml_parser(Mode::InFrameset, seq![ml_elem(Tag::Html)], seq![]) }, ml_end(Tag::Frameset))->Done_0.open.len() == 0),
{
    assert(!(crate::independent::w3c_mode_in_frameset(ml_env(), Parser { context: Some(ml_elem(Tag::Html)), ..ml_parser(Mode::InFrameset, seq![ml_elem(Tag::Html)], seq![]) }, ml_end(Tag::Frameset))->Done_0.open.len() == 0)) by (compute_only);
    ml_w3c_eq_in_frameset();
}

/// What `independent::equivalence::lemma_after_frameset` gives at the certificate
/// input of `after-frameset-html-end-wrong-mode`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_after_frameset()
    ensures
        crate::independent::w3c_mode_after_frameset(ml_env(), ml_parser(Mode::AfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_end(Tag::Html)) == mode_after_frameset(ml_env(), ml_parser(Mode::AfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_end(Tag::Html)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_after_frameset(ml_env(), ml_parser(Mode::AfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_end(Tag::Html));
}

pub proof fn ml_w3c_after_frameset()
    ensures
        !(mode_after_frameset(ml_env(), ml_parser(Mode::AfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_end(Tag::Html))->Done_0.mode == Mode::AfterFrameset),
{
    assert(!(crate::independent::w3c_mode_after_frameset(ml_env(), ml_parser(Mode::AfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_end(Tag::Html))->Done_0.mode == Mode::AfterFrameset)) by (compute_only);
    ml_w3c_eq_after_frameset();
}

/// What `independent::equivalence::lemma_after_after_frameset` gives at the certificate
/// input of `after-after-frameset-noframes-dropped`.
/// The equivalence lemma at that input (`tag_of` hidden: the records and
/// tokens are tagged by construction).
proof fn ml_w3c_eq_after_after_frameset()
    ensures
        crate::independent::w3c_mode_after_after_frameset(ml_env(), ml_parser(Mode::AfterAfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Noframes)) == mode_after_after_frameset(ml_env(), ml_parser(Mode::AfterAfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Noframes)),
{
    hide(tag_of);
    crate::independent::equivalence::lemma_after_after_frameset(ml_env(), ml_parser(Mode::AfterAfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Noframes));
}

pub proof fn ml_w3c_after_after_frameset()
    ensures
        !(mode_after_after_frameset(ml_env(), ml_parser(Mode::AfterAfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Noframes)) is Done),
{
    assert(!(crate::independent::w3c_mode_after_after_frameset(ml_env(), ml_parser(Mode::AfterAfterFrameset, seq![ml_elem(Tag::Html)], seq![]), ml_start(Tag::Noframes)) is Done)) by (compute_only);
    ml_w3c_eq_after_after_frameset();
}

// ---------------------------------------------------------------------
// The W3C transcription of "in body" and "in table"
// (`independent::equivalence_body`) at concrete parsers.

/// "html"
pub open spec fn ml_name_html() -> Seq<u32> {
    seq![0x68u32, 0x74, 0x6d, 0x6c]
}

/// "body"
pub open spec fn ml_name_body() -> Seq<u32> {
    seq![0x62u32, 0x6f, 0x64, 0x79]
}

/// "table"
pub open spec fn ml_name_table() -> Seq<u32> {
    seq![0x74u32, 0x61, 0x62, 0x6c, 0x65]
}

/// "b"
pub open spec fn ml_name_b() -> Seq<u32> {
    seq![0x62u32]
}

/// "div"
pub open spec fn ml_name_div() -> Seq<u32> {
    seq![0x64u32, 0x69, 0x76]
}

/// "track"
pub open spec fn ml_name_track() -> Seq<u32> {
    seq![0x74u32, 0x72, 0x61, 0x63, 0x6b]
}

/// An HTML element record named `name` for node `id`, tagged by its name.
pub open spec fn ml_el(name: Seq<u32>, id: NodeId) -> Elem {
    Elem { id, ns: Namespace::Html, tag: tag_of(name), name, annotation_html: false }
}

/// An HTML element node named `name`, with no attributes, the given
/// parent and children.
pub open spec fn ml_el_node(name: Seq<u32>, parent: NodeId, children: Seq<NodeId>) -> clazel_dom::spec::Node {
    clazel_dom::spec::Node {
        kind: NodeKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: name,
            attributes: seq![],
            template_contents: None,
            form_owner: None,
        },
        parent: Some(parent),
        children,
        wrapper: None,
    }
}

/// The Document node, with the given children.
pub open spec fn ml_document_node(children: Seq<NodeId>) -> clazel_dom::spec::Node {
    clazel_dom::spec::Node {
        kind: NodeKind::Document { mode: DocumentMode::NoQuirks, url: seq![], base_url: seq![] },
        parent: None,
        children,
        wrapper: None,
    }
}

/// A document `html` (1) > `body` (2) > `table` (3).
pub open spec fn ml_doc_table() -> clazel_dom::spec::Document {
    clazel_dom::spec::Document {
        nodes: seq![
            ml_document_node(seq![1]),
            ml_el_node(ml_name_html(), 0, seq![2]),
            ml_el_node(ml_name_body(), 1, seq![3]),
            ml_el_node(ml_name_table(), 2, seq![]),
        ],
    }
}

/// A parser in insertion mode `mode` over [`ml_doc_table`], with the stack
/// `html`, `body`, `table`.
pub open spec fn ml_table_parser(mode: Mode) -> Parser {
    Parser {
        doc: ml_doc_table(),
        ..ml_parser(mode, seq![ml_el(ml_name_html(), 1), ml_el(ml_name_body(), 2), ml_el(ml_name_table(), 3)], seq![])
    }
}

/// The stack entry `j` of the adoption agency scenario: `html` (node 1),
/// `body` (2), `b` (3), then seven `div` elements (4 to 10).
pub open spec fn ml_aa_elem(j: int) -> Elem {
    if j == 0 {
        ml_el(ml_name_html(), 1)
    } else if j == 1 {
        ml_el(ml_name_body(), 2)
    } else if j == 2 {
        ml_el(ml_name_b(), 3)
    } else {
        ml_el(ml_name_div(), (j + 1) as NodeId)
    }
}

/// The node `i` of the adoption agency scenario: the Document, then
/// `html` > `body` > `b` > `div` > … > `div`, each the only child of the
/// one before.
pub open spec fn ml_aa_node(i: int) -> clazel_dom::spec::Node {
    if i == 0 {
        ml_document_node(seq![1])
    } else {
        let name = if i == 1 {
            ml_name_html()
        } else if i == 2 {
            ml_name_body()
        } else if i == 3 {
            ml_name_b()
        } else {
            ml_name_div()
        };
        let children = if i < 10 {
            seq![(i + 1) as NodeId]
        } else {
            seq![]
        };
        ml_el_node(name, (i - 1) as NodeId, children)
    }
}

/// The token of a `b` start tag, without attributes.
pub open spec fn ml_b_token() -> TagTok {
    TagTok { name: ml_name_b(), tag: tag_of(ml_name_b()), attrs: seq![], self_closing: false }
}

/// "In body" with the stack `html`, `body`, `b` and seven `div` elements,
/// each inside the one before, and `b` in the list of active formatting
/// elements: a `b` end tag makes the adoption agency algorithm's outer loop
/// run seven times with a furthest block, and an eighth without.
pub open spec fn ml_aa_parser() -> Parser {
    Parser {
        doc: clazel_dom::spec::Document { nodes: Seq::new(11, |i: int| ml_aa_node(i)) },
        formatting: seq![Fmt::Entry { elem: ml_el(ml_name_b(), 3), token: ml_b_token() }],
        ..ml_parser(Mode::InBody, Seq::new(10, |j: int| ml_aa_elem(j)), seq![])
    }
}

/// "In body" over [`ml_doc_html`] with the stack `html`.
pub open spec fn ml_body_parser() -> Parser {
    ml_parser_html(Mode::InBody, seq![ml_named(ml_name_html())])
}

/// The stack of [`ml_table_parser`] satisfies `equivalence::place_stable`
/// and its records are tagged.
proof fn ml_table_stable(mode: Mode)
    ensures
        crate::independent::equivalence::place_stable(ml_table_parser(mode)),
        crate::independent::equivalence_body::aa_wf(ml_table_parser(mode)),
{
    let p = ml_table_parser(mode);
    assert(tag_of(ml_name_html()) == Tag::Html) by (compute_only);
    assert(p.open[0] == ml_el(ml_name_html(), 1));
    assert(p.open[1] == ml_el(ml_name_body(), 2));
    assert(p.open[2] == ml_el(ml_name_table(), 3));
    assert(p.doc.nodes[1] == ml_el_node(ml_name_html(), 0, seq![2]));
    assert(p.doc.nodes[2] == ml_el_node(ml_name_body(), 1, seq![3]));
    assert(p.doc.nodes[3] == ml_el_node(ml_name_table(), 2, seq![]));
    assert forall|i: int| 0 <= i < p.open.len() implies clazel_dom::spec::valid(p.doc, (#[trigger] p.open[i]).id) && (
    p.doc.nodes[p.open[i].id as int].parent is None || clazel_dom::spec::valid(
        p.doc,
        p.doc.nodes[p.open[i].id as int].parent->Some_0,
    )) by {
        if i == 0 {
        } else if i == 1 {
        } else {
            assert(i == 2);
        }
    }
    assert forall|j: int| 0 <= j < p.open.len() implies (#[trigger] p.open[j]).id < p.doc.nodes.len() && elem_tagged(p.open[j]) by {
        if j == 0 {
        } else if j == 1 {
        } else {
            assert(j == 2);
        }
    }
}

/// The adoption agency scenario's parser has the facts the "in body"
/// lemma uses (`equivalence_body::aa_wf`).
proof fn ml_aa_wf()
    ensures
        crate::independent::equivalence_body::aa_wf(ml_aa_parser()),
{
    let p = ml_aa_parser();
    assert forall|j: int| 0 <= j < p.open.len() implies (#[trigger] p.open[j]).id < p.doc.nodes.len() && elem_tagged(p.open[j]) by {
        assert(p.open[j] == ml_aa_elem(j));
    }
    let f = p.formatting;
    assert forall|j: int| 0 <= j < f.len() implies crate::independent::equivalence_body::fmt_entry_ok(
        #[trigger] f[j],
        p.doc.nodes.len(),
    ) by {
        assert(j == 0);
    }
    assert forall|j: int, k: int|
        #![trigger f[j], f[k]]
        0 <= j < f.len() && 0 <= k < f.len() && f[j] is Entry && f[k] is Entry && f[j]->Entry_elem.id
            == f[k]->Entry_elem.id implies f[j]->Entry_elem.tag == f[k]->Entry_elem.tag by {
        assert(j == 0 && k == 0);
    }
}

/// The "in body" lemma's precondition at the adoption agency scenario, for
/// a `b` end tag: the texts agree there, and so do the algorithm's
/// insertions (both evaluated).
proof fn ml_aa_agrees()
    ensures
        crate::independent::equivalence_body::in_body_texts_agree(ml_aa_parser(), ml_named_end(ml_name_b())),
        crate::independent::equivalence_body::in_body_aa_agrees(ml_aa_parser(), ml_named_end(ml_name_b())),
        tag_of(ml_name_b()) == Tag::B,
{
    assert(crate::independent::equivalence_body::in_body_texts_agree(ml_aa_parser(), ml_named_end(ml_name_b()))) by (compute_only);
    assert(crate::independent::equivalence_body::in_body_aa_agrees(ml_aa_parser(), ml_named_end(ml_name_b()))) by (compute_only);
    assert(tag_of(ml_name_b()) == Tag::B) by (compute_only);
}

/// What `independent::equivalence_body::lemma_in_body` gives at the
/// certificate input of `adoption-outer-loop-seven`.
proof fn ml_w3c_eq_in_body_aa()
    ensures
        crate::independent::w3c_mode_in_body(ml_env(), ml_aa_parser(), ml_named_end(ml_name_b())) == mode_in_body(
            ml_env(),
            ml_aa_parser(),
            ml_named_end(ml_name_b()),
        ),
{
    hide(tag_of);
    ml_aa_wf();
    ml_aa_agrees();
    crate::independent::equivalence_body::lemma_in_body(ml_env(), ml_aa_parser(), ml_named_end(ml_name_b()));
}

pub proof fn ml_w3c_in_body_aa()
    ensures
        !(mode_in_body(ml_env(), ml_aa_parser(), ml_named_end(ml_name_b()))->Done_0.open.len() == 10),
{
    assert(!(crate::independent::w3c_mode_in_body(ml_env(), ml_aa_parser(), ml_named_end(ml_name_b()))->Done_0.open.len() == 10))
        by (compute_only);
    ml_w3c_eq_in_body_aa();
}

/// The "in body" lemma's precondition at [`ml_body_parser`] for a `track`
/// start tag.
proof fn ml_track_agrees()
    ensures
        crate::independent::equivalence_body::in_body_texts_agree(ml_body_parser(), ml_named_start(ml_name_track())),
        crate::independent::equivalence_body::in_body_aa_agrees(ml_body_parser(), ml_named_start(ml_name_track())),
        tag_of(ml_name_track()) == Tag::Track,
{
    assert(tag_of(ml_name_track()) == Tag::Track) by (compute_only);
    assert(crate::independent::equivalence_body::in_body_texts_agree(ml_body_parser(), ml_named_start(ml_name_track())))
        by (compute_only);
    assert(crate::independent::equivalence_body::in_body_aa_agrees(ml_body_parser(), ml_named_start(ml_name_track())))
        by (compute_only);
}

/// What `independent::equivalence_body::lemma_in_body` gives at the
/// certificate input of `in-body-track-dropped`.
proof fn ml_w3c_eq_in_body_track()
    ensures
        crate::independent::w3c_mode_in_body(ml_env(), ml_body_parser(), ml_named_start(ml_name_track())) == mode_in_body(
            ml_env(),
            ml_body_parser(),
            ml_named_start(ml_name_track()),
        ),
{
    hide(tag_of);
    ml_track_agrees();
    let p = ml_body_parser();
    assert(p.open[0] == ml_named(ml_name_html()));
    assert forall|j: int| 0 <= j < p.open.len() implies (#[trigger] p.open[j]).id < p.doc.nodes.len() && elem_tagged(p.open[j]) by {
        assert(j == 0);
    }
    crate::independent::equivalence_body::lemma_in_body(ml_env(), ml_body_parser(), ml_named_start(ml_name_track()));
}

pub proof fn ml_w3c_in_body_track()
    ensures
        !(mode_in_body(ml_env(), ml_body_parser(), ml_named_start(ml_name_track()))->Done_0.open.len() == 2),
{
    assert(!(crate::independent::w3c_mode_in_body(ml_env(), ml_body_parser(), ml_named_start(ml_name_track()))->Done_0.open.len()
        == 2)) by (compute_only);
    ml_w3c_eq_in_body_track();
}

/// The "in table" lemma's precondition at [`ml_table_parser`] for a `div`
/// start tag.
proof fn ml_div_in_table_agrees()
    ensures
        crate::independent::equivalence_body::in_table_texts_agree(ml_table_parser(Mode::InTable), ml_named_start(ml_name_div())),
        crate::independent::equivalence_body::in_body_texts_agree(
            Parser { foster: true, ..ml_table_parser(Mode::InTable) },
            ml_named_start(ml_name_div()),
        ),
        crate::independent::equivalence_body::in_body_aa_agrees(
            Parser { foster: true, ..ml_table_parser(Mode::InTable) },
            ml_named_start(ml_name_div()),
        ),
        tag_of(ml_name_div()) == Tag::Div,
{
    assert(tag_of(ml_name_div()) == Tag::Div) by (compute_only);
    assert(crate::independent::equivalence_body::in_table_texts_agree(ml_table_parser(Mode::InTable), ml_named_start(ml_name_div())))
        by (compute_only);
    assert(crate::independent::equivalence_body::in_body_texts_agree(
        Parser { foster: true, ..ml_table_parser(Mode::InTable) },
        ml_named_start(ml_name_div()),
    )) by (compute_only);
    assert(crate::independent::equivalence_body::in_body_aa_agrees(
        Parser { foster: true, ..ml_table_parser(Mode::InTable) },
        ml_named_start(ml_name_div()),
    )) by (compute_only);
}

/// What `independent::equivalence_body::lemma_in_table` gives at the
/// certificate input of `in-table-foster-parenting-disabled`.
proof fn ml_w3c_eq_in_table()
    ensures
        crate::independent::w3c_mode_in_table(ml_env(), ml_table_parser(Mode::InTable), ml_named_start(ml_name_div()))
            == mode_in_table(ml_env(), ml_table_parser(Mode::InTable), ml_named_start(ml_name_div())),
{
    hide(crate::independent::w3c_mode_in_table);
    hide(mode_in_table);
    ml_div_in_table_ok();
    crate::independent::equivalence_body::lemma_in_table(ml_env(), ml_table_parser(Mode::InTable), ml_named_start(ml_name_div()));
}

/// The "in table" lemma's precondition at the certificate input of
/// `in-table-foster-parenting-disabled`.
proof fn ml_div_in_table_ok()
    ensures
        crate::independent::equivalence_body::in_table_texts_agree(ml_table_parser(Mode::InTable), ml_named_start(ml_name_div())),
        crate::independent::equivalence::place_stable(ml_table_parser(Mode::InTable)),
        crate::independent::equivalence_body::in_table_body_ok(ml_table_parser(Mode::InTable), ml_named_start(ml_name_div())),
{
    hide(tag_of);
    ml_table_stable(Mode::InTable);
    ml_div_in_table_agrees();
}

pub proof fn ml_w3c_in_table()
    ensures
        !(mode_in_table(ml_env(), ml_table_parser(Mode::InTable), ml_named_start(ml_name_div()))->Done_0.doc.nodes[3].children.len()
            == 1),
{
    assert(!(crate::independent::w3c_mode_in_table(
        ml_env(),
        ml_table_parser(Mode::InTable),
        ml_named_start(ml_name_div()),
    )->Done_0.doc.nodes[3].children.len() == 1)) by (compute_only);
    ml_w3c_eq_in_table();
}

// ---------------------------------------------------------------------
// Foreign content and its tables (`independent::equivalence_foreign`)

/// An SVG `svg` element, node 1.
pub open spec fn ml_svg_elem() -> Elem {
    Elem { id: 1, ns: Namespace::Svg, tag: Tag::Svg, name: seq![0x73u32, 0x76, 0x67], annotation_html: false }
}

/// A parser "in body" whose stack is `html`, `svg`: the `svg` element is
/// the current node, so the dispatcher sends tags to the rules for foreign
/// content.
pub open spec fn ml_svg_parser() -> Parser {
    ml_parser(Mode::InBody, seq![ml_elem(Tag::Html), ml_svg_elem()], seq![])
}

/// "altglyph"
pub open spec fn ml_name_altglyph() -> Seq<u32> {
    seq![0x61u32, 0x6c, 0x74, 0x67, 0x6c, 0x79, 0x70, 0x68]
}

/// "xlink:href"
pub open spec fn ml_name_xlink_href() -> Seq<u32> {
    seq![0x78u32, 0x6c, 0x69, 0x6e, 0x6b, 0x3a, 0x68, 0x72, 0x65, 0x66]
}

/// "b" is a `b` start tag's name.
proof fn ml_tag_b()
    ensures
        tag_of(ml_name_b()) == Tag::B,
{
    assert(tag_of(ml_name_b()) == Tag::B) by (compute_only);
}

/// What `independent::equivalence_foreign::lemma_foreign_content` gives at
/// the certificate input of `foreign-breakout-not-popped`: a `b` start tag
/// with the stack `html`, `svg` (outside the fragment case, and a breakout
/// tag in both texts).
proof fn ml_w3c_eq_foreign()
    ensures
        crate::independent::w3c_foreign_content(ml_env(), ml_svg_parser(), ml_named_start(ml_name_b())) == foreign_content(
            ml_env(),
            ml_svg_parser(),
            ml_named_start(ml_name_b()),
        ),
{
    hide(tag_of);
    hide(crate::independent::w3c_foreign_content);
    hide(foreign_content);
    ml_tag_b();
    let p = ml_svg_parser();
    assert(crate::independent::equivalence_foreign::open_distinct(p.open));
    assert(crate::independent::equivalence_body::attrs_plain(seq![]));
    crate::independent::equivalence_foreign::lemma_foreign_content(ml_env(), p, ml_named_start(ml_name_b()));
}

pub proof fn ml_w3c_foreign_breakout()
    ensures
        !(foreign_content(ml_env(), ml_svg_parser(), ml_named_start(ml_name_b()))->Reprocess_0.open.len() == 2),
{
    assert(!(crate::independent::w3c_foreign_content(ml_env(), ml_svg_parser(), ml_named_start(ml_name_b()))->Reprocess_0.open.len()
        == 2)) by (compute_only);
    ml_w3c_eq_foreign();
}

/// `independent::equivalence_foreign::lemma_svg_element_name` at
/// "altglyph" (the certificate input of `svg-tag-name-row-dropped`).
pub proof fn ml_w3c_svg_tag_name()
    ensures
        !(svg_tag_name(ml_name_altglyph()) == ml_name_altglyph()),
{
    assert(!(crate::independent::w3c_svg_element_name(ml_name_altglyph()) == ml_name_altglyph())) by (compute_only);
    crate::independent::equivalence_foreign::lemma_svg_element_name(ml_name_altglyph());
}

/// `independent::equivalence_foreign::lemma_foreign_attribute` at
/// "xlink:href" (the certificate input of `foreign-attribute-row-dropped`).
pub proof fn ml_w3c_foreign_attribute()
    ensures
        !(foreign_attribute(ml_name_xlink_href()) is None),
{
    assert(!(crate::independent::w3c_foreign_attribute(ml_name_xlink_href()) is None)) by (compute_only);
    crate::independent::equivalence_foreign::lemma_foreign_attribute(ml_name_xlink_href());
}

} // verus!
