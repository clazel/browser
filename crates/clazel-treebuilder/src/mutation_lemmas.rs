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

} // verus!
