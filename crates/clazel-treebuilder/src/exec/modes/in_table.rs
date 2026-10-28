//! HTML §13.2.6.4.9 the "in table" insertion mode ([`mode_in_table`]),
//! "clear the stack back to a table context" and the "anything else" entry
//! ([`in_table_anything_else`]), over [`ParserBuf`].
//!
//! Also the facts the table modes share: popping while the predicate fails
//! on the `html` element keeps the stack rooted, and inserting an element,
//! reconstructing the active formatting elements and inserting characters
//! keep it rooted or stop the parser; changing the flags and the insertion
//! mode keeps [`parser_inv`].

use super::in_body::{in_body_char_exec, mode_in_body_exec};
use super::in_head::mode_in_head_exec;
#[allow(unused_imports)]
use super::spec::*;
use crate::exec::formatting::*;
#[cfg(verus_only)]
use crate::exec::frame::*;
use crate::exec::insert::*;
use crate::exec::names::*;
use crate::exec::stack::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The invariant and the root of the stack

/// The parser has stopped or its stack is rooted at an `html` element.
pub open spec fn rooted_or_stopped(p: Parser) -> bool {
    p.stopped || stack_rooted(p)
}

/// [`parser_inv`] gives `modes_ok`.
pub proof fn lemma_inv_modes(p: Parser)
    requires
        parser_inv(p),
    ensures
        crate::termination::modes_ok(p),
{
}

/// Changing the foster parenting and frameset-ok flags keeps
/// [`parser_inv`].
pub proof fn lemma_inv_flags(p: Parser, q: Parser)
    requires
        parser_inv(p),
        q == (Parser { foster: q.foster, frameset_ok: q.frameset_ok, ..p }),
    ensures
        parser_inv(q),
{
    lemma_inv_iff(p);
    lemma_inv_iff(q);
}

/// Setting an insertion mode other than "text", "in table text" and "in
/// template" keeps [`parser_inv`].
pub proof fn lemma_set_mode(p: Parser, m: Mode)
    requires
        parser_inv(p),
        m != Mode::Text && m != Mode::InTableText && m != Mode::InTemplate,
    ensures
        parser_inv(Parser { mode: m, ..p }),
{
    lemma_inv_iff(p);
    lemma_inv_iff(Parser { mode: m, ..p });
}

/// Popping while `f` holds, with `f` false on the `html` element at the
/// bottom, keeps the stack rooted and changes nothing but the stack.
pub proof fn lemma_pop_while_rooted(p: Parser, f: spec_fn(Elem) -> bool)
    requires
        stack_rooted(p),
        !f(p.open[0]),
    ensures
        stack_rooted(pop_while(p, f)),
        pop_while(p, f) == (Parser { open: pop_while(p, f).open, ..p }),
    decreases p.open.len(),
{
    if f(current_node(p)) {
        assert(p.open.len() > 1);
        let q = pop(p);
        assert(q.open[0] == p.open[0]);
        lemma_pop_while_rooted(q, f);
    }
}

/// "Insert an HTML element" stops the parser or pushes the element.
pub proof fn lemma_insert_html_pushes(p: Parser, tt: TagTok)
    ensures
        p.stopped ==> insert_html_element(p, tt).0.stopped,
        insert_html_element(p, tt).0.stopped || insert_html_element(p, tt).0.open == p.open.push(
            insert_html_element(p, tt).1,
        ),
{
    let parent = appropriate_place(p, None).parent;
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, parent);
    let p2 = insert_element_at(p1, e.id, None);
    crate::termination::helpers_ranking::lemma_insert_element_at(p1, e.id, None);
    assert(p1.stopped || p1.open == p.open);
    assert(p2.stopped == p1.stopped);
}

/// "Insert an HTML element" keeps the stack rooted or stops the parser.
pub proof fn lemma_insert_html_rooted(p: Parser, tt: TagTok)
    requires
        rooted_or_stopped(p),
    ensures
        rooted_or_stopped(insert_html_element(p, tt).0),
{
    lemma_insert_html_pushes(p, tt);
    let q = insert_html_element(p, tt).0;
    if !q.stopped {
        assert(q.open[0] == p.open[0]);
    }
}

/// Steps 7 to 10 of "reconstruct the active formatting elements" keep the
/// stack rooted or stop the parser.
pub proof fn lemma_reconstruct_create_rooted(p: Parser, i: int)
    requires
        rooted_or_stopped(p),
    ensures
        rooted_or_stopped(reconstruct_create(p, i)),
    decreases p.formatting.len() - i,
{
    if !(i < 0 || i >= p.formatting.len() || p.stopped || !(p.formatting[i] is Entry)) {
        let token = p.formatting[i]->Entry_token;
        lemma_insert_html_rooted(p, token);
        let (p1, e) = insert_html_element(p, token);
        let p2 = if p1.stopped {
            p1
        } else {
            Parser { formatting: p1.formatting.update(i, Fmt::Entry { elem: e, token }), ..p1 }
        };
        if i + 1 < p2.formatting.len() && p2.formatting.len() == p.formatting.len() {
            lemma_reconstruct_create_rooted(p2, i + 1);
        }
    }
}

/// "Reconstruct the active formatting elements" keeps the stack rooted or
/// stops the parser.
pub proof fn lemma_reconstruct_rooted(p: Parser)
    requires
        rooted_or_stopped(p),
    ensures
        rooted_or_stopped(reconstruct_formatting(p)),
{
    let n = p.formatting.len();
    if n > 0 && !(p.formatting[n - 1] is Marker || fmt_on_stack(p, p.formatting[n - 1])) {
        lemma_reconstruct_create_rooted(p, reconstruct_rewind(p, n - 1));
    }
}

/// "Insert a character" keeps the stack or stops the parser.
pub proof fn lemma_insert_characters_rooted(p: Parser, data: Seq<u32>)
    ensures
        insert_characters(p, data).stopped || insert_characters(p, data).open == p.open,
{
    let k = NodeKind::Text { data };
    let loc = adjusted_location(p, None);
    let (p1, n) = create(p, k);
    assert(p1.stopped || p1.open == p.open);
    let p2 = dom_insert(p1, n, loc.parent, loc.child);
    assert(p2.stopped || p2.open == p1.open);
}

/// "Insert a character" keeps the stack rooted or stops the parser.
pub proof fn lemma_insert_char_rooted(p: Parser, c: u32)
    requires
        rooted_or_stopped(p),
    ensures
        rooted_or_stopped(insert_char(p, c)),
{
    lemma_insert_characters_rooted(p, seq![c]);
}

// ---------------------------------------------------------------------
// Tokens

/// "colgroup".
fn name_colgroup_exec() -> (r: Vec<u32>)
    ensures
        r@ == name_colgroup(),
{
    let s: &[u32] = &[0x63u32, 0x6f, 0x6c, 0x67, 0x72, 0x6f, 0x75, 0x70];
    proof {
        assert(s@ =~= name_colgroup());
    }
    copy_str(s)
}

/// "tbody".
fn name_tbody_exec() -> (r: Vec<u32>)
    ensures
        r@ == name_tbody(),
{
    let s: &[u32] = &[0x74u32, 0x62, 0x6f, 0x64, 0x79];
    proof {
        assert(s@ =~= name_tbody());
    }
    copy_str(s)
}

/// [`start_tag_named`]: a start tag token with no attributes.
pub fn start_tag_named_exec(name: Vec<u32>) -> (r: ExecTagTok)
    ensures
        r@ == start_tag_named(name@),
        tok_tagged(r@),
{
    let tag = tag_of_exec(name.as_slice());
    let r = ExecTagTok { name, tag, attrs: Vec::new(), self_closing: false };
    proof {
        assert(clazel_dom::exec::attrs_view(r.attrs@) =~= Seq::<Attr>::empty());
    }
    r
}

/// [`is_ascii_whitespace`].
pub fn is_ascii_whitespace_exec(c: u32) -> (r: bool)
    ensures
        r == is_ascii_whitespace(c),
{
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

/// [`in_table_input_is_hidden`].
pub fn in_table_input_is_hidden_exec(tt: &ExecTagTok) -> (r: bool)
    ensures
        r == in_table_input_is_hidden(tt@),
{
    let type_name: &[u32] = &[0x74u32, 0x79, 0x70, 0x65];
    let hidden: &[u32] = &[0x68u32, 0x69, 0x64, 0x64, 0x65, 0x6e];
    proof {
        assert(type_name@ =~= seq![0x74u32, 0x79, 0x70, 0x65]);
        assert(hidden@ =~= seq![0x68u32, 0x69, 0x64, 0x64, 0x65, 0x6e]);
    }
    match attr_value_exec(tt.attrs.as_slice(), type_name) {
        Some(v) => ascii_ci_eq_exec(v.as_slice(), hidden),
        None => false,
    }
}

// ---------------------------------------------------------------------
// Helpers

/// "clear the stack back to a table context"
/// ([`clear_stack_back_to_table_context`]).
pub fn clear_stack_back_to_table_context_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == clear_stack_back_to_table_context(old(p)@),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        final(p)@ == (Parser { open: final(p)@.open, ..old(p)@ }),
{
    let ghost f = |e: Elem| !(is_html(e, Tag::Table) || is_html(e, Tag::Template) || is_html(e, Tag::Html));
    proof {
        lemma_pop_while_rooted(old(p)@, f);
    }
    pop_while_exec(p, &ElemPred::NotTableContext, Ghost(f));
}

/// "Insert an HTML element for the token" and pop it ([`insert_and_pop`]):
/// the "in table" `input` case and the "in column group" `col` case.
pub fn table_insert_and_pop_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == insert_and_pop(old(p)@, tt@),
        parser_inv(final(p)@),
{
    hide(insert_html_element);
    hide(pop);
    let _ = insert_html_element_exec(p, tt);
    if !p.stopped {
        pop_exec(p);
    }
}

/// "Clear the stack back to a table context", insert a marker if `marker`,
/// "insert an HTML element for" `tt` and switch the insertion mode to `m`
/// ("in table" cases 5 to 9).
fn table_insert_exec(p: &mut ParserBuf, tt: &ExecTagTok, marker: bool, m: Mode)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
        m != Mode::Text && m != Mode::InTableText && m != Mode::InTemplate,
    ensures
        final(p)@ == (Parser {
            mode: m,
            ..insert_html_element(
                if marker {
                    push_marker(clear_stack_back_to_table_context(old(p)@))
                } else {
                    clear_stack_back_to_table_context(old(p)@)
                },
                tt@,
            ).0
        }),
        parser_inv(final(p)@),
{
    hide(insert_html_element);
    hide(clear_stack_back_to_table_context);
    hide(parser_inv);
    clear_stack_back_to_table_context_exec(p);
    if marker {
        push_marker_exec(p);
    }
    let _ = insert_html_element_exec(p, tt);
    proof {
        lemma_set_mode(p@, m);
    }
    p.mode = m;
}

/// The "in table" "anything else" entry for a character token: the "in
/// body" rules' character cases with foster parenting enabled.
pub proof fn lemma_in_table_anything_else_char(env: EncFns, p: Parser, c: u32)
    ensures
        in_table_anything_else(env, p, Tok::Char(c)) == Outcome::Done(
            Parser { foster: false, ..in_body_char(Parser { foster: true, ..p }, c) },
        ),
{
    hide(in_body_char);
    hide(mode_in_head);
}

/// The modes are fields that "insert a character" leaves alone.
pub open spec fn modes_kept(p: Parser, q: Parser) -> bool {
    &&& q.mode == p.mode
    &&& q.original_mode == p.original_mode
    &&& q.template_modes == p.template_modes
    &&& q.pending_table_text == p.pending_table_text
}

/// "Insert a character" keeps the modes.
proof fn lemma_insert_char_modes(p: Parser, c: u32)
    ensures
        modes_kept(p, insert_char(p, c)),
{
    let data = seq![c];
    let k = NodeKind::Text { data };
    let loc = adjusted_location(p, None);
    let (p1, n) = create(p, k);
    assert(modes_kept(p, p1));
    let p2 = dom_insert(p1, n, loc.parent, loc.child);
    assert(modes_kept(p1, p2));
}

/// The "in body" rules' character cases keep the stack rooted (or stop the
/// parser) and keep the modes.
proof fn lemma_in_body_char_kept(p: Parser, c: u32)
    requires
        parser_inv(p),
        rooted_or_stopped(p),
    ensures
        rooted_or_stopped(in_body_char(p, c)),
        modes_kept(p, in_body_char(p, c)),
{
    hide(parser_inv);
    if c != 0 {
        lemma_reconstruct_rooted(p);
        lemma_inv_modes(p);
        crate::termination::helpers_ranking::lemma_reconstruct_formatting(p);
        let r = reconstruct_formatting(p);
        lemma_insert_char_rooted(r, c);
        lemma_insert_char_modes(r, c);
    }
}

/// [`in_table_anything_else`] for a character token (cases 1 to 3 of the
/// "in body" insertion mode, with foster parenting enabled, then
/// disabled): see [`lemma_in_table_anything_else_char`].
pub fn in_table_char_exec(p: &mut ParserBuf, c: u32)
    requires
        parser_inv(old(p)@),
        rooted_or_stopped(old(p)@),
    ensures
        final(p)@ == (Parser { foster: false, ..in_body_char(Parser { foster: true, ..old(p)@ }, c) }),
        parser_inv(final(p)@),
        rooted_or_stopped(final(p)@),
        final(p)@.mode == old(p)@.mode,
        final(p)@.original_mode == old(p)@.original_mode,
        final(p)@.template_modes == old(p)@.template_modes,
        final(p)@.pending_table_text == old(p)@.pending_table_text,
{
    hide(parser_inv);
    hide(in_body_char);
    let ghost p0 = p@;
    p.foster = true;
    proof {
        lemma_inv_flags(p0, p@);
        lemma_in_body_char_kept(p@, c);
    }
    in_body_char_exec(p, c);
    let ghost p2 = p@;
    p.foster = false;
    proof {
        lemma_inv_flags(p2, p@);
    }
}

/// The "in body" outcome with foster parenting disabled
/// ([`outcome_without_foster`]), in place.
fn foster_off_exec(p: &mut ParserBuf, o: ExecOutcome) -> (r: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(r, final(p)@) == outcome_without_foster(outcome_view(o, old(p)@)),
        parser_inv(final(p)@),
{
    let ghost q = p@;
    p.foster = false;
    proof {
        lemma_inv_flags(q, p@);
    }
    o
}

/// The "in table" "anything else" entry ([`in_table_anything_else`]):
/// enable foster parenting, process the token using the "in body" rules
/// (and the "in head" rules they send it to), disable foster parenting.
pub fn in_table_anything_else_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        rooted_or_stopped(old(p)@),
        old(p)@.mode != Mode::Text,
        old(p)@.mode != Mode::InTableText,
        t@ is Start ==> tok_tagged(t@->Start_0),
        t@ is End ==> tok_tagged(t@->End_0),
    ensures
        outcome_view(o, final(p)@) == in_table_anything_else(env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(tag_of);
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(in_body_char);
    hide(in_body_eof);
    hide(mode_in_head);
    hide(parser_inv);
    hide(insert_comment);
    hide(insert_pi);
    hide(outcome_without_foster);
    let ghost p0 = p@;
    let ghost t0 = t@;
    if let ExecTok::Char(c) = t {
        proof {
            lemma_in_table_anything_else_char(env.enc(), p0, c);
        }
        in_table_char_exec(p, c);
        return ExecOutcome::Done;
    }
    p.foster = true;
    proof {
        lemma_inv_flags(p0, p@);
    }
    let ghost pf = p@;
    let o = mode_in_body_exec(env, p, t);
    proof {
        match t0 {
            Tok::Start(tt) => crate::termination::helpers_in_body::lemma_in_body_start_tag_outcome(pf, t0, tt),
            Tok::End(tt) => crate::termination::helpers_in_body::lemma_in_body_end_tag_outcome(pf, t0, tt),
            Tok::Eof => crate::termination::helpers_in_body::lemma_in_body_eof_outcome(pf, t0),
            _ => {},
        }
    }
    match o {
        ExecOutcome::Using(Mode::InHead, t2) => {
            proof {
                assert(p@ == pf);
                assert(t2@ == t0);
            }
            let o2 = mode_in_head_exec(env, p, t2);
            foster_off_exec(p, o2)
        },
        _ => foster_off_exec(p, o),
    }
}

// ---------------------------------------------------------------------
// The mode

/// §13.2.6.4.9 the "in table" insertion mode ([`mode_in_table`]).
pub fn mode_in_table_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        crate::termination::rules_ok(Rules::Html(Mode::InTable), old(p)@),
        t@ is Start ==> tok_tagged(t@->Start_0),
        t@ is End ==> tok_tagged(t@->End_0),
    ensures
        outcome_view(o, final(p)@) == mode_in_table(env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(in_table_anything_else);
    hide(insert_comment);
    hide(insert_pi);
    match t {
        ExecTok::Char(c) => in_table_char_case_exec(env, p, c),
        ExecTok::Comment(data) => {
            // 2.
            insert_comment_exec(p, data, None);
            ExecOutcome::Done
        },
        ExecTok::Pi(target, data) => {
            // 3.
            insert_pi_exec(p, target, data, None);
            ExecOutcome::Done
        },
        ExecTok::Doctype { .. } => {
            // 4.
            ExecOutcome::Done
        },
        ExecTok::Start(tt) => in_table_start_exec(env, p, tt),
        ExecTok::End(tt) => in_table_end_exec(env, p, tt),
        ExecTok::Eof => {
            // 16.
            ExecOutcome::Using(Mode::InBody, ExecTok::Eof)
        },
    }
}

/// [`mode_in_table`] for a character token: case 1, or case 17.
fn in_table_char_case_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, c: u32) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        crate::termination::rules_ok(Rules::Html(Mode::InTable), old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_in_table(env.enc(), old(p)@, Tok::Char(c)),
        parser_inv(final(p)@),
{
    hide(in_table_anything_else);
    let cur = current_node_exec(p);
    let tableish = is_html_ns(cur) && matches!(
        cur.tag,
        Tag::Table | Tag::Tbody | Tag::Template | Tag::Tfoot | Tag::Thead | Tag::Tr
    );
    if tableish {
        // 1.
        let ghost p0 = p@;
        p.pending_table_text = Vec::new();
        p.original_mode = copy_mode(&p.mode);
        p.mode = Mode::InTableText;
        proof {
            assert(p@.pending_table_text =~= Seq::<u32>::empty());
            lemma_inv_iff(p0);
            lemma_inv_iff(p@);
        }
        ExecOutcome::Reprocess(ExecTok::Char(c))
    } else {
        // 17.
        in_table_anything_else_exec(env, p, ExecTok::Char(c))
    }
}

/// [`mode_in_table`] for a start tag token.
#[verifier::spinoff_prover]
fn in_table_start_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        crate::termination::rules_ok(Rules::Html(Mode::InTable), old(p)@),
        tok_tagged(tt@),
    ensures
        outcome_view(o, final(p)@) == mode_in_table(env.enc(), old(p)@, Tok::Start(tt@)),
        parser_inv(final(p)@),
{
    hide(in_table_anything_else);
    hide(insert_html_element);
    hide(pop_until_popped);
    hide(reset_insertion_mode);
    hide(push_marker);
    hide(pop);
    hide(has_in_scope);
    hide(in_table_input_is_hidden);
    hide(parsing_template_contents);
    hide(clear_stack_back_to_table_context);
    hide(parser_inv);
    match tt.tag {
        Tag::Caption => {
            // 5.
            table_insert_exec(p, &tt, true, Mode::InCaption);
            ExecOutcome::Done
        },
        Tag::Colgroup => {
            // 6.
            table_insert_exec(p, &tt, false, Mode::InColumnGroup);
            ExecOutcome::Done
        },
        Tag::Col => {
            // 7.
            let colgroup = start_tag_named_exec(name_colgroup_exec());
            proof {
                crate::termination::helpers_ranking::lemma_not_template(name_colgroup());
            }
            table_insert_exec(p, &colgroup, false, Mode::InColumnGroup);
            ExecOutcome::Reprocess(ExecTok::Start(tt))
        },
        Tag::Tbody | Tag::Tfoot | Tag::Thead => {
            // 8.
            table_insert_exec(p, &tt, false, Mode::InTableBody);
            ExecOutcome::Done
        },
        Tag::Td | Tag::Th | Tag::Tr => {
            // 9.
            let tbody = start_tag_named_exec(name_tbody_exec());
            proof {
                crate::termination::helpers_ranking::lemma_not_template(name_tbody());
            }
            table_insert_exec(p, &tbody, false, Mode::InTableBody);
            ExecOutcome::Reprocess(ExecTok::Start(tt))
        },
        Tag::Table => {
            // 10.
            if !has_in_scope_exec(p, Tag::Table, &Scope::Table) {
                ExecOutcome::Done
            } else {
                pop_until_popped_exec(p, Tag::Table);
                reset_insertion_mode_exec(p);
                ExecOutcome::Reprocess(ExecTok::Start(tt))
            }
        },
        Tag::Style | Tag::Script | Tag::Template => {
            // 13.
            ExecOutcome::Using(Mode::InHead, ExecTok::Start(tt))
        },
        Tag::Input => {
            if in_table_input_is_hidden_exec(&tt) {
                // 14.
                table_insert_and_pop_exec(p, &tt);
                ExecOutcome::Done
            } else {
                // 14. (fallthrough to 17.)
                in_table_anything_else_exec(env, p, ExecTok::Start(tt))
            }
        },
        Tag::Form => {
            // 15.
            in_table_form_exec(p, &tt);
            ExecOutcome::Done
        },
        _ => {
            // 17.
            in_table_anything_else_exec(env, p, ExecTok::Start(tt))
        },
    }
}

/// "In table" case 15, a `form` start tag.
fn in_table_form_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::Form,
    ensures
        final(p)@ == (if old(p)@.form is Some && !parsing_template_contents(old(p)@) {
            old(p)@
        } else {
            let (p1, e) = insert_html_element(old(p)@, tt@);
            let p2 = if !parsing_template_contents(p1) && !p1.stopped {
                Parser { form: Some(e.id), ..p1 }
            } else {
                p1
            };
            if p2.stopped {
                p2
            } else {
                pop(p2)
            }
        }),
        parser_inv(final(p)@),
{
    hide(insert_html_element);
    hide(pop);
    hide(parsing_template_contents);
    if p.form.is_some() && !parsing_template_contents_exec(p) {
        return ;
    }
    let e = insert_html_element_exec(p, tt);
    if !parsing_template_contents_exec(p) && !p.stopped {
        proof {
            lemma_inv_iff(p@);
            assert(p@.open[p@.open.len() - 1] == e@);
            assert(elem_ok(p@.doc, p@.open[p@.open.len() - 1]));
        }
        let ghost q = p@;
        p.form = Some(e.id);
        proof {
            lemma_inv_iff(q);
            lemma_inv_iff(p@);
        }
    }
    if !p.stopped {
        pop_exec(p);
    }
}

/// [`mode_in_table`] for an end tag token.
#[verifier::spinoff_prover]
fn in_table_end_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        crate::termination::rules_ok(Rules::Html(Mode::InTable), old(p)@),
        tok_tagged(tt@),
    ensures
        outcome_view(o, final(p)@) == mode_in_table(env.enc(), old(p)@, Tok::End(tt@)),
        parser_inv(final(p)@),
{
    hide(in_table_anything_else);
    hide(pop_until_popped);
    hide(reset_insertion_mode);
    hide(has_in_scope);
    match tt.tag {
        Tag::Table => {
            // 11.
            if has_in_scope_exec(p, Tag::Table, &Scope::Table) {
                pop_until_popped_exec(p, Tag::Table);
                reset_insertion_mode_exec(p);
            }
            ExecOutcome::Done
        },
        Tag::Body | Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Html | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th
        | Tag::Thead | Tag::Tr => {
            // 12.
            ExecOutcome::Done
        },
        Tag::Template => {
            // 13.
            ExecOutcome::Using(Mode::InHead, ExecTok::End(tt))
        },
        _ => {
            // 17.
            in_table_anything_else_exec(env, p, ExecTok::End(tt))
        },
    }
}

} // verus!
