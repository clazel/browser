//! HTML §13.2.6.4.16 the "in template" insertion mode ([`mode_in_template`])
//! over [`ParserBuf`].

#[cfg(verus_only)]
use super::in_table::lemma_set_mode;
#[allow(unused_imports)]
use super::spec::*;
use crate::exec::formatting::*;
#[cfg(verus_only)]
use crate::exec::frame::*;
use crate::exec::insert::*;
use crate::exec::stack::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Reset the insertion mode appropriately" does not read the insertion
/// mode.
proof fn lemma_reset_from_mode(p: Parser, q: Parser, i: int)
    requires
        q == (Parser { mode: q.mode, ..p }),
    ensures
        reset_from(q, i) == reset_from(p, i),
    decreases i,
{
    if i > 0 {
        lemma_reset_from_mode(p, q, i - 1);
    }
}

/// Cases 3 to 7 ([`in_template_switch`]): replace the current template
/// insertion mode by `m`, switch to `m`, reprocess the token.
fn in_template_switch_exec(p: &mut ParserBuf, t: ExecTok, m: Mode) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.template_modes.len() > 0,
        m == Mode::InTable || m == Mode::InColumnGroup || m == Mode::InTableBody || m == Mode::InRow || m == Mode::InBody,
    ensures
        outcome_view(o, final(p)@) == in_template_switch(old(p)@, t@, m),
        parser_inv(final(p)@),
{
    let ghost p0 = p@;
    let ghost mm = m;
    let _ = p.template_modes.pop();
    p.template_modes.push(copy_mode(&m));
    p.mode = m;
    proof {
        lemma_inv_iff(p0);
        lemma_inv_iff(p@);
        assert(p@.template_modes == p0.template_modes.drop_last().push(mm));
        assert forall|i: int| 0 <= i < p@.template_modes.len() implies crate::termination::template_mode_ok(
            #[trigger] p@.template_modes[i],
        ) by {
            if i < p0.template_modes.len() - 1 {
                assert(p@.template_modes[i] == p0.template_modes[i]);
            }
        }
        assert(crate::termination::template_count(p@) == crate::termination::template_count(p0));
    }
    ExecOutcome::Reprocess(t)
}

/// Popping to a `template` element and clearing the list to the last
/// marker pops at least one `template` element and keeps the stack of
/// template insertion modes and the context.
proof fn lemma_eof_pops_template(p: Parser)
    requires
        open_has_html(p, Tag::Template),
    ensures
        ({
            let p2 = clear_to_last_marker(pop_until_popped(p, Tag::Template));
            &&& crate::termination::template_count(p2) + 1 <= crate::termination::template_count(p)
            &&& p2.template_modes == p.template_modes
        }),
{
    let j = crate::termination::helpers_ranking::lemma_open_has_html(p, Tag::Template);
    crate::termination::helpers_ranking::lemma_pop_until_template(p, j);
    crate::termination::helpers_tables::lemma_pop_until_popped(p, Tag::Template);
    let p1 = pop_until_popped(p, Tag::Template);
    crate::termination::helpers_tables::lemma_clear_to_last_marker(p1);
    crate::termination::helpers_ranking::lemma_template_count(p);
    crate::termination::helpers_ranking::lemma_template_count(p1);
    crate::termination::helpers_ranking::lemma_template_count(clear_to_last_marker(p1));
}

/// Popping the current template insertion mode of a parser in "in body"
/// with fewer `template` elements than template insertion modes keeps
/// [`parser_inv`].
proof fn lemma_drop_template_mode(p: Parser)
    requires
        parser_inv(p),
        p.mode == Mode::InBody,
        p.template_modes.len() > 0,
        crate::termination::template_count(p) + 1 <= p.template_modes.len(),
    ensures
        parser_inv(Parser { template_modes: p.template_modes.drop_last(), ..p }),
{
    let q = Parser { template_modes: p.template_modes.drop_last(), ..p };
    lemma_inv_iff(p);
    lemma_inv_iff(q);
    assert forall|i: int| 0 <= i < q.template_modes.len() implies crate::termination::template_mode_ok(
        #[trigger] q.template_modes[i],
    ) by {
        assert(q.template_modes[i] == p.template_modes[i]);
    }
    assert(crate::termination::template_count(q) == crate::termination::template_count(p));
}

/// Case 9 with a `template` element on the stack: pop to it, clear the
/// list to the last marker, pop the current template insertion mode,
/// reset the insertion mode, reprocess.
fn in_template_eof_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        old(p)@.template_modes.len() > 0,
        open_has_html(old(p)@, Tag::Template),
    ensures
        final(p)@ == ({
            let p2 = clear_to_last_marker(pop_until_popped(old(p)@, Tag::Template));
            reset_insertion_mode(Parser { template_modes: p2.template_modes.drop_last(), ..p2 })
        }),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    hide(reset_insertion_mode);
    hide(open_has_html);
    let ghost p0 = p@;
    proof {
        lemma_eof_pops_template(p0);
        reveal(parser_inv);
        crate::termination::helpers_ranking::lemma_template_count(p0);
    }
    pop_until_popped_exec(p, Tag::Template);
    clear_to_last_marker_exec(p);
    let ghost p2 = p@;
    proof {
        lemma_set_mode(p2, Mode::InBody);
    }
    // The mode is replaced by the reset below; "in body" keeps the
    // invariant while the stack of template insertion modes may be empty.
    p.mode = Mode::InBody;
    let ghost p3 = p@;
    proof {
        lemma_drop_template_mode(p3);
    }
    let _ = p.template_modes.pop();
    let ghost p4 = p@;
    reset_insertion_mode_exec(p);
    proof {
        let q = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
        assert(p4 == Parser { mode: Mode::InBody, ..q });
        lemma_reset_from_mode(q, p4, q.open.len() - 1);
        reveal(reset_insertion_mode);
    }
}


/// §13.2.6.4.16 the "in template" insertion mode ([`mode_in_template`]).
pub fn mode_in_template_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        crate::termination::rules_ok(Rules::Html(Mode::InTemplate), old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_in_template(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(in_template_switch);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    hide(reset_insertion_mode);
    hide(open_has_html);
    hide(stop_parsing);
    match t {
        ExecTok::Start(tt) => match tt.tag {
            Tag::Base | Tag::Basefont | Tag::Bgsound | Tag::Link | Tag::Meta | Tag::Noframes | Tag::Script | Tag::Style
            | Tag::Template | Tag::Title => {
                // 2.
                ExecOutcome::Using(Mode::InHead, ExecTok::Start(tt))
            },
            Tag::Caption | Tag::Colgroup | Tag::Tbody | Tag::Tfoot | Tag::Thead => {
                // 3.
                in_template_switch_exec(p, ExecTok::Start(tt), Mode::InTable)
            },
            Tag::Col => {
                // 4.
                in_template_switch_exec(p, ExecTok::Start(tt), Mode::InColumnGroup)
            },
            Tag::Tr => {
                // 5.
                in_template_switch_exec(p, ExecTok::Start(tt), Mode::InTableBody)
            },
            Tag::Td | Tag::Th => {
                // 6.
                in_template_switch_exec(p, ExecTok::Start(tt), Mode::InRow)
            },
            _ => {
                // 7.
                in_template_switch_exec(p, ExecTok::Start(tt), Mode::InBody)
            },
        },
        ExecTok::End(tt) => match tt.tag {
            Tag::Template => {
                // 2.
                ExecOutcome::Using(Mode::InHead, ExecTok::End(tt))
            },
            _ => {
                // 8.
                ExecOutcome::Done
            },
        },
        ExecTok::Eof => {
            // 9.
            if !open_has_html_exec(p, Tag::Template) {
                stop_parsing_exec(p);
                ExecOutcome::Done
            } else {
                in_template_eof_exec(p);
                ExecOutcome::Reprocess(ExecTok::Eof)
            }
        },
        _ => {
            // 1.
            ExecOutcome::Using(Mode::InBody, t)
        },
    }
}

} // verus!
