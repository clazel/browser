//! Units: the bridge from a list of the validator's units to its `scan`
//! (jit.md item J.9, "every emitted blob is accepted", x86-64).
//!
//! The validator's `scan` ([`clazel_codecheck::spec::scan`]) walks the
//! instruction list from the front, recognizing an exit sequence (3
//! instructions), a bounds-check sequence (8) or a single instruction at each
//! unit start, and forgets what it knows at each jump target. This module
//! says: **if the instruction list is the concatenation of a list of units,
//! each of which is of one of those three shapes, then `scan` walks exactly
//! those units** ([`lemma_scan_units`]), and what it holds at each unit is
//! computed by [`ucheck`], a recursion over the unit list, not over
//! instruction positions. The back end's proof then works on unit lists that
//! mirror its templates (`crate::cfaccept`).
//!
//! The one place `scan` looks past a unit is a single instruction, where it
//! must rule out an exit sequence and a bounds-check sequence starting
//! there. Both need the instruction two places on to be a `ret` and a `jb`
//! (`jcc` 2): no instruction at the first or second place of any unit is
//! either ([`ok2`], [`lemma_uok_ok2`]), so neither starts at a single
//! instruction ([`lemma_scan_units`]).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::runseq::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A list of units: each is a list of instructions the validator treats as one
/// step of its scan.
pub type Us = Seq<Seq<x64::Instr>>;

/// All the instructions of the units, in order.
pub open spec fn uflat(us: Us) -> Seq<x64::Instr>
    decreases us.len(),
{
    if us.len() == 0 {
        Seq::empty()
    } else {
        us[0] + uflat(us.skip(1))
    }
}

/// The length in bytes of all the units.
pub open spec fn blen(us: Us) -> nat
    decreases us.len(),
{
    if us.len() == 0 {
        0
    } else {
        code_len(us[0]) + blen(us.skip(1))
    }
}

/// One unit per instruction.
pub open spec fn ones(c: Seq<x64::Instr>) -> Us {
    c.map_values(|i: x64::Instr| seq![i])
}

/// `jcc` with condition code 2 (`jb`): the second instruction of a
/// bounds-check sequence.
pub open spec fn jcc2(i: x64::Instr) -> bool {
    i is Jcc && i->Jcc_cc == 2
}

/// An instruction that cannot be the third instruction of an exit sequence
/// (a `ret`) or of a bounds-check sequence (a `jcc 2`).
pub open spec fn ok2(i: x64::Instr) -> bool {
    !(i is Ret) && !jcc2(i)
}

/// A unit is well formed: a single instruction that is neither a `ret` nor a
/// `jcc 2`, an exit sequence, or a bounds-check sequence (both as the
/// validator recognizes them).
pub open spec fn uok(u: Seq<x64::Instr>) -> bool {
    (u.len() == 1 && ok2(u[0])) || (u.len() == 3 && clazel_codecheck::spec::exit_unit_at(u, 0))
        || (u.len() == 8 && clazel_codecheck::spec::check_unit_at(u, 0))
}

/// What the scan holds after a unit, from what it held before.
pub open spec fn ufacts(u: Seq<x64::Instr>, fs: clazel_codecheck::spec::Facts) -> Option<
    clazel_codecheck::spec::Facts,
> {
    if u.len() == 1 {
        clazel_codecheck::spec::plain_ok(fs, u[0])
    } else if u.len() == 3 {
        Some(clazel_codecheck::spec::no_facts())
    } else if u.len() == 8 {
        Some(clazel_codecheck::spec::check_facts(fs, u, 0))
    } else {
        None
    }
}

/// The scan over the units from byte position `pos` with facts `fs`, where
/// `p` says which positions are jump targets (the scan forgets its facts
/// there). `None` if some unit is refused.
pub open spec fn ucheck(
    us: Us,
    pos: int,
    fs: clazel_codecheck::spec::Facts,
    p: spec_fn(int) -> bool,
) -> Option<clazel_codecheck::spec::Facts>
    decreases us.len(),
{
    if us.len() == 0 {
        Some(fs)
    } else {
        let fs0 = if p(pos) {
            clazel_codecheck::spec::no_facts()
        } else {
            fs
        };
        match ufacts(us[0], fs0) {
            None => None,
            Some(f) => ucheck(us.skip(1), pos + code_len(us[0]) as int, f, p),
        }
    }
}

/// The unit starts the scan reports.
pub open spec fn ustarts(us: Us, pos: int) -> Seq<int>
    decreases us.len(),
{
    if us.len() == 0 {
        Seq::empty()
    } else {
        seq![pos] + ustarts(us.skip(1), pos + code_len(us[0]) as int)
    }
}

/// `x` is the start of a unit.
pub open spec fn ub(us: Us, pos: int, x: int) -> bool
    decreases us.len(),
{
    us.len() > 0 && (x == pos || ub(us.skip(1), pos + code_len(us[0]) as int, x))
}

/// `x` is the start of a unit, or the end of the last.
pub open spec fn ubi(us: Us, pos: int, x: int) -> bool {
    ub(us, pos, x) || x == pos + blen(us)
}

// ----------------------------------------------------------------------------
// Lists of units
// ----------------------------------------------------------------------------

/// The instructions of a concatenation of unit lists.
pub proof fn lemma_uflat_cat(a: Us, b: Us)
    ensures
        uflat(a + b) == uflat(a) + uflat(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(uflat(a) + uflat(b) =~= uflat(b));
    } else {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        lemma_uflat_cat(a.skip(1), b);
        assert(uflat(a + b) =~= a[0] + (uflat(a.skip(1)) + uflat(b)));
        assert(uflat(a) =~= a[0] + uflat(a.skip(1)));
    }
}

/// The length of a concatenation of unit lists.
pub proof fn lemma_blen_cat(a: Us, b: Us)
    ensures
        blen(a + b) == blen(a) + blen(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        lemma_blen_cat(a.skip(1), b);
    }
}

/// The length of the units is the length of their instructions.
pub proof fn lemma_blen_flat(us: Us)
    ensures
        blen(us) == code_len(uflat(us)),
    decreases us.len(),
{
    if us.len() > 0 {
        lemma_blen_flat(us.skip(1));
        lemma_code_len_append(us[0], uflat(us.skip(1)));
    }
}

/// The instructions of a list of single-instruction units are the list.
pub proof fn lemma_uflat_ones(c: Seq<x64::Instr>)
    ensures
        uflat(ones(c)) =~= c,
        ones(c).len() == c.len(),
        forall|k: int| 0 <= k < c.len() ==> #[trigger] ones(c)[k] == seq![c[k]],
    decreases c.len(),
{
    if c.len() > 0 {
        assert(ones(c).skip(1) =~= ones(c.skip(1)));
        lemma_uflat_ones(c.skip(1));
        assert(ones(c)[0] == seq![c[0]]);
        assert(uflat(ones(c)) =~= seq![c[0]] + c.skip(1));
    }
}

/// The length of a one-unit list.
pub proof fn lemma_blen_one(u: Seq<x64::Instr>)
    ensures
        blen(seq![u]) == code_len(u),
{
    assert(seq![u].skip(1) =~= Seq::<Seq<x64::Instr>>::empty());
    assert(blen(Seq::<Seq<x64::Instr>>::empty()) == 0);
}

/// The length of a two-unit list.
pub proof fn lemma_blen_two(u: Seq<x64::Instr>, v: Seq<x64::Instr>)
    ensures
        blen(seq![u, v]) == code_len(u) + code_len(v),
{
    assert(seq![u, v].skip(1) =~= seq![v]);
    lemma_blen_one(v);
}

/// The length of single-instruction units.
pub proof fn lemma_blen_ones(c: Seq<x64::Instr>)
    ensures
        blen(ones(c)) == code_len(c),
{
    lemma_uflat_ones(c);
    lemma_blen_flat(ones(c));
}

// ----------------------------------------------------------------------------
// The scan over a concatenation
// ----------------------------------------------------------------------------

/// The scan over a concatenation is the scan over the first, then over the
/// second from where the first ended, with the facts it ended with.
pub proof fn lemma_ucheck_cat(
    a: Us,
    b: Us,
    pos: int,
    fs: clazel_codecheck::spec::Facts,
    p: spec_fn(int) -> bool,
)
    ensures
        ucheck(a + b, pos, fs, p) == match ucheck(a, pos, fs, p) {
            None => None,
            Some(f) => ucheck(b, pos + blen(a), f, p),
        },
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        let fs0 = if p(pos) {
            clazel_codecheck::spec::no_facts()
        } else {
            fs
        };
        match ufacts(a[0], fs0) {
            None => {},
            Some(f) => {
                lemma_ucheck_cat(a.skip(1), b, pos + code_len(a[0]) as int, f, p);
            },
        }
    }
}

/// The unit starts of a concatenation.
pub proof fn lemma_ub_cat(a: Us, b: Us, pos: int, x: int)
    ensures
        ub(a + b, pos, x) == (ub(a, pos, x) || ub(b, pos + blen(a), x)),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        lemma_ub_cat(a.skip(1), b, pos + code_len(a[0]) as int, x);
    }
}

/// A boundary of either part is a boundary of the concatenation.
pub proof fn lemma_ubi_cat(a: Us, b: Us, pos: int, x: int)
    requires
        ubi(a, pos, x) || ubi(b, pos + blen(a), x),
    ensures
        ubi(a + b, pos, x),
{
    lemma_ub_cat(a, b, pos, x);
    lemma_blen_cat(a, b);
    if x == pos + blen(a) && b.len() > 0 {
        // the end of `a` is the first unit start of `b`
        assert(ub(b, pos + blen(a), x));
    }
}

/// The scan reports unit starts, and `ub` is membership in them.
pub proof fn lemma_seq_has_ustarts(us: Us, pos: int, x: int)
    ensures
        clazel_codecheck::spec::seq_has(ustarts(us, pos), x) == ub(us, pos, x),
    decreases us.len(),
{
    if us.len() > 0 {
        let rest = ustarts(us.skip(1), pos + code_len(us[0]) as int);
        clazel_codecheck::acc_lemmas::lemma_seq_has_concat(seq![pos], rest, x);
        clazel_codecheck::acc_lemmas::lemma_seq_has_single(pos, x);
        lemma_seq_has_ustarts(us.skip(1), pos + code_len(us[0]) as int, x);
    } else {
        reveal_with_fuel(clazel_codecheck::spec::seq_has, 1);
    }
}

// ----------------------------------------------------------------------------
// Positions
// ----------------------------------------------------------------------------

/// The byte position of instruction `j + m` is that of `j` plus the length of
/// the `m` instructions between, which are `u`'s.
pub proof fn lemma_start_of_run(ins: Seq<x64::Instr>, j: int, u: Seq<x64::Instr>, m: int)
    requires
        0 <= j,
        0 <= m <= u.len(),
        j + m <= ins.len(),
        forall|i: int| 0 <= i < m ==> ins[j + i] == #[trigger] u[i],
    ensures
        clazel_codecheck::spec::start_of(ins, j + m) == clazel_codecheck::spec::start_of(ins, j)
            + code_len(u.take(m)),
    decreases m,
{
    if m == 0 {
        assert(u.take(0) =~= Seq::<x64::Instr>::empty());
    } else {
        lemma_start_of_run(ins, j, u, m - 1);
        assert(u.take(m) =~= u.take(m - 1) + seq![u[m - 1]]);
        lemma_code_len_append(u.take(m - 1), seq![u[m - 1]]);
        lemma_code_len_one(u[m - 1]);
        assert(ins[j + (m - 1)] == u[m - 1]);
    }
}

/// `start_of` of a whole unit.
pub proof fn lemma_start_of_unit(ins: Seq<x64::Instr>, j: int, u: Seq<x64::Instr>)
    requires
        0 <= j,
        j + u.len() <= ins.len(),
        forall|i: int| 0 <= i < u.len() ==> ins[j + i] == #[trigger] u[i],
    ensures
        clazel_codecheck::spec::start_of(ins, j + u.len()) == clazel_codecheck::spec::start_of(
            ins,
            j,
        ) + code_len(u),
{
    lemma_start_of_run(ins, j, u, u.len() as int);
    assert(u.take(u.len() as int) =~= u);
}

/// A unit's first two instructions are neither a `ret` nor a `jcc 2`.
pub proof fn lemma_uok_ok2(u: Seq<x64::Instr>, i: int)
    requires
        uok(u),
        0 <= i <= 1,
        i < u.len(),
    ensures
        ok2(u[i]),
{
    if u.len() == 8 {
        let c = clazel_codecheck::spec::check_params(u, 0)->Some_0;
        assert(clazel_codecheck::spec::check_unit_at(u, 0));
        assert(u[0] == clazel_codecheck::spec::check_instr(0, c));
        assert(u[1] == clazel_codecheck::spec::check_instr(1, c));
    }
}

/// The units' lengths are 1, 3 or 8.
pub proof fn lemma_uok_len(u: Seq<x64::Instr>)
    requires
        uok(u),
    ensures
        u.len() == 1 || u.len() == 3 || u.len() == 8,
{
}

// ----------------------------------------------------------------------------
// The bridge
// ----------------------------------------------------------------------------

/// The instruction two places on from a single-instruction unit is not a
/// `ret` or a `jcc 2` (or there are fewer than three instructions left).
proof fn lemma_lookahead(ins: Seq<x64::Instr>, j: int, us: Us)
    requires
        0 <= j <= ins.len(),
        ins.skip(j) =~= uflat(us),
        us.len() >= 1,
        us[0].len() == 1,
        forall|k: int| 0 <= k < us.len() ==> uok(us[k]),
    ensures
        j + 2 >= ins.len() || ok2(ins[j + 2]),
{
    let rest = us.skip(1);
    if rest.len() == 0 {
        assert(uflat(us) =~= us[0] + uflat(rest));
        assert(uflat(rest).len() == 0);
        assert(ins.skip(j).len() == 1);
    }
    if rest.len() >= 1 && j + 2 < ins.len() {
        let u1 = rest[0];
        assert(uok(u1));
        lemma_uok_len(u1);
        let r1 = rest.skip(1);
        assert(uflat(rest) =~= u1 + uflat(r1));
        assert(uflat(us) =~= us[0] + uflat(rest));
        assert(uflat(us) =~= us[0] + (u1 + uflat(r1)));
        if u1.len() >= 2 {
            lemma_uok_ok2(u1, 1);
            assert(ins[j + 2] == uflat(us)[2]);
            assert(uflat(us)[2] == u1[1]);
        } else {
            assert(r1.len() >= 1) by {
                assert(uflat(us).len() == 1 + 1 + uflat(r1).len());
            }
            let u2 = r1[0];
            assert(uok(u2));
            lemma_uok_ok2(u2, 0);
            assert(uflat(r1) =~= u2 + uflat(r1.skip(1)));
            assert(ins[j + 2] == uflat(us)[2]);
            assert(uflat(us)[2] == u2[0]);
        }
    }
}

/// **The scan walks the units.** If the instructions from `j` on are those of
/// the units, every unit is well formed, `p` is membership in the scan's
/// targets, and [`ucheck`] accepts the units, then `scan` accepts them and
/// reports their starts.
#[verifier::rlimit(200)]
pub proof fn lemma_scan_units(
    ins: Seq<x64::Instr>,
    tg: Seq<int>,
    j: int,
    us: Us,
    pos: int,
    fs: clazel_codecheck::spec::Facts,
    p: spec_fn(int) -> bool,
)
    requires
        0 <= j <= ins.len(),
        ins.skip(j) =~= uflat(us),
        clazel_codecheck::spec::start_of(ins, j) == pos,
        forall|k: int| 0 <= k < us.len() ==> uok(us[k]),
        forall|x: int| clazel_codecheck::spec::seq_has(tg, x) == p(x),
        ucheck(us, pos, fs, p) is Some,
    ensures
        clazel_codecheck::spec::scan(ins, tg, j, fs) == Some(ustarts(us, pos)),
    decreases us.len(),
{
    if us.len() == 0 {
        assert(uflat(us).len() == 0);
        assert(ins.skip(j).len() == 0);
    } else {
        let u = us[0];
        let rest = us.skip(1);
        assert(uok(u));
        lemma_uok_len(u);
        assert(uflat(us) =~= u + uflat(rest));
        assert forall|i: int| 0 <= i < u.len() implies ins[j + i] == #[trigger] u[i] by {
            assert(ins.skip(j)[i] == uflat(us)[i]);
        }
        assert(j + u.len() <= ins.len());
        let fs0 = if p(pos) {
            clazel_codecheck::spec::no_facts()
        } else {
            fs
        };
        let f = ufacts(u, fs0)->Some_0;
        assert(ufacts(u, fs0) is Some);
        lemma_start_of_unit(ins, j, u);
        // which unit does the scan find at `j`?
        if u.len() == 3 {
            assert(clazel_codecheck::spec::exit_unit_at(ins, j));
        } else if u.len() == 8 {
            let c = clazel_codecheck::spec::check_params(u, 0)->Some_0;
            assert(clazel_codecheck::spec::check_unit_at(u, 0));
            assert(u[0] == clazel_codecheck::spec::check_instr(0, c));
            assert(ins[j] == u[0]);
            assert(!clazel_codecheck::spec::exit_unit_at(ins, j));
            assert(clazel_codecheck::spec::check_params(ins, j) == clazel_codecheck::spec::check_params(
                u,
                0,
            ));
            assert(clazel_codecheck::spec::check_unit_at(ins, j));
            assert(clazel_codecheck::spec::check_facts(fs0, ins, j)
                == clazel_codecheck::spec::check_facts(fs0, u, 0));
        } else {
            lemma_lookahead(ins, j, us);
            assert(!clazel_codecheck::spec::exit_unit_at(ins, j));
            assert(!clazel_codecheck::spec::check_unit_at(ins, j));
        }
        let ul = clazel_codecheck::spec::unit_at(ins, j, fs0)->Some_0;
        assert(clazel_codecheck::spec::unit_at(ins, j, fs0) is Some);
        assert(ul.len == u.len() && ul.facts == f);
        assert(ins.skip(j + u.len()) =~= ins.skip(j).skip(u.len() as int));
        assert((u + uflat(rest)).skip(u.len() as int) =~= uflat(rest));
        assert(ins.skip(j + u.len()) =~= uflat(rest));
        lemma_scan_units(ins, tg, j + u.len(), rest, pos + code_len(u) as int, f, p);
    }
}

} // verus!
