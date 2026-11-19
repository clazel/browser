//! **The proof of the safety theorem** ([`super::safety`]): the machine
//! invariant [`pos_inv`] holds at every position an execution reaches, by
//! induction on the number of steps, and each step is safe.
//!
//! The invariant says: the machine is at instruction `m` of the unit that the
//! scan found at instruction `j` ([`super::safety_unit::mid_ok`]); `rip` is
//! that instruction's address; the context invariant holds; and the scan, run
//! from `j` with the facts `fs`, is accepted. A step from such a state is one
//! of [`super::safety_unit::lemma_unit_step`]'s cases; the next position is the
//! next instruction of the unit, the start of the next unit (the scan found it),
//! or a jump target (the policy made every target a unit start, where nothing
//! is known).

#[allow(unused_imports)]
use super::acc_lemmas::*;
#[allow(unused_imports)]
use super::safety::*;
#[allow(unused_imports)]
use super::safety_chk::*;
#[allow(unused_imports)]
use super::safety_inv::*;
#[allow(unused_imports)]
use super::safety_sem::*;
#[allow(unused_imports)]
use super::safety_unit::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The facts at entry to instruction `j` as the scan uses them: forgotten at a
/// target.
pub open spec fn fs_in(ins: Seq<Instr>, tg: Seq<int>, j: int, fs: Facts) -> Facts {
    if seq_has(tg, start_of(ins, j)) {
        no_facts()
    } else {
        fs
    }
}

/// **The invariant**: the machine is at instruction `m` of the unit starting
/// at instruction `j`, which the scan (entered there with `fs`) accepts.
pub open spec fn pos_inv(
    s: State,
    h: Handed,
    blob: Seq<u8>,
    ins: Seq<Instr>,
    tg: Seq<int>,
    j: int,
    fs: Facts,
    m: int,
) -> bool {
    &&& 0 <= j < ins.len()
    &&& scan(ins, tg, j, fs) is Some
    &&& unit_at(ins, j, fs_in(ins, tg, j, fs)) is Some
    &&& 0 <= m < unit_len(ins, j, fs_in(ins, tg, j, fs))
    &&& s.rip == h.code + start_of(ins, j + m)
    &&& ctx_inv(s, h, blob)
    &&& mid_ok(s, h, ins, j, fs_in(ins, tg, j, fs), m)
}

/// `scan` unfolds one unit.
proof fn lemma_scan_unfold(ins: Seq<Instr>, tg: Seq<int>, j: int, fs: Facts)
    requires
        0 <= j < ins.len(),
        scan(ins, tg, j, fs) is Some,
    ensures
        unit_at(ins, j, fs_in(ins, tg, j, fs)) is Some,
        unit_len(ins, j, fs_in(ins, tg, j, fs)) >= 1,
        j + unit_len(ins, j, fs_in(ins, tg, j, fs)) <= ins.len(),
        scan(
            ins,
            tg,
            j + unit_len(ins, j, fs_in(ins, tg, j, fs)),
            unit_facts(ins, j, fs_in(ins, tg, j, fs)),
        ) is Some,
{
    reveal_with_fuel(scan, 2);
}

/// Every start the scan finds is the start of an instruction `j2` at which a
/// scan (from some facts) is accepted.
proof fn lemma_scan_start_pos(ins: Seq<Instr>, tg: Seq<int>, j: int, fs: Facts, x: int)
    requires
        0 <= j,
        scan(ins, tg, j, fs) is Some,
        seq_has(scan(ins, tg, j, fs)->Some_0, x),
    ensures
        exists|j2: int, fs2: Facts|
            0 <= j2 < ins.len() && x == start_of(ins, j2) && scan(ins, tg, j2, fs2) is Some,
    decreases ins.len() - j,
{
    reveal_with_fuel(scan, 2);
    if j < ins.len() {
        lemma_scan_unfold(ins, tg, j, fs);
        let here = start_of(ins, j);
        let fs0 = fs_in(ins, tg, j, fs);
        let u = unit_at(ins, j, fs0)->Some_0;
        let rest = scan(ins, tg, j + u.len, u.facts)->Some_0;
        lemma_seq_has_concat(seq![here], rest, x);
        lemma_seq_has_single(here, x);
        if x != here {
            lemma_scan_start_pos(ins, tg, j + u.len, u.facts, x);
        } else {
            assert(0 <= j < ins.len() && x == start_of(ins, j) && scan(ins, tg, j, fs) is Some);
        }
    }
}

/// A target (entry or jump target) of an accepted blob is the start of an
/// instruction at which the scan is accepted.
proof fn lemma_target_pos(ins: Seq<Instr>, entries: Seq<int>, x: int)
    requires
        policy(ins, entries),
        seq_has(all_targets(ins, entries), x),
    ensures
        exists|j2: int, fs2: Facts|
            0 <= j2 < ins.len() && x == start_of(ins, j2) && scan(
                ins,
                all_targets(ins, entries),
                j2,
                fs2,
            ) is Some,
{
    let tg = all_targets(ins, entries);
    let starts = scan(ins, tg, 0, no_facts())->Some_0;
    lemma_subset_elim(tg, starts, x);
    lemma_scan_start_pos(ins, tg, 0, no_facts(), x);
}

/// The target of the jump at instruction `j` is among the jump targets from
/// `j0` on.
proof fn lemma_jt_has(ins: Seq<Instr>, j0: int, j: int, r: int)
    requires
        0 <= j0 <= j < ins.len(),
        jump_rel(ins[j]) == Some(r),
    ensures
        seq_has(jump_targets(ins, j0), start_of(ins, j + 1) + r),
    decreases j - j0,
{
    super::validate::lemma_jump_targets_step(ins, j0);
    let here: Seq<int> = match jump_rel(ins[j0]) {
        Some(r0) => seq![start_of(ins, j0 + 1) + r0],
        None => Seq::empty(),
    };
    lemma_seq_has_concat(here, jump_targets(ins, j0 + 1), start_of(ins, j + 1) + r);
    if j0 == j {
        lemma_seq_has_single(start_of(ins, j + 1) + r, start_of(ins, j + 1) + r);
    } else {
        lemma_jt_has(ins, j0 + 1, j, r);
    }
}

/// A jump target is a target.
proof fn lemma_jump_is_target(ins: Seq<Instr>, entries: Seq<int>, j: int, r: int)
    requires
        0 <= j < ins.len(),
        jump_rel(ins[j]) == Some(r),
    ensures
        seq_has(all_targets(ins, entries), start_of(ins, j + 1) + r),
{
    lemma_jt_has(ins, 0, j, r);
    lemma_seq_has_concat(entries, jump_targets(ins, 0), start_of(ins, j + 1) + r);
}

/// `seq_has` is `contains`.
proof fn lemma_seq_has_contains(s: Seq<int>, x: int)
    ensures
        seq_has(s, x) == s.contains(x),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_seq_has_contains(s.drop_last(), x);
        let d = s.drop_last();
        assert(s =~= d.push(s.last()));
        if s.contains(x) && s.last() != x {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
            assert(i < s.len() - 1);
            assert(d[i] == x);
        }
        if d.contains(x) {
            let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
            assert(s[i] == x);
        }
    }
}

/// Facts that hold are enough for the first position of any unit.
proof fn lemma_mid0(s: State, h: Handed, ins: Seq<Instr>, j: int, fs0: Facts)
    requires
        holds(s, h, fs0),
    ensures
        mid_ok(s, h, ins, j, fs0, 0),
{
    if !exit_unit_at(ins, j) && check_unit_at(ins, j) {
        let c = check_params(ins, j)->Some_0;
        assert forall|r: u8| r < 16 && r != c.t && r != c.z implies fact_holds(
            s,
            h,
            r,
            #[trigger] fact_of(fs0, r),
        ) by {}
    }
}

/// The instruction fetched at the position is the one the blob has there.
proof fn lemma_fetch_is(
    blob: Seq<u8>,
    ins: Seq<Instr>,
    h: Handed,
    s: State,
    i: Instr,
    p: int,
)
    requires
        decodes_to(blob, ins),
        ctx_inv(s, h, blob),
        0 <= p < ins.len(),
        s.rip == h.code + start_of(ins, p),
        fetch_ok(s, i),
    ensures
        i == ins[p],
{
    clazel_x64::decoder_proofs::lemma_canonical_prefix_free();
    super::validate::lemma_enc_all_len(ins);
    super::uniq::lemma_enc_all_index(ins, p);
    assert(blob == enc_all(ins));
    let e = encode(ins[p]);
    let st = start_of(ins, p);
    assert(valid_instr(ins[p]));
    let n = if instr_len(i) > instr_len(ins[p]) {
        instr_len(i)
    } else {
        instr_len(ins[p])
    };
    let bytes = Seq::new(n, |x: int| if s.mem.dom().contains(s.rip + x) {
        s.mem[s.rip + x]
    } else {
        0u8
    });
    assert(bytes.subrange(0, encode(i).len() as int) =~= encode(i));
    super::validate::lemma_start_of_ge(ins, p);
    assert forall|x: int| 0 <= x < e.len() implies bytes.subrange(0, e.len() as int)[x] == e[x] by {
        assert(0 <= st + x < blob.len());
        assert(s.mem.dom().contains(h.code + (st + x)));
        assert(blob[st + x] == enc_all(ins).subrange(st, st + e.len() as int)[x]);
    }
    assert(bytes.subrange(0, e.len() as int) =~= e);
    assert(starts_with_encoding(bytes, i));
    assert(starts_with_encoding(bytes, ins[p]));
    assert(clazel_x64::contract::canonical_prefix_free());
    assert(starts_with_encoding(bytes, i) && starts_with_encoding(bytes, ins[p]) ==> i == ins[p]);
}

} // verus!
