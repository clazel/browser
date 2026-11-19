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
            0 <= j2 < ins.len() && x == start_of(ins, j2) && #[trigger] scan(ins, tg, j2, fs2) is Some,
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
            0 <= j2 < ins.len() && x == start_of(ins, j2) && #[trigger] scan(
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
            let i = choose|i: int| 0 <= i < s.len() && #[trigger] s[i] == x;
            assert(i < s.len() - 1);
            assert(d[i] == x);
        }
        if d.contains(x) {
            let i = choose|i: int| 0 <= i < d.len() && #[trigger] d[i] == x;
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

/// `start_of` of the next instruction.
proof fn lemma_start_of_next(ins: Seq<Instr>, p: int)
    requires
        0 <= p < ins.len(),
    ensures
        start_of(ins, p + 1) == start_of(ins, p) + instr_len(ins[p]),
{
}

/// A jump or entry that lands at offset `x` (a target of the blob) is a
/// position the invariant holds at, when the machine is there with the context
/// invariant.
proof fn lemma_at_target(
    s: State,
    h: Handed,
    blob: Seq<u8>,
    ins: Seq<Instr>,
    entries: Seq<int>,
    x: int,
)
    requires
        policy(ins, entries),
        ctx_inv(s, h, blob),
        s.rip == h.code + x,
        seq_has(all_targets(ins, entries), x),
    ensures
        exists|j2: int, fs2: Facts|
            0 <= j2 < ins.len() && s.rip == h.code + start_of(ins, j2) && #[trigger] pos_inv(
                s,
                h,
                blob,
                ins,
                all_targets(ins, entries),
                j2,
                fs2,
                0,
            ),
{
    let tg = all_targets(ins, entries);
    lemma_target_pos(ins, entries, x);
    let (j2, fs2) = choose|j2: int, fs2: Facts|
        0 <= j2 < ins.len() && x == start_of(ins, j2) && #[trigger] scan(ins, tg, j2, fs2) is Some;
    lemma_scan_unfold(ins, tg, j2, fs2);
    assert(fs_in(ins, tg, j2, fs2) == no_facts());
    lemma_no_facts_hold(s, h);
    lemma_mid0(s, h, ins, j2, no_facts());
    assert(pos_inv(s, h, blob, ins, tg, j2, fs2, 0));
}

/// **One step from the invariant**: the step is safe, and, unless it is the
/// `ret` of an exit sequence, the invariant holds again.
#[verifier::rlimit(400)]
pub proof fn lemma_step_from_inv(
    u: spec_fn(nat) -> nat,
    blob: Seq<u8>,
    entries: Seq<int>,
    ins: Seq<Instr>,
    h: Handed,
    st: Seq<State>,
    ex: Seq<Instr>,
    k: int,
    j: int,
    fs: Facts,
    m: int,
)
    requires
        decodes_to(blob, ins),
        policy(ins, entries),
        handed_ok(h),
        run_ok(u, st, ex),
        0 <= k < ex.len(),
        pos_inv(st[k], h, blob, ins, all_targets(ins, entries), j, fs, m),
    ensures
        step_claim(h, ins, st, ex, k),
        !(ex[k] is Ret) ==> exists|j2: int, fs2: Facts, m2: int|
            #[trigger] pos_inv(st[k + 1], h, blob, ins, all_targets(ins, entries), j2, fs2, m2),
{
    let tg = all_targets(ins, entries);
    let s = st[k];
    let s2 = st[k + 1];
    let i = ex[k];
    let fs0 = fs_in(ins, tg, j, fs);
    lemma_scan_unfold(ins, tg, j, fs);
    let ulen = unit_len(ins, j, fs0);
    let p = j + m;
    assert(0 <= p < ins.len());
    assert(fetch_ok(s, i) && step(u, s, i) == Some(s2));
    lemma_fetch_is(blob, ins, h, s, i, p);
    assert(i == ins[p]);
    lemma_unit_step(u, h, blob, ins, j, fs0, m, s, s2, i);
    lemma_start_of_next(ins, p);
    assert(s.rip + instr_len(i) == h.code + start_of(ins, p + 1));
    assert(step_safe(h, s, i, s2));
    if i is Ret {
        assert(exit_unit_at(ins, j) && m == 2);
        assert(s.rip == h.code + start_of(ins, j + 2));
    } else if i is Jmp || jumps(s, i) {
        // a direct jump to a target of the blob
        let rel = if i is Jmp {
            i->Jmp_rel
        } else {
            i->Jcc_rel
        };
        assert(jump_rel(ins[p]) == Some(rel as int));
        assert(s2.rip == h.code + (start_of(ins, p + 1) + rel));
        lemma_jump_is_target(ins, entries, p, rel as int);
        lemma_at_target(s2, h, blob, ins, entries, start_of(ins, p + 1) + rel);
    } else {
        assert(s2.rip == s.rip + instr_len(i));
        if m + 1 < ulen {
            assert(p + 1 < ins.len());
            assert(pos_inv(s2, h, blob, ins, tg, j, fs, m + 1));
        } else {
            assert(m + 1 == ulen);
            // the unit is done: the next instruction starts the next unit
            assert(p + 1 < ins.len()) by {
                if p + 1 == ins.len() {
                    assert(ins[p] == ins.last());
                }
            }
            let j2 = j + ulen;
            let fs2 = unit_facts(ins, j, fs0);
            assert(scan(ins, tg, j2, fs2) is Some);
            lemma_scan_unfold(ins, tg, j2, fs2);
            let fs0b = fs_in(ins, tg, j2, fs2);
            if seq_has(tg, start_of(ins, j2)) {
                lemma_no_facts_hold(s2, h);
            }
            lemma_mid0(s2, h, ins, j2, fs0b);
            assert(pos_inv(s2, h, blob, ins, tg, j2, fs2, 0));
        }
    }
}

/// **The invariant holds at every step reached without a `ret`.**
proof fn lemma_reach(
    u: spec_fn(nat) -> nat,
    blob: Seq<u8>,
    entries: Seq<int>,
    ins: Seq<Instr>,
    h: Handed,
    e: int,
    st: Seq<State>,
    ex: Seq<Instr>,
    k: int,
)
    requires
        decodes_to(blob, ins),
        policy(ins, entries),
        entries.contains(e),
        handed_ok(h),
        st.len() > 0,
        start_ok(st[0], h, blob, e),
        run_ok(u, st, ex),
        0 <= k <= ex.len(),
        forall|j: int| 0 <= j < k ==> !((#[trigger] ex[j]) is Ret),
    ensures
        exists|j: int, fs: Facts, m: int|
            #[trigger] pos_inv(st[k], h, blob, ins, all_targets(ins, entries), j, fs, m),
    decreases k,
{
    let tg = all_targets(ins, entries);
    if k == 0 {
        lemma_seq_has_contains(entries, e);
        lemma_seq_has_concat(entries, jump_targets(ins, 0), e);
        lemma_at_target(st[0], h, blob, ins, entries, e);
    } else {
        lemma_reach(u, blob, entries, ins, h, e, st, ex, k - 1);
        let (j, fs, m) = choose|j: int, fs: Facts, m: int|
            #[trigger] pos_inv(st[k - 1], h, blob, ins, tg, j, fs, m);
        lemma_step_from_inv(u, blob, entries, ins, h, st, ex, k - 1, j, fs, m);
        assert(!(ex[k - 1] is Ret));
    }
}

/// **The safety theorem** (jit.md exit criterion 2, x86-64): over every
/// execution prefix of an accepted blob started at an accepted entry in a state
/// satisfying the context invariant, [`safe_execution`] holds.
pub proof fn safety_theorem(
    u: spec_fn(nat) -> nat,
    blob: Seq<u8>,
    entries: Seq<int>,
    ins: Seq<Instr>,
    h: Handed,
    e: int,
    st: Seq<State>,
    ex: Seq<Instr>,
)
    requires
        decodes_to(blob, ins),
        policy(ins, entries),
        entries.contains(e),
        handed_ok(h),
        st.len() > 0,
        start_ok(st[0], h, blob, e),
        run_ok(u, st, ex),
    ensures
        safe_execution(h, ins, st, ex),
{
    assert forall|k: int|
        0 <= k < ex.len() && (forall|j: int| 0 <= j < k ==> !((#[trigger] ex[j]) is Ret))
            implies step_claim(h, ins, st, ex, k) by {
        lemma_reach(u, blob, entries, ins, h, e, st, ex, k);
        let (j, fs, m) = choose|j: int, fs: Facts, m: int|
            #[trigger] pos_inv(st[k], h, blob, ins, all_targets(ins, entries), j, fs, m);
        lemma_step_from_inv(u, blob, entries, ins, h, st, ex, k, j, fs, m);
    }
}

/// The theorem as [`super::safety::safety_statement`] states it.
pub proof fn safety_holds(
    u: spec_fn(nat) -> nat,
    blob: Seq<u8>,
    entries: Seq<int>,
    ins: Seq<Instr>,
    h: Handed,
    e: int,
    st: Seq<State>,
    ex: Seq<Instr>,
)
    ensures
        safety_statement(u, blob, entries, ins, h, e, st, ex),
{
    if decodes_to(blob, ins) && policy(ins, entries) && entries.contains(e) && handed_ok(h)
        && st.len() > 0 && start_ok(st[0], h, blob, e) && run_ok(u, st, ex) {
        safety_theorem(u, blob, entries, ins, h, e, st, ex);
    }
}

} // verus!
