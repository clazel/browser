//! **Unit starts and their facts** (A64): what an accepted blob's scan guarantees,
//! phrased for the machine-level invariant. The units the scan takes from
//! instruction 0 ([`chain_facts`]) are the positions the invariant allows;
//! every entry and jump target is one, with no facts; each such unit has a
//! recognized shape and fits in the blob; the unit after one is again one.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The 4 bytes of the canonical encoding of `i` (kept opaque so that the
/// large `encode` is unfolded only where it must be).
#[verifier::opaque]
pub open spec fn word_of(i: Instr) -> Seq<u8> {
    word_bytes(encode(i))
}

/// **What a configuration the sandbox may hand over says**, without the
/// large `encode` unfolded: the blob is the words [`word_of`] of the
/// instructions, which are valid, the policy holds, and the layout is
/// disjoint and below `2^47`.
pub proof fn lemma_cfg(c: Cfg)
    requires
        cfg_ok(c),
    ensures
        policy(c.ins, c.entries),
        all_valid(c.ins),
        c.blob.len() == 4 * c.ins.len(),
        word_of_len(),
        forall|j: int|
            0 <= j < c.ins.len() ==> c.blob.subrange(4 * j, 4 * j + 4) == #[trigger] word_of(
                c.ins[j],
            ),
        c.bases.len() == abi::num_regions(),
        c.bounds.len() == abi::num_regions(),
        0 <= c.code,
        c.code % 4 == 0,
        c.code + c.blob.len() <= lim(),
        0 <= c.ctx,
        c.ctx + abi::ctx_size() <= lim(),
        disjoint(c.code, c.blob.len() as int, c.ctx, abi::ctx_size()),
        forall|k: int| 0 <= k < abi::num_regions() ==> #[trigger] region_ok(c, k),
        0 <= c.sp < p2(64),
        0 <= c.lr < p2(64),
        disjoint(c.lr, 1, c.code, c.blob.len() as int),
{
    reveal(cfg_ok);
    reveal(word_of);
    assert(decodes_to(c.blob, c.ins));
    assert forall|j: int| 0 <= j < c.ins.len() implies c.blob.subrange(4 * j, 4 * j + 4)
        == #[trigger] word_of(c.ins[j]) by {
        assert(c.blob.subrange(4 * j, 4 * j + 4) == word_bytes(encode(c.ins[j])));
    }
}

/// Every [`word_of`] has 4 bytes.
pub open spec fn word_of_len() -> bool {
    forall|i: Instr| #[trigger] word_of(i).len() == 4
}

/// The proof of [`word_of_len`].
pub proof fn lemma_word_of_len()
    ensures
        word_of_len(),
{
    reveal(word_of);
}

/// Forgetting twice is forgetting once.
pub proof fn lemma_forgotten_idem(c: Cfg, j: int, fs: Facts)
    ensures
        forgotten(c, j, forgotten(c, j, fs)) == forgotten(c, j, fs),
{
}

/// A fact list reached at a unit start is already forgotten there, and the
/// facts reached by continuing from `j` to `t2` are the ones reached by
/// continuing from `t`.
pub proof fn lemma_chain_append(c: Cfg, j: int, fs: Facts, t: int, f: Facts, t2: int)
    requires
        0 <= j <= t <= t2,
        chain_facts(c, j, fs, t) == Some(f),
    ensures
        f == forgotten(c, t, f),
        chain_facts(c, j, fs, t2) == chain_facts(c, t, f, t2),
    decreases t - j,
{
    let fs0 = forgotten(c, j, fs);
    if j == t {
        assert(f == fs0);
        lemma_forgotten_idem(c, j, fs);
    } else {
        let u = unit_at(c.ins, j, fs0)->Some_0;
        assert(unit_at(c.ins, j, fs0) is Some);
        assert(u.len >= 1 && j + u.len <= t);
        lemma_chain_append(c, j + u.len, u.facts, t, f, t2);
    }
}

/// The facts at the next unit start: the unit's facts, forgotten there.
pub proof fn lemma_next_start(c: Cfg, t: int, f: Facts, u: Unit)
    requires
        start_facts(c, t) == Some(f),
        0 <= t < c.ins.len(),
        unit_at(c.ins, t, f) == Some(u),
        u.len >= 1,
    ensures
        start_facts(c, t + u.len) == Some(forgotten(c, t + u.len, u.facts)),
{
    lemma_chain_append(c, 0, no_facts(), t, f, t + u.len);
    lemma_forgotten_idem(c, t, f);
    reveal_with_fuel(chain_facts, 2);
    assert(forgotten(c, t, f) == f);
    assert(chain_facts(c, t, f, t + u.len) == Some(forgotten(c, t + u.len, u.facts)));
}

/// The scan from a reached unit start is the scan with the facts of that
/// start.
pub proof fn lemma_scan_reach(c: Cfg, j: int, fs: Facts, t: int, f: Facts)
    requires
        0 <= j <= t < c.ins.len(),
        scan(c.ins, all_targets(c.ins, c.entries), j, fs) is Some,
        chain_facts(c, j, fs, t) == Some(f),
    ensures
        scan(c.ins, all_targets(c.ins, c.entries), t, f) is Some,
    decreases t - j,
{
    let tg = all_targets(c.ins, c.entries);
    let fs0 = forgotten(c, j, fs);
    reveal_with_fuel(scan, 2);
    if j == t {
        lemma_forgotten_idem(c, j, fs);
        assert(forgotten(c, t, f) == f);
    } else {
        let u = unit_at(c.ins, j, fs0)->Some_0;
        lemma_scan_reach(c, j + u.len, u.facts, t, f);
    }
}

/// **Every reached unit start has a unit that fits in the blob.**
pub proof fn lemma_unit_ok(c: Cfg, t: int, f: Facts)
    requires
        cfg_ok(c),
        start_facts(c, t) == Some(f),
        0 <= t < c.ins.len(),
    ensures
        unit_at(c.ins, t, f) is Some,
        unit_at(c.ins, t, f)->Some_0.len >= 1,
        t + unit_at(c.ins, t, f)->Some_0.len <= c.ins.len(),
{
    let tg = all_targets(c.ins, c.entries);
    lemma_cfg(c);
    assert(policy(c.ins, c.entries));
    assert(scan(c.ins, tg, 0, no_facts()) is Some);
    lemma_scan_reach(c, 0, no_facts(), t, f);
    lemma_chain_append(c, 0, no_facts(), t, f, t);
    reveal_with_fuel(scan, 2);
    assert(forgotten(c, t, f) == f);
}

/// Every offset the scan lists as a unit start is a unit start that the
/// chain from `j` reaches.
pub proof fn lemma_scan_chain_starts(c: Cfg, j: int, fs: Facts, x: int)
    requires
        0 <= j,
        scan(c.ins, all_targets(c.ins, c.entries), j, fs) is Some,
        seq_has(scan(c.ins, all_targets(c.ins, c.entries), j, fs)->Some_0, x),
    ensures
        exists|t: int|
            j <= t < c.ins.len() && x == start_of(c.ins, t) && chain_facts(c, j, fs, t) is Some,
    decreases c.ins.len() - j,
{
    let tg = all_targets(c.ins, c.entries);
    reveal_with_fuel(scan, 2);
    if j < c.ins.len() {
        let here = start_of(c.ins, j);
        let fs0 = forgotten(c, j, fs);
        let u = unit_at(c.ins, j, fs0)->Some_0;
        let rest = scan(c.ins, tg, j + u.len, u.facts)->Some_0;
        crate::a64::acc_lemmas::lemma_seq_has_concat(seq![here], rest, x);
        crate::a64::acc_lemmas::lemma_seq_has_single(here, x);
        if x != here {
            lemma_scan_chain_starts(c, j + u.len, u.facts, x);
            let t = choose|t: int|
                j + u.len <= t < c.ins.len() && x == start_of(c.ins, t) && chain_facts(
                    c,
                    j + u.len,
                    u.facts,
                    t,
                ) is Some;
            assert(chain_facts(c, j, fs, t) is Some);
        } else {
            assert(chain_facts(c, j, fs, j) is Some);
        }
    }
}

/// **Every entry and every jump target is a reached unit start.**
pub proof fn lemma_targets_are_starts(c: Cfg, x: int)
    requires
        cfg_ok(c),
        seq_has(all_targets(c.ins, c.entries), x),
    ensures
        exists|t: int|
            0 <= t < c.ins.len() && x == start_of(c.ins, t) && start_facts(c, t) is Some,
{
    let tg = all_targets(c.ins, c.entries);
    let starts = scan(c.ins, tg, 0, no_facts())->Some_0;
    lemma_cfg(c);
    assert(policy(c.ins, c.entries));
    crate::a64::acc_lemmas::lemma_subset_elim(tg, starts, x);
    lemma_scan_chain_starts(c, 0, no_facts(), x);
}

/// An entry is a target of the scan.
pub proof fn lemma_entry_in_targets(c: Cfg, e: int)
    requires
        seq_has(c.entries, e),
    ensures
        seq_has(all_targets(c.ins, c.entries), e),
{
    crate::a64::acc_lemmas::lemma_seq_has_concat(c.entries, jump_targets(c.ins, 0), e);
}

/// The jump targets of `ins[j'..]` include the target of the jump at `j`.
pub proof fn lemma_jump_target_from(ins: Seq<Instr>, j0: int, j: int, x: int)
    requires
        0 <= j0 <= j < ins.len(),
        jump_rel(ins[j]) is Some,
        x == start_of(ins, j) + jump_rel(ins[j])->Some_0,
    ensures
        seq_has(jump_targets(ins, j0), x),
    decreases j - j0,
{
    crate::a64::validate::lemma_jump_targets_step(ins, j0);
    let here: Seq<int> = match jump_rel(ins[j0]) {
        Some(r) => seq![start_of(ins, j0) + r],
        None => Seq::empty(),
    };
    if j0 == j {
        crate::a64::acc_lemmas::lemma_seq_has_concat(here, jump_targets(ins, j0 + 1), x);
        crate::a64::acc_lemmas::lemma_seq_has_single(x, x);
    } else {
        lemma_jump_target_from(ins, j0 + 1, j, x);
        crate::a64::acc_lemmas::lemma_seq_has_concat(here, jump_targets(ins, j0 + 1), x);
    }
}

/// **The target of every direct jump of the blob is a reached unit start**
/// (so it is where a unit begins, and what the scan knows there is nothing).
pub proof fn lemma_jump_target_is_start(c: Cfg, j: int)
    requires
        cfg_ok(c),
        0 <= j < c.ins.len(),
        jump_rel(c.ins[j]) is Some,
    ensures
        ({
            let x = start_of(c.ins, j) + jump_rel(c.ins[j])->Some_0;
            exists|t: int|
                0 <= t < c.ins.len() && x == start_of(c.ins, t) && start_facts(c, t) is Some
                    && start_facts(c, t)->Some_0 == no_facts()
        }),
{
    let x = start_of(c.ins, j) + jump_rel(c.ins[j])->Some_0;
    lemma_jump_target_from(c.ins, 0, j, x);
    crate::a64::acc_lemmas::lemma_seq_has_concat(c.entries, jump_targets(c.ins, 0), x);
    lemma_targets_are_starts(c, x);
    let t = choose|t: int|
        0 <= t < c.ins.len() && x == start_of(c.ins, t) && start_facts(c, t) is Some;
    // The facts at a target are `no_facts()`: forgotten.
    let f = start_facts(c, t)->Some_0;
    lemma_chain_append(c, 0, no_facts(), t, f, t);
    assert(seq_has(all_targets(c.ins, c.entries), start_of(c.ins, t)));
    assert(f == forgotten(c, t, f));
    assert(f == no_facts());
}

/// An entry is a unit start with no facts.
pub proof fn lemma_entry_is_start(c: Cfg, e: int)
    requires
        cfg_ok(c),
        seq_has(c.entries, e),
    ensures
        exists|t: int|
            0 <= t < c.ins.len() && e == start_of(c.ins, t) && start_facts(c, t) is Some
                && start_facts(c, t)->Some_0 == no_facts(),
{
    lemma_entry_in_targets(c, e);
    lemma_targets_are_starts(c, e);
    let t = choose|t: int|
        0 <= t < c.ins.len() && e == start_of(c.ins, t) && start_facts(c, t) is Some;
    let f = start_facts(c, t)->Some_0;
    lemma_chain_append(c, 0, no_facts(), t, f, t);
    assert(f == forgotten(c, t, f));
}

} // verus!
