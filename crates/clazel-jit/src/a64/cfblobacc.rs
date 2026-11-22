//! **J.9: the back end never produces a blob the validator refuses**, for A64
//! (jit.md item J.9): for every program with a translation, the blob the
//! control-flow back end emits ([`super::cfemit::emit_cf_blob`]: the
//! canonical encodings of [`ctmpl`] and the exit sequence) is accepted by the
//! validator's spec ([`clazel_codecheck::a64::spec::accepted`]), from the
//! entry the back end uses (byte 0): [`theorem_blob_accepted`]. The
//! counterpart of [`crate::cfblobacc`], whose header says how it is proven;
//! here the units are an exit sequence (3 instructions), a bounds-check
//! sequence (7) and single instructions, and a branch is relative to its own
//! address.

#[cfg(verus_only)]
use super::cfaccept::*;
#[cfg(verus_only)]
use super::cfbs::*;
#[cfg(verus_only)]
use super::cffit::labels_fit;
#[cfg(verus_only)]
use super::cfjt::*;
#[cfg(verus_only)]
use super::cflens::*;
#[cfg(verus_only)]
use super::cfproofs::lemma_csize_mod4;
#[cfg(verus_only)]
use super::cfsimple::nojump;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::cfuacc2::*;
#[cfg(verus_only)]
use super::cfunits::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The instructions the back end emits for the program `n` with `nl` locals
/// and the exit code `c` (the function's return label is at the end of the
/// body, where the exit sequence starts).
pub open spec fn emitted_ins(n: Node, nl: nat, c: u16) -> Seq<isa::Instr> {
    ctmpl(n, nl, 0, seq![csize(n, nl, 0, 1) as int]) + exit_seq(c)
}

/// A list of numbers is a subset of another if each is in it.
proof fn lemma_subset_intro(a: Seq<int>, b: Seq<int>)
    requires
        forall|x: int| clazel_codecheck::a64::spec::seq_has(a, x)
            ==> clazel_codecheck::a64::spec::seq_has(b, x),
    ensures
        clazel_codecheck::a64::spec::subset_of(a, b),
    decreases a.len(),
{
    if a.len() > 0 {
        let d = a.drop_last();
        assert(clazel_codecheck::a64::spec::seq_has(a, a.last()));
        assert forall|x: int| clazel_codecheck::a64::spec::seq_has(d, x)
            implies clazel_codecheck::a64::spec::seq_has(b, x) by {
            assert(clazel_codecheck::a64::spec::seq_has(a, x));
        }
        lemma_subset_intro(d, b);
    }
}

/// The scan's branch targets are the targets `jt` names.
proof fn lemma_jump_targets_has(ins: Seq<isa::Instr>, j: int, x: int)
    requires
        0 <= j,
    ensures
        clazel_codecheck::a64::spec::seq_has(clazel_codecheck::a64::spec::jump_targets(ins, j), x)
            == (exists|j2: int|
            j <= j2 < ins.len() && #[trigger] clazel_codecheck::a64::spec::jump_rel(ins[j2]) is Some
                && x == clazel_codecheck::a64::spec::start_of(ins, j2)
                + clazel_codecheck::a64::spec::jump_rel(ins[j2])->Some_0),
    decreases ins.len() - j,
{
    if j >= ins.len() {
        reveal_with_fuel(clazel_codecheck::a64::spec::seq_has, 1);
    } else {
        lemma_jump_targets_has(ins, j + 1, x);
        let rest = clazel_codecheck::a64::spec::jump_targets(ins, j + 1);
        match clazel_codecheck::a64::spec::jump_rel(ins[j]) {
            Some(r) => {
                let here = seq![clazel_codecheck::a64::spec::start_of(ins, j) + r];
                clazel_codecheck::a64::acc_lemmas::lemma_seq_has_concat(here, rest, x);
                clazel_codecheck::a64::acc_lemmas::lemma_seq_has_single(
                    clazel_codecheck::a64::spec::start_of(ins, j) + r,
                    x,
                );
                assert(clazel_codecheck::a64::spec::jump_targets(ins, j) =~= here + rest);
            },
            None => {
                assert(clazel_codecheck::a64::spec::jump_targets(ins, j) =~= rest);
            },
        }
    }
}

/// The targets of the whole blob.
proof fn lemma_targets_has(ins: Seq<isa::Instr>, x: int)
    ensures
        clazel_codecheck::a64::spec::seq_has(
            clazel_codecheck::a64::spec::all_targets(ins, seq![0int]),
            x,
        ) == (x == 0 || jt(ins, x)),
{
    lemma_jump_targets_has(ins, 0, x);
    clazel_codecheck::a64::acc_lemmas::lemma_seq_has_concat(
        seq![0int],
        clazel_codecheck::a64::spec::jump_targets(ins, 0),
        x,
    );
    clazel_codecheck::a64::acc_lemmas::lemma_seq_has_single(0, x);
}

/// **The validator accepts the instructions** the back end emits for a program
/// with a translation, from entry 0: the policy holds of them.
#[verifier::rlimit(1500)]
pub proof fn theorem_policy(n: Node, nl: nat, c: u16)
    requires
        cf_prog_ok(n, nl),
    ensures
        clazel_codecheck::a64::spec::policy(emitted_ins(n, nl, c), seq![0int]),
{
    let size = csize(n, nl, 0, 1);
    let offs = seq![size as int];
    assert(offs.len() == 1);
    let body = ctmpl(n, nl, 0, offs);
    let ins = body + exit_seq(c);
    lemma_csize_mod4(n, nl, 0, 1);
    assert(labels_fit(offs, size)) by {
        assert forall|l: int| 0 <= l < offs.len() implies #[trigger] offs[l] % 4 == 0 && -0x10_0000
            + size + 8 <= offs[l] && offs[l] <= 0xF_FFF0 by {
            assert(size <= max_size());
        }
    }
    // units
    let ut = utmpl(n, nl, 0, offs);
    let us = ut + seq![exit_seq(c)];
    lemma_utmpl_flat(n, nl, 0, offs);
    lemma_uflat_one(exit_seq(c));
    lemma_uflat_cat(ut, seq![exit_seq(c)]);
    assert(uflat(us) =~= ins);
    lemma_utmpl_uok(n, nl, 0, offs);
    lemma_exit_uok(c);
    assert(uok_all(seq![exit_seq(c)])) by {
        assert forall|k: int| 0 <= k < seq![exit_seq(c)].len() implies uok(
            #[trigger] seq![exit_seq(c)][k],
        ) by {
            assert(k == 0);
        }
    }
    lemma_uok_cat(ut, seq![exit_seq(c)]);
    // the branch targets
    let p = |x: int| x == 0 || jt(ins, x);
    assert forall|x: int| clazel_codecheck::a64::spec::seq_has(
        clazel_codecheck::a64::spec::all_targets(ins, seq![0int]),
        x,
    ) == p(x) by {
        lemma_targets_has(ins, x);
    }
    lemma_bs_facts(n, nl, 0, 1);
    lemma_bs_ubi(n, nl, 0, offs);
    lemma_jt_bs(n, nl, 0, offs);
    lemma_utmpl_blen(n, nl, 0, offs);
    // every branch target is a boundary of the body, and not protected
    assert forall|x: int| jt(ins, x) implies (bs(n, nl, 0, 1, x) && 0 <= x <= size) by {
        lemma_jt_cat(body, exit_seq(c), x);
        if jt(exit_seq(c), x - code_len(body)) {
            let e = exit_seq(c);
            assert(forall|j: int| 0 <= j < e.len() ==> nojump(#[trigger] e[j])) by {
                assert forall|j: int| 0 <= j < e.len() implies nojump(e[j]) by {
                    assert(j == 0 || j == 1 || j == 2);
                }
            }
            lemma_jt_none(e, x - code_len(body));
        }
        assert(jt(body, x));
        if inoffs(offs, x) {
            assert(x == size as int);
        }
    }
    // the scan
    let fs = clazel_codecheck::a64::spec::no_facts();
    assert(pf(n, nl, 0, 1, 0, p)) by {
        assert forall|x: int| #[trigger] prot(n, nl, 0, 1, x) implies !p(0 + x) by {
            assert(0 < x < size as int);
            if jt(ins, x) {
                assert(bs(n, nl, 0, 1, x));
            }
        }
    }
    lemma_utmpl_ucheck(n, nl, 0, offs, p);
    assert(ucheck(ut, 0, fs, p) is Some);
    let f = ucheck(ut, 0, fs, p)->Some_0;
    lemma_ucheck_cat(ut, seq![exit_seq(c)], 0, fs, p);
    super::cfuacc::lemma_ucheck_one(exit_seq(c), blen(ut) as int, f, p);
    assert(exit_seq(c).len() == 3);
    assert(ucheck(us, 0, fs, p) is Some);
    let tg = clazel_codecheck::a64::spec::all_targets(ins, seq![0int]);
    lemma_scan_units(ins, tg, 0, us, 0, fs, p);
    assert(clazel_codecheck::a64::spec::start_of(ins, 0) == 0);
    let starts = ustarts(us, 0);
    assert(clazel_codecheck::a64::spec::scan(ins, tg, 0, fs) == Some(starts));
    // the targets are unit starts
    lemma_blen_cat(ut, seq![exit_seq(c)]);
    lemma_blen_one(exit_seq(c));
    assert forall|x: int| clazel_codecheck::a64::spec::seq_has(tg, x)
        implies clazel_codecheck::a64::spec::seq_has(starts, x) by {
        lemma_seq_has_ustarts(us, 0, x);
        assert(p(x));
        if x == 0 {
            assert(us.len() > 0);
            assert(ub(us, 0, 0));
        } else {
            assert(jt(ins, x));
            assert(bs(n, nl, 0, 1, x));
            assert(ubi(ut, 0, 0 + x));
            lemma_ubi_cat(ut, seq![exit_seq(c)], 0, x);
            assert(x <= size as int);
            assert(blen(ut) == size);
            assert(x < blen(us));
            assert(ub(us, 0, x));
        }
    }
    lemma_subset_intro(tg, starts);
    assert(ins.last() is Ret) by {
        assert(ins[ins.len() - 1] == exit_seq(c)[2]);
    }
    assert(ins.len() > 0);
    assert(clazel_codecheck::a64::spec::policy(ins, seq![0int]));
}

/// **The validator accepts the blob**: any bytes that are the canonical
/// encodings of the instructions the back end emits are accepted, from entry
/// 0.
pub proof fn theorem_blob_accepted(n: Node, nl: nat, c: u16, bytes: Seq<u8>)
    requires
        cf_prog_ok(n, nl),
        clazel_codecheck::a64::spec::decodes_to(bytes, emitted_ins(n, nl, c)),
    ensures
        clazel_codecheck::a64::spec::accepted(bytes, seq![0int]),
{
    theorem_policy(n, nl, c);
}

/// **The emitter's blob is accepted** (`emit_cf_blob` carries this as its
/// own postcondition).
pub open spec fn emit_cf_blob_accepted_ensures(
    n: Node,
    nl: usize,
    exit_code: u16,
    r: Option<Seq<u8>>,
) -> bool {
    match r {
        Some(b) => clazel_codecheck::a64::spec::accepted(b, seq![0int]),
        None => true,
    }
}

/// From the emitter's two postconditions to the validator's acceptance.
pub proof fn lemma_emitter_accepted(n: Node, nl: usize, exit_code: u16, bytes: Seq<u8>)
    requires
        super::cfcontract::emit_cf_blob_ensures(n, nl, exit_code, Some(bytes)),
        clazel_codecheck::a64::spec::decodes_to(bytes, emitted_ins(n, nl as nat, exit_code)),
    ensures
        emit_cf_blob_accepted_ensures(n, nl, exit_code, Some(bytes)),
{
    theorem_blob_accepted(n, nl as nat, exit_code, bytes);
}

} // verus!
