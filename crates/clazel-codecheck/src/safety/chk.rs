//! The bounds-check sequence ([`check_instr`]) run one instruction at a time:
//! what is true of the machine after each of its eight instructions, so that
//! falling through all eight leaves the index register `i` with `i + n <=
//! bound(k)` ([`Fact::Idx`]), and the two conditional jumps are taken only to
//! places the validator checked ([`super::spec::policy`]).
//!
//! [`chk_mid`] is the invariant after `m` instructions of the sequence.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// 2^64.
pub open spec fn two64() -> int {
    0x1_0000_0000_0000_0000
}

/// The facts of `fs` hold for every register but the scratch `t` and `z`.
pub open spec fn holds_except(s: State, h: Handed, fs: Facts, t: u8, z: u8) -> bool {
    forall|r: u8|
        r < 16 && r != t && r != z ==> fact_holds(s, h, r, #[trigger] fact_of(fs, r))
}

/// **The invariant after `m` instructions of the bounds-check sequence** `c`
/// (`0 <= m <= 7`), starting from facts `fs0`:
///
/// - `m = 1`: `t = i`;
/// - `m = 2`: `t = (i + n) mod 2^64`, and the carry flag says it wrapped;
/// - `m = 3`: it did not wrap: `t = i + n`;
/// - `m = 4`: the carry and zero flags compare `t` with the bound;
/// - `m = 5, 6`: `i + n <= bound`;
/// - `m = 7`: the same, and the carry flag says `i < bound`.
pub open spec fn chk_mid(s: State, h: Handed, c: Chk, fs0: Facts, m: int) -> bool {
    let iv = s.rgf[c.i as int] as int;
    let tv = s.rgf[c.t as int] as int;
    let bound = h.rg[c.k].bound;
    &&& holds_except(s, h, fs0, c.t, c.z)
    &&& (m == 1 ==> tv == iv)
    &&& (m == 2 ==> tv == (iv + c.n) % two64() && flgi(s, cf_bit()) == if iv + c.n >= two64() {
        1int
    } else {
        0int
    })
    &&& (m == 3 ==> tv == iv + c.n)
    &&& (m == 4 ==> tv == iv + c.n && flgi(s, cf_bit()) == (if tv < bound {
        1int
    } else {
        0int
    }) && flgi(s, zf_bit()) == (if tv == bound {
        1int
    } else {
        0int
    }))
    &&& ((m == 5 || m == 6) ==> iv + c.n <= bound)
    &&& (m == 7 ==> iv + c.n <= bound && flgi(s, cf_bit()) == 1)
}

/// What is known after the whole sequence, from `fs0`.
pub open spec fn chk_facts(fs0: Facts, c: Chk) -> Facts {
    set_fact(
        set_fact(set_fact(fs0, c.t, Fact::Unknown), c.z, Fact::Unknown),
        c.i,
        Fact::Idx(c.k, c.n),
    )
}

/// The check's parameters are in range as the machine sees them.
pub open spec fn chk_ok(h: Handed, c: Chk) -> bool {
    check_ok(c) && c.n < 0x8000_0000 && 1 <= c.n && 0 <= c.k < 16 && c.t < 16 && c.i < 16 && c.z < 16
}

/// The instruction is a conditional jump whose condition holds in `s`.
pub open spec fn jumps(s: State, i: Instr) -> bool {
    i is Jcc && jcc_cmovcc_setcc_spec(s, i->Jcc_cc)
}

/// What the step of instruction `m` of the sequence gives, relative to the
/// sequence's own unit-level invariants. (The conclusion of
/// [`lemma_chk_step`].)
pub open spec fn chk_step_post(
    h: Handed,
    blob: Seq<u8>,
    c: Chk,
    fs0: Facts,
    m: int,
    s: State,
    s2: State,
    i: Instr,
) -> bool {
    &&& ctx_inv(s2, h, blob)
    &&& step_safe(h, s, i, s2)
    &&& s2.rgf.len() == 16
    &&& (!jumps(s, i) ==> s2.rip == s.rip + instr_len(i) && if m < 7 {
        chk_mid(s2, h, c, fs0, m + 1)
    } else {
        holds(s2, h, chk_facts(fs0, c))
    })
    &&& (jumps(s, i) ==> s2.rip == s.rip + instr_len(i) + i->Jcc_rel)
}

/// No scratch register is reserved or the other: a write to `t` or `z` or `i`
/// does not touch `r15` and `rsp`.
proof fn lemma_chk_kept(c: Chk, s: State, s2: State, d: u8)
    requires
        check_ok(c),
        d == c.t || d == c.z || d == c.i,
        gpr_kept(s, s2, Some(d)),
        s.rgf.len() == 16,
    ensures
        s2.rgf[15] == s.rgf[15],
        s2.rgf[4] == s.rgf[4],
{
    assert(d != 15 && d != 4);
}

/// `holds_except` survives a step that writes only `t` or `z`.
proof fn lemma_hx_kept(c: Chk, s: State, s2: State, h: Handed, fs0: Facts, d: u8)
    requires
        holds_except(s, h, fs0, c.t, c.z),
        d == c.t || d == c.z,
        gpr_kept(s, s2, Some(d)),
        s.rgf.len() == 16,
    ensures
        holds_except(s2, h, fs0, c.t, c.z),
{
    assert forall|r: u8| r < 16 && r != c.t && r != c.z implies fact_holds(
        s2,
        h,
        r,
        #[trigger] fact_of(fs0, r),
    ) by {
        assert(fact_holds(s, h, r, fact_of(fs0, r)));
    }
}

/// The bound of region `k` is read from the context.
proof fn lemma_bound_read(h: Handed, blob: Seq<u8>, s: State, k: int)
    requires
        handed_ok(h),
        ctx_inv(s, h, blob),
        0 <= k < 16,
    ensures
        read_operand_mem(s, Size::W64, bound_mem(k)) == Some(h.rg[k].bound),
        0 <= h.rg[k].bound < two64(),
        mem_ok(bound_mem(k)),
        access_ok(no_facts(), Access { mem: bound_mem(k), size: 8, store: false }),
{
    lemma_p2_vals();
    assert(region_ok(h, h.rg[k]));
    assert(rr64(s, 15) == h.ctx);
    let x = h.ctx + abi::bound_off(k);
    assert(0 <= x < 0x8000_0000_0000_0000);
    lemma_logext_small(x);
    assert(eff_addr(s, bound_mem(k)) == x);
    assert(bound_mem(k).disp as int == abi::bound_off(k));
}

/// **One instruction of the bounds-check sequence**, entered at a state
/// satisfying [`chk_mid`] for `m`.
#[verifier::rlimit(400)]
pub proof fn lemma_chk_step(
    u: spec_fn(nat) -> nat,
    h: Handed,
    blob: Seq<u8>,
    c: Chk,
    fs0: Facts,
    m: int,
    s: State,
    s2: State,
    i: Instr,
)
    requires
        handed_ok(h),
        ctx_inv(s, h, blob),
        chk_ok(h, c),
        0 <= m < 8,
        i == check_instr(m, c),
        chk_mid(s, h, c, fs0, m),
        step(u, s, i) == Some(s2),
    ensures
        chk_step_post(h, blob, c, fs0, m, s, s2, i),
{
    lemma_p2_vals();
    assert(valid_instr(i));
    assert(s.rgf.len() == 16);
    lemma_step_frame(u, s, i, s2);
    lemma_bound_read(h, blob, s, c.k);
    lemma_no_facts_hold(s, h);
    assert(region_ok(h, h.rg[c.k]));
    let iv = s.rgf[c.i as int] as int;
    let tv = s.rgf[c.t as int] as int;
    let bound = h.rg[c.k].bound;
    assert(0 <= iv < two64() && 0 <= tv < two64());
    if m == 0 {
        // mov t, i
        lemma_set_rgfi(s, Size::W64, c.t, rr64(s, c.i));
        lemma_chk_kept(c, s, s2, c.t);
        lemma_ctx_inv_preserved(h, blob, s, s2, i);
        lemma_hx_kept(c, s, s2, h, fs0, c.t);
        assert(s2.rgf[c.t as int] as int == iv);
        assert(s2.rgf[c.i as int] == s.rgf[c.i as int]);
    } else if m == 1 {
        // add t, n
        lemma_step_add(u, s, s2, c.t, c.n as i32);
        lemma_chk_kept(c, s, s2, c.t);
        lemma_ctx_inv_preserved(h, blob, s, s2, i);
        lemma_hx_kept(c, s, s2, h, fs0, c.t);
        assert(s2.rgf[c.i as int] == s.rgf[c.i as int]);
    } else if m == 2 || m == 4 {
        // jb / ja: no register, memory or flag change
        assert(s2.rgf == s.rgf && s2.mem == s.mem && s2.rflags == s.rflags);
        lemma_ctx_inv_preserved(h, blob, s, s2, i);
        assert forall|r: u8| r < 16 && r != c.t && r != c.z implies fact_holds(
            s2,
            h,
            r,
            #[trigger] fact_of(fs0, r),
        ) by {
            assert(fact_holds(s, h, r, fact_of(fs0, r)));
        }
        assert(step_safe(h, s, i, s2));
        if m == 2 {
            assert(jcc_cmovcc_setcc_spec(s, 2) == (flgi(s, cf_bit()) == 1));
        } else {
            assert(jcc_cmovcc_setcc_spec(s, 7) == (flgi(s, cf_bit()) == 0 && flgi(s, zf_bit())
                == 0));
        }
    } else if m == 3 || m == 6 {
        // cmp t, [bound]  /  cmp i, [bound]
        let r = if m == 3 {
            c.t
        } else {
            c.i
        };
        lemma_step_cmp(u, s, s2, r, bound_mem(c.k), bound);
        lemma_access_allowed(
            s,
            h,
            no_facts(),
            Access { mem: bound_mem(c.k), size: 8, store: false },
        );
        lemma_ctx_inv_preserved(h, blob, s, s2, i);
        assert forall|q: u8| q < 16 && q != c.t && q != c.z implies fact_holds(
            s2,
            h,
            q,
            #[trigger] fact_of(fs0, q),
        ) by {
            assert(fact_holds(s, h, q, fact_of(fs0, q)));
        }
        assert(step_safe(h, s, i, s2));
    } else if m == 5 {
        // mov z, 0
        lemma_wr64(s, c.z, 0);
        lemma_chk_kept(c, s, s2, c.z);
        lemma_ctx_inv_preserved(h, blob, s, s2, i);
        lemma_hx_kept(c, s, s2, h, fs0, c.z);
        assert(s2.rgf[c.i as int] == s.rgf[c.i as int]);
    } else {
        // cmovae i, z: not taken, the carry flag is set
        assert(jcc_cmovcc_setcc_spec(s, 3) == (flgi(s, cf_bit()) == 0));
        assert(s2.rgf == s.rgf && s2.mem == s.mem);
        lemma_ctx_inv_preserved(h, blob, s, s2, i);
        assert(step_safe(h, s, i, s2));
        assert forall|r: u8| r < 16 implies fact_holds(
            s2,
            h,
            r,
            #[trigger] fact_of(chk_facts(fs0, c), r),
        ) by {
            lemma_fact_of_set(
                set_fact(set_fact(fs0, c.t, Fact::Unknown), c.z, Fact::Unknown),
                c.i,
                Fact::Idx(c.k, c.n),
                r,
            );
            lemma_fact_of_set(set_fact(fs0, c.t, Fact::Unknown), c.z, Fact::Unknown, r);
            lemma_fact_of_set(fs0, c.t, Fact::Unknown, r);
            if r != c.t && r != c.z && r != c.i {
                assert(fact_holds(s, h, r, fact_of(fs0, r)));
            }
        }
    }
}

} // verus!
