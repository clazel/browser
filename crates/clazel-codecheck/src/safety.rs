//! **The safety theorem of the x86-64 validator** (jit.md exit criterion 2),
//! *statement only*: what an execution of an accepted blob may do, over
//! `clazel_x64::spec::step`. The proof is later work (CLAUDE.md rule 3: the
//! statement is committed first, and it is the part humans review).
//!
//! # The theorem, in words
//!
//! Let `ins` be a decoding of an accepted blob placed at address `code`, and
//! let a machine start at an accepted entry `e` (so `rip = code + e`) in a
//! state that satisfies the **context invariant** ([`start_ok`]) for what
//! the host handed over ([`Handed`], [`handed_ok`]). Take any finite
//! execution prefix: states `st[0..=n]` and instructions `ex[0..n]` with
//! `fetch_ok` and `step(st[k], ex[k]) == Some(st[k+1])` ([`run_ok`]). Then
//! for every step `k` reached without an earlier `ret` ([`safe_execution`]):
//!
//! 1. **Decoded subset instruction.** `rip` is the byte offset of
//!    instruction `j` of the blob, and `ex[k] == ins[j]`: only decoded,
//!    canonically encoded subset instructions run, and the subset has no
//!    system instruction.
//! 2. **Memory.** If `ex[k]` accesses memory ([`mem_access`]), the bytes
//!    touched, which are `eff_addr(st[k], mem) .. + size` in `step`'s own
//!    address computation, lie in one of the handed regions or in the
//!    context; a store lies in a handed region or the context's exit area.
//!    (`ret` also reads `[rsp]`; see 4.)
//! 3. **Reserved registers.** `r15` is the same after the step, and so is
//!    `rsp`, except by a `ret`.
//! 4. **Leaving.** If `ex[k]` is `ret`, it is the `ret` of an exit sequence
//!    of the blob ([`exit_unit_at`]), at its offset: control leaves only
//!    there. Every other step is followed by a step again inside the blob
//!    (item 1 for `k + 1`), so control never runs past the end.
//!
//! # How memory and control flow are observed
//!
//! `step` does not report the addresses it touches, and none is added to
//! `clazel-x64`: an access is observed as [`mem_access`] (the instruction's
//! operand and size) evaluated at the *pre-state* with `eff_addr`, which is
//! the very function `read_operand_mem`, `read_xmm_src` and `store_mem` use.
//! Control flow is observed as `rip` of the pre-state. The execution model is
//! flat: `fetch_ok` says which bytes at `rip` are the instruction executed.
//!
//! # Modelling choices
//!
//! - **What the host hands over** ([`handed_ok`]). The theorem needs the
//!   handed regions to be addresses the code must not be able to write
//!   through a region: not the context's region table (or the table would
//!   not stay what the invariant says), and not the code (immutable, J.8);
//!   and the code and
//!   the context block do not overlap. Regions may overlap each other and
//!   the exit area. Where the return address is, and where `ret` goes, is
//!   not constrained: the theorem stops at the `ret`. All addresses are
//!   below 2^63 so that `eff_addr`'s wrap-around never occurs.
//! - **Faults are not violations.** `step` returns `None` on an unmapped
//!   access; the theorem is about the steps that do happen.
//! - **The execution prefix stops at the first `ret`.** What is after the
//!   exit sequence's `ret` is the enter stub's (`clazel-sys`, J.7), outside
//!   this theorem; `ret` is the one step allowed to write `rsp`, the fixed
//!   epilogue of jit.md's "except in the fixed prologue and epilogue".
//! - **No termination claim**: a prefix may be of any length, a loop may go
//!   on for ever (see [`super::spec`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A handed region: `bound` bytes at address `base`.
pub struct Region {
    /// The address of the first byte.
    pub base: int,
    /// The size in bytes.
    pub bound: int,
}

/// What the host fixed before the code runs: where the code is and how long,
/// the context address, the address of the return-address slot (`rsp`), and
/// the 16 regions of the context's table.
pub struct Handed {
    /// The address the blob is placed at.
    pub code: int,
    /// The length of the blob in bytes.
    pub len: int,
    /// The address of the context (`r15`).
    pub ctx: int,
    /// The value of `rsp` at entry: the return address is at `[sp, sp+8)`.
    pub sp: int,
    /// The regions, `rg[k]` being what the table says for region `k`.
    pub rg: Seq<Region>,
}

/// The bytes `[a, a+n)` lie in `[lo, lo+len)`.
pub open spec fn within(a: int, n: int, lo: int, len: int) -> bool {
    lo <= a && a + n <= lo + len
}

/// `[lo1, lo1+len1)` and `[lo2, lo2+len2)` share no byte.
pub open spec fn disjoint(lo1: int, len1: int, lo2: int, len2: int) -> bool {
    lo1 + len1 <= lo2 || lo2 + len2 <= lo1
}

/// 2^63: addresses below it are the ones `eff_addr` leaves alone.
pub open spec fn addr_limit() -> int {
    0x8000_0000_0000_0000
}

/// Region `r` is a legitimate handout: it does not wrap, and it shares no
/// byte with the region table or the code.
pub open spec fn region_ok(h: Handed, r: Region) -> bool {
    &&& 0 <= r.base
    &&& 0 <= r.bound
    &&& r.base + r.bound <= addr_limit()
    &&& disjoint(r.base, r.bound, h.ctx, abi::table_end())
    &&& disjoint(r.base, r.bound, h.code, h.len)
}

/// The host's side of the bargain: sixteen regions, all legitimate; the
/// blob and the context are below 2^63, and the code and the context block
/// do not overlap.
pub open spec fn handed_ok(h: Handed) -> bool {
    &&& h.rg.len() == abi::num_regions()
    &&& (forall|k: int| 0 <= k < 16 ==> region_ok(h, #[trigger] h.rg[k]))
    &&& 0 <= h.code && 0 < h.len && h.code + h.len <= addr_limit()
    &&& 0 <= h.ctx && h.ctx + abi::ctx_size() <= addr_limit()
    &&& disjoint(h.code, h.len, h.ctx, abi::ctx_size())
}

/// **The context invariant**: `r15` is the context address, `rsp` is the
/// slot, and the context's table reads, as 8-byte little-endian loads,
/// `rg[k].base` at `16k` and `rg[k].bound` at `16k + 8` (so it is mapped);
/// the blob's bytes are at `code`.
pub open spec fn ctx_inv(s: State, h: Handed, blob: Seq<u8>) -> bool {
    &&& s.rgf.len() == 16
    &&& s.rgf[abi::ctx_reg() as int] as int == h.ctx
    &&& s.rgf[abi::sp_reg() as int] as int == h.sp
    &&& (forall|k: int|
        0 <= k < 16 ==> read_mem(s.mem, h.ctx + abi::base_off(k), 8) == Some(
            (#[trigger] h.rg[k]).base,
        ) && read_mem(s.mem, h.ctx + abi::bound_off(k), 8) == Some(h.rg[k].bound))
    &&& blob.len() == h.len
    &&& (forall|i: int|
        0 <= i < h.len ==> s.mem.dom().contains(#[trigger] (h.code + i)) && s.mem[h.code + i]
            == blob[i])
}

/// The start state: [`ctx_inv`], and `rip` at the entry `e` of the blob.
pub open spec fn start_ok(s: State, h: Handed, blob: Seq<u8>, e: int) -> bool {
    ctx_inv(s, h, blob) && s.rip == h.code + e
}

/// The access of `a` at address `addr` is one the context or the handed
/// regions allow: a load in the context or a region, a store in the exit
/// area or a region.
pub open spec fn access_allowed(h: Handed, addr: int, a: Access) -> bool {
    (if a.store {
        within(addr, a.size, h.ctx + abi::exit_code_off(), abi::ctx_size() - abi::table_end())
    } else {
        within(addr, a.size, h.ctx, abi::ctx_size())
    }) || exists|k: int|
        0 <= k < 16 && within(addr, a.size, (#[trigger] h.rg[k]).base, h.rg[k].bound)
}

/// The step `s -> s2` by `i` is safe: its memory access (observed as
/// `mem_access` at `eff_addr` of the pre-state) is allowed, `r15` is kept,
/// and `rsp` is kept unless `i` is `ret`.
pub open spec fn step_safe(h: Handed, s: State, i: Instr, s2: State) -> bool {
    &&& (mem_access(i) matches Some(a) ==> access_allowed(h, eff_addr(s, a.mem), a))
    &&& s2.rgf[abi::ctx_reg() as int] == s.rgf[abi::ctx_reg() as int]
    &&& (!(i is Ret) ==> s2.rgf[abi::sp_reg() as int] == s.rgf[abi::sp_reg() as int])
}

/// `st`, `ex` is a finite execution prefix: `n` instructions, each fetched
/// from the bytes at `rip` and stepped by `step` (for any `create_undef`).
pub open spec fn run_ok(
    create_undef: spec_fn(nat) -> nat,
    st: Seq<State>,
    ex: Seq<Instr>,
) -> bool {
    st.len() == ex.len() + 1 && forall|k: int|
        0 <= k < ex.len() ==> fetch_ok(st[k], #[trigger] ex[k]) && step(
            create_undef,
            st[k],
            ex[k],
        ) == Some(st[k + 1])
}

/// What is claimed of step `k` of a run of the blob decoded as `ins`.
pub open spec fn step_claim(
    h: Handed,
    ins: Seq<Instr>,
    st: Seq<State>,
    ex: Seq<Instr>,
    k: int,
) -> bool {
    &&& exists|j: int|
        0 <= j < ins.len() && st[k].rip == h.code + start_of(ins, j) && ex[k] == ins[j]
    &&& step_safe(h, st[k], ex[k], st[k + 1])
    &&& (ex[k] is Ret ==> exists|j: int|
        exit_unit_at(ins, j) && st[k].rip == h.code + start_of(ins, j + 2))
    &&& (!(ex[k] is Ret) ==> exists|j: int|
        0 <= j < ins.len() && st[k + 1].rip == h.code + start_of(ins, j))
}

/// **The theorem's conclusion**: every step reached before any `ret` has
/// [`step_claim`].
pub open spec fn safe_execution(
    h: Handed,
    ins: Seq<Instr>,
    st: Seq<State>,
    ex: Seq<Instr>,
) -> bool {
    forall|k: int|
        0 <= k < ex.len() && (forall|j: int| 0 <= j < k ==> !((#[trigger] ex[j]) is Ret))
            ==> step_claim(h, ins, st, ex, k)
}

/// **The safety theorem** (jit.md exit criterion 2, x86-64): an accepted
/// blob, placed and entered as [`start_ok`] says, only does what
/// [`safe_execution`] says, over every execution prefix. *Not yet proven*:
/// the lemma that this holds follows in a later commit.
pub open spec fn safety_statement(
    create_undef: spec_fn(nat) -> nat,
    blob: Seq<u8>,
    entries: Seq<int>,
    ins: Seq<Instr>,
    h: Handed,
    e: int,
    st: Seq<State>,
    ex: Seq<Instr>,
) -> bool {
    (decodes_to(blob, ins) && policy(ins, entries) && entries.contains(e) && handed_ok(h)
        && st.len() > 0 && start_ok(st[0], h, blob, e) && run_ok(create_undef, st, ex))
        ==> safe_execution(h, ins, st, ex)
}

} // verus!
