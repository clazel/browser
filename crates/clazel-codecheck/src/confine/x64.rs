//! **The x86-64 machine** of the confinement theorem
//! ([`super::machine::confinement`]): the configuration, the machine-level
//! invariant, and the observations, over `clazel_x64::spec`'s `State` and
//! `step`. This file is *statement only*: definitions and the
//! [`super::machine::Machine`] instance. The proof is in `super::x64proof`
//! (CLAUDE.md rule 3: the statement is committed before it).
//!
//! # The configuration ([`Cfg`])
//!
//! What the sandbox hands over, as numbers: the blob and the instruction list
//! it decodes to, the entries; the address of the blob's first byte (`code`),
//! of the context (`ctx`, 512 bytes, jit.md J.0 and [`crate::spec::abi`]); the
//! 16 regions' bases and bounds (as in the context's table); and the stack
//! slot of the enter stub (`sp`, the address `rsp` holds on entry, and
//! `ret_raw`, the return address the stub put there).
//! [`cfg_ok`] says it is a configuration the sandbox may hand over: the blob
//! is accepted, everything lies in the positive canonical addresses
//! (`0 <= a < 2^47`, so that no address computation wraps), and **the code,
//! the context's table, the stack slot and each region are pairwise
//! disjoint** (a region may overlap another region and the exit area, which
//! is harmless; the stack slot may overlap neither, or a store could change
//! where `ret` goes). These are obligations of the enter stub and the
//! sandbox (J.7, J.8), not of the validator.
//!
//! # The machine-level invariant ([`inv`])
//!
//! Before an instruction ([`pos_inv`], at unit `j0`, `m` instructions into
//! it):
//!
//! - **the state is well formed** (`clazel_x64::spec::wf`);
//! - **the context register `r15` holds the context** and **`rsp` holds the
//!   stub's stack pointer**;
//! - **the region table is intact**: the 16 base/bound words in memory are
//!   the configuration's;
//! - **the code is intact**: the blob's bytes are in memory at `code`;
//! - **the stub's return address is intact** at `[sp, sp + 8)`;
//! - **RIP is at the start of instruction `j0 + m`**, where `j0` is a *unit
//!   start* of the blob: a position the validator's scan reaches by taking
//!   units from 0 ([`start_facts`]);
//! - **the facts the scan tracks hold** ([`facts_hold`]): at a unit start
//!   (`m == 0`) those the scan has there, after forgetting at targets; inside
//!   an exit or bounds-check sequence (`m > 0`), the corresponding
//!   intermediate facts ([`mid_inv`]).
//!
//! Where the theorem is applied, the invariant holds on entry: see
//! `super::x64proof::lemma_entry_inv`.
//!
//! # Modelling choices
//!
//! - **The accesses are [`mem_access`]'s**, the validator's own account of
//!   what an instruction touches ([`loads_ok`], [`stores_ok`]); the proof
//!   ties it to the semantics: a write changes memory only inside the access
//!   it names ([`writes_confined`]), and a step's outcome depends only on the
//!   bytes of the read area ([`reads_confined`]).
//! - **`ret` reads the stack**: `[rsp, rsp + 8)`, the stub's slot. It is the
//!   only instruction of an accepted blob that touches anything but the
//!   context and the regions, and it is accepted only in the exit sequence.
//!   [`mem_access`] has no entry for it; the invariant says `rsp = sp` and
//!   the slot holds `ret_raw`, so the step returns to `logext(64, ret_raw)`.
//!   [`reads_confined`] counts the slot as readable.
//! - **The next instruction is found by offset**: [`next_instr`] looks RIP's
//!   offset up among the instruction starts; [`inv`] has RIP at one.
//! - **No system instruction**: [`is_system`] is false for every
//!   [`Instr`]; the match is spelled out so that a new variant forces a
//!   decision.

#[allow(unused_imports)]
use super::machine::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The x86-64 machine: the marker the [`Machine`] instance is for.
pub struct X64;

/// What the sandbox hands over (see the module documentation).
pub struct Cfg {
    /// The blob.
    pub blob: Seq<u8>,
    /// The instructions it decodes to.
    pub ins: Seq<Instr>,
    /// The entries, as byte offsets.
    pub entries: Seq<int>,
    /// The address of the blob's first byte.
    pub code: int,
    /// The address of the 512-byte context.
    pub ctx: int,
    /// The base address of each of the 16 regions.
    pub bases: Seq<int>,
    /// The bound (size in bytes) of each of the 16 regions.
    pub bounds: Seq<int>,
    /// The value of `rsp` on entry: the address of the stub's return slot.
    pub sp: int,
    /// The 64-bit word the stub left in the return slot.
    pub ret_raw: int,
}

/// The first address that is not in the positive canonical range: `2^47`.
pub open spec fn lim() -> int {
    140737488355328
}

/// The byte ranges `[a, a + la)` and `[b, b + lb)` do not overlap.
pub open spec fn disjoint(a: int, la: int, b: int, lb: int) -> bool {
    a + la <= b || b + lb <= a
}

/// Region `k` is well placed: positive canonical addresses, and disjoint from
/// the code, the context's table and the stub's slot.
pub open spec fn region_ok(c: Cfg, k: int) -> bool {
    0 <= c.bases[k] && 0 <= c.bounds[k] && c.bases[k] + c.bounds[k] <= lim() && disjoint(
        c.bases[k],
        c.bounds[k],
        c.code,
        c.blob.len() as int,
    ) && disjoint(c.bases[k], c.bounds[k], c.ctx, abi::table_end()) && disjoint(
        c.bases[k],
        c.bounds[k],
        c.sp,
        8,
    )
}

/// **A configuration the sandbox may hand over**: the blob is accepted (the
/// instruction list `ins` is its decoding and passes the policy at the
/// entries), and the layout is as the module documentation says.
pub open spec fn cfg_ok(c: Cfg) -> bool {
    decodes_to(c.blob, c.ins) && policy(c.ins, c.entries) && c.bases.len() == abi::num_regions()
        && c.bounds.len() == abi::num_regions() && 0 <= c.code && c.code + c.blob.len() <= lim()
        && 0 <= c.ctx && c.ctx + abi::ctx_size() <= lim() && disjoint(
        c.code,
        c.blob.len() as int,
        c.ctx,
        abi::ctx_size(),
    ) && (forall|k: int| 0 <= k < abi::num_regions() ==> #[trigger] region_ok(c, k)) && 0 <= c.sp
        && c.sp + 8 <= lim() && disjoint(c.sp, 8, c.code, c.blob.len() as int) && disjoint(
        c.sp,
        8,
        c.ctx,
        abi::ctx_size(),
    ) && 0 <= c.ret_raw && c.ret_raw < p2(64) && disjoint(
        logext(64, c.ret_raw),
        1,
        c.code,
        c.blob.len() as int,
    )
}

// ----------------------------------------------------------------------------
// Section: what holds in the registers
// ----------------------------------------------------------------------------

/// The scan's facts `fs` hold in `s`: a register known to hold region `k`'s
/// base does, and a register known to be checked for `n` bytes of region `k`
/// holds an `i` with `i + n <= bound(k)`.
pub open spec fn facts_hold(c: Cfg, s: State, fs: Facts) -> bool {
    forall|r: u8|
        r < 16 ==> match #[trigger] fact_of(fs, r) {
            Fact::Unknown => true,
            Fact::Base(k) => 0 <= k < abi::num_regions() && rr64(s, r) == c.bases[k],
            Fact::Idx(k, n) => 0 <= k < abi::num_regions() && 0 <= n && rr64(s, r) + n
                <= c.bounds[k],
        }
}

/// What the scan forgets at instruction `j`: everything, if its offset is a
/// target or an entry, else nothing.
pub open spec fn forgotten(c: Cfg, j: int, fs: Facts) -> Facts {
    if seq_has(all_targets(c.ins, c.entries), start_of(c.ins, j)) {
        no_facts()
    } else {
        fs
    }
}

/// The facts the scan has on reaching the unit that starts at instruction
/// `t`, after forgetting there, if the scan starting at unit `j` with `fs`
/// reaches `t` as a unit start; `None` if it does not.
pub open spec fn chain_facts(c: Cfg, j: int, fs: Facts, t: int) -> Option<Facts>
    decreases t - j,
{
    let fs0 = forgotten(c, j, fs);
    if j == t {
        Some(fs0)
    } else if j > t || j < 0 || j >= c.ins.len() {
        None
    } else {
        match unit_at(c.ins, j, fs0) {
            None => None,
            Some(u) => if u.len >= 1 && j + u.len <= t {
                chain_facts(c, j + u.len, u.facts, t)
            } else {
                None
            },
        }
    }
}

/// The facts at unit start `t`: the scan from the first instruction.
pub open spec fn start_facts(c: Cfg, t: int) -> Option<Facts> {
    chain_facts(c, 0, no_facts(), t)
}

// ----------------------------------------------------------------------------
// Section: the invariant inside the validator's sequences
// ----------------------------------------------------------------------------

/// What is known after `mov t, code` of an exit sequence starting at
/// instruction `j0`: `t` is overwritten.
pub open spec fn exit_mid_facts(ins: Seq<Instr>, j0: int, fs0: Facts) -> Facts {
    match ins[j0] {
        Instr::MovImm32 { dst, .. } => set_fact(fs0, dst, Fact::Unknown),
        _ => fs0,
    }
}

/// The facts that hold throughout a bounds check `ch`: all of `fs0` except
/// for the three registers it writes.
pub open spec fn check_mid_facts(fs0: Facts, ch: Chk) -> Facts {
    set_fact(set_fact(set_fact(fs0, ch.t, Fact::Unknown), ch.z, Fact::Unknown), ch.i, Fact::Unknown)
}

/// The invariant before instruction `m` (1 to 7) of the bounds check `ch`,
/// whose region's bound is `bound` and which began with `fs0` (the
/// instructions are numbered as in [`check_instr`]). With `I` the index
/// register's value and `n` the size, `T` the scratch's:
///
/// - 1: `T = I`;
/// - 2: `T = (I + n) mod 2^64` and `CF` is set exactly when `I + n >= 2^64`;
/// - 3: `jb` fell through, so `I + n < 2^64` and `T = I + n`;
/// - 4: `cmp` has set `CF` for `T < bound` and `ZF` for `T = bound`;
/// - 5: `ja` fell through, so `I + n <= bound`;
/// - 6: the same, and `z = 0`;
/// - 7: the same, and `CF` is set exactly when `I < bound`.
pub open spec fn check_mid(c: Cfg, s: State, ch: Chk, fs0: Facts, m: int) -> bool {
    0 <= ch.k < abi::num_regions() && facts_hold(c, s, check_mid_facts(fs0, ch)) && {
        let i = rr64(s, ch.i);
        let t = rr64(s, ch.t);
        let n = ch.n;
        let b = c.bounds[ch.k];
        if m == 1 {
            t == i
        } else if m == 2 {
            t == (i + n) % p2(64) && flgi(s, cf_bit()) == (if i + n >= p2(64) {
                1int
            } else {
                0int
            })
        } else if m == 3 {
            i + n < p2(64) && t == i + n
        } else if m == 4 {
            t == i + n && flgi(s, cf_bit()) == (if t < b {
                1int
            } else {
                0int
            }) && flgi(s, zf_bit()) == (if t == b {
                1int
            } else {
                0int
            })
        } else if m == 5 {
            i + n <= b
        } else if m == 6 {
            i + n <= b && rr64(s, ch.z) == 0
        } else if m == 7 {
            i + n <= b && rr64(s, ch.z) == 0 && flgi(s, cf_bit()) == (if i < b {
                1int
            } else {
                0int
            })
        } else {
            false
        }
    }
}

/// The invariant on the registers, `m` instructions into the unit that starts
/// at instruction `j0` with facts `fs0`.
pub open spec fn mid_inv(c: Cfg, s: State, j0: int, fs0: Facts, m: int) -> bool {
    if m == 0 {
        facts_hold(c, s, fs0)
    } else if exit_unit_at(c.ins, j0) {
        facts_hold(c, s, exit_mid_facts(c.ins, j0, fs0))
    } else {
        check_unit_at(c.ins, j0) && check_mid(c, s, check_params(c.ins, j0)->Some_0, fs0, m)
    }
}

// ----------------------------------------------------------------------------
// Section: the machine-level invariant
// ----------------------------------------------------------------------------

/// The part of the invariant that does not depend on where in the blob the
/// state is (and that `ret`-free code never disturbs): the state is well
/// formed, `r15` is the context, `rsp` is the stub's stack pointer, and the
/// region table, the code and the stub's return slot are intact in memory.
pub open spec fn base_inv(c: Cfg, s: State) -> bool {
    wf(s) && rr64(s, abi::ctx_reg()) == c.ctx && rr64(s, abi::sp_reg()) == c.sp && (forall|
        k: int,
    |
        0 <= k < abi::num_regions() ==> read_mem(s.mem, c.ctx + abi::base_off(k), 8) == Some(
            c.bases[k],
        ) && #[trigger] read_mem(s.mem, c.ctx + abi::bound_off(k), 8) == Some(c.bounds[k]))
        && (forall|q: int|
        0 <= q < c.blob.len() ==> #[trigger] s.mem.dom().contains(c.code + q) && s.mem[c.code + q]
            == c.blob[q]) && read_mem(s.mem, c.sp, 8) == Some(c.ret_raw)
}

/// **The invariant at a position**: the base invariant, and RIP is at
/// instruction `j0 + m`, where `j0` is a unit start that the scan reaches and
/// `m` is within the unit; the facts hold as [`mid_inv`] says.
pub open spec fn pos_inv(c: Cfg, s: State, j0: int, m: int) -> bool {
    base_inv(c, s) && match start_facts(c, j0) {
        None => false,
        Some(fs0) => match unit_at(c.ins, j0, fs0) {
            None => false,
            Some(u) => 0 <= j0 && j0 + u.len <= c.ins.len() && 0 <= m && m < u.len && s.rip == c.code
                + start_of(c.ins, j0 + m) && mid_inv(c, s, j0, fs0, m),
        },
    }
}

/// **The machine-level invariant**: [`pos_inv`] at some position.
pub open spec fn inv(c: Cfg, s: State) -> bool {
    exists|j0: int, m: int| pos_inv(c, s, j0, m)
}

// ----------------------------------------------------------------------------
// Section: the observations
// ----------------------------------------------------------------------------

/// The index of the instruction whose first byte is at RIP, if there is one.
pub open spec fn index_at(c: Cfg, s: State) -> Option<int> {
    if exists|j: int| 0 <= j < c.ins.len() && start_of(c.ins, j) == s.rip - c.code {
        Some(choose|j: int| 0 <= j < c.ins.len() && start_of(c.ins, j) == s.rip - c.code)
    } else {
        None
    }
}

/// The instruction executed next from `s`.
pub open spec fn next_instr(c: Cfg, s: State) -> Option<Instr> {
    match index_at(c, s) {
        Some(j) => Some(c.ins[j]),
        None => None,
    }
}

/// `i` is a system or privileged instruction: none of the subset is. (Spelled
/// out over every variant, so that adding one forces a decision here.)
pub open spec fn is_system(i: Instr) -> bool {
    match i {
        Instr::MovRR { .. } => false,
        Instr::MovLoad { .. } => false,
        Instr::MovStore { .. } => false,
        Instr::MovImm32 { .. } => false,
        Instr::MovImm32S { .. } => false,
        Instr::MovImm64 { .. } => false,
        Instr::AluRR { .. } => false,
        Instr::AluRM { .. } => false,
        Instr::AluRI { .. } => false,
        Instr::TestRR { .. } => false,
        Instr::TestRI { .. } => false,
        Instr::Neg { .. } => false,
        Instr::Not { .. } => false,
        Instr::ShiftImm { .. } => false,
        Instr::ShiftCl { .. } => false,
        Instr::ImulRR { .. } => false,
        Instr::ImulRRI { .. } => false,
        Instr::Jcc { .. } => false,
        Instr::Jmp { .. } => false,
        Instr::Ret => false,
        Instr::Cmovcc { .. } => false,
        Instr::Setcc { .. } => false,
        Instr::FpArith { .. } => false,
        Instr::Sqrtsd { .. } => false,
        Instr::Ucomisd { .. } => false,
        Instr::Cvtsi2sd { .. } => false,
        Instr::Cvttsd2si { .. } => false,
        Instr::Cvtsd2si { .. } => false,
        Instr::MovqToXmm { .. } => false,
        Instr::MovqFromXmm { .. } => false,
        Instr::MovsdLoad { .. } => false,
        Instr::MovsdStore { .. } => false,
    }
}

/// The `n` bytes at `addr` lie in a handed region.
pub open spec fn in_region(c: Cfg, addr: int, n: int) -> bool {
    exists|k: int|
        0 <= k < abi::num_regions() && c.bases[k] <= addr && addr + n <= c.bases[k] + c.bounds[k]
}

/// The `n` bytes at `addr` may be read: they lie in the context or a region.
pub open spec fn readable(c: Cfg, addr: int, n: int) -> bool {
    (c.ctx <= addr && addr + n <= c.ctx + abi::ctx_size()) || in_region(c, addr, n)
}

/// The `n` bytes at `addr` may be written: they lie in the context's exit
/// area or a region.
pub open spec fn writable(c: Cfg, addr: int, n: int) -> bool {
    (c.ctx + abi::exit_code_off() <= addr && addr + n <= c.ctx + abi::ctx_size()) || in_region(
        c,
        addr,
        n,
    )
}

/// The byte at `a` is writable.
pub open spec fn writable_byte(c: Cfg, a: int) -> bool {
    writable(c, a, 1)
}

/// Every load of `i` from `s` is to readable bytes (by [`mem_access`]).
pub open spec fn loads_ok(c: Cfg, s: State, i: Instr) -> bool {
    match mem_access(i) {
        None => true,
        Some(a) => a.store || readable(c, eff_addr(s, a.mem), a.size),
    }
}

/// Every store of `i` from `s` is to writable bytes (by [`mem_access`]).
pub open spec fn stores_ok(c: Cfg, s: State, i: Instr) -> bool {
    match mem_access(i) {
        None => true,
        Some(a) => !a.store || writable(c, eff_addr(s, a.mem), a.size),
    }
}

/// The byte at `a` may be observed by a step: it is readable, or in the
/// stub's return slot (which `ret` reads).
pub open spec fn read_area(c: Cfg, a: int) -> bool {
    readable(c, a, 1) || (c.sp <= a && a < c.sp + 8)
}

/// The memories `m` and `m2` agree (on which bytes are mapped, and on their
/// values) at every byte of the read area.
pub open spec fn agree_on_read_area(c: Cfg, m: Map<int, u8>, m2: Map<int, u8>) -> bool {
    forall|a: int|
        read_area(c, a) ==> (#[trigger] m2.dom().contains(a) == m.dom().contains(a) && (
        m.dom().contains(a) ==> m2[a] == m[a]))
}

/// The states agree on everything but memory.
pub open spec fn eq_mod_mem(t: State, t2: State) -> bool {
    t.rgf == t2.rgf && t.rip == t2.rip && t.rflags == t2.rflags && t.undef == t2.undef && t.xmm
        == t2.xmm
}

/// Two outcomes of a step agree but for memory: both fault, or neither does
/// and the states agree apart from memory.
pub open spec fn same_outcome(o: Option<State>, o2: Option<State>) -> bool {
    (o is Some == o2 is Some) && (o is Some ==> eq_mod_mem(o->Some_0, o2->Some_0))
}

/// **Reads are confined**: from every state that differs from `s` only in
/// memory outside the read area, the step of `i` has the same outcome (apart
/// from memory).
pub open spec fn reads_confined(c: Cfg, e: spec_fn(nat) -> nat, s: State, i: Instr) -> bool {
    forall|m2: Map<int, u8>|
        agree_on_read_area(c, s.mem, m2) ==> #[trigger] same_outcome(
            step(e, s, i),
            step(e, State { mem: m2, ..s }, i),
        )
}

/// Memory is the same in `s` and `s2` at every byte that is not writable
/// (mapped or not).
pub open spec fn writes_confined(c: Cfg, s: State, s2: State) -> bool {
    forall|a: int|
        !writable_byte(c, a) ==> (#[trigger] s2.mem.dom().contains(a) == s.mem.dom().contains(a)
            && (s.mem.dom().contains(a) ==> s2.mem[a] == s.mem[a]))
}

/// `i`, executed from `s`, is the `ret` that ends an exit sequence of the
/// blob: the instruction at the third position of an [`exit_unit_at`].
pub open spec fn is_exit(c: Cfg, s: State, i: Instr) -> bool {
    exists|j: int|
        exit_unit_at(c.ins, j) && i == c.ins[j + 2] && s.rip == c.code + start_of(c.ins, j + 2)
}

/// `s` is the state after the exit sequence returned to the stub: RIP is the
/// stub's return address, `r15` is still the context, `rsp` has popped the
/// slot.
pub open spec fn exited(c: Cfg, s: State) -> bool {
    s.rip == logext(64, c.ret_raw) && rr64(s, abi::ctx_reg()) == c.ctx && rr64(s, abi::sp_reg())
        == c.sp + 8
}

/// The context register and the stack pointer hold the same in `s` and `s2`.
pub open spec fn reserved_same(s: State, s2: State) -> bool {
    rr64(s, abi::ctx_reg()) == rr64(s2, abi::ctx_reg()) && rr64(s, abi::sp_reg()) == rr64(
        s2,
        abi::sp_reg(),
    )
}

impl Machine for X64 {
    type Cfg = Cfg;
    type St = State;
    type Ins = Instr;
    type Env = spec_fn(nat) -> nat;

    open spec fn cfg_ok(c: Cfg) -> bool {
        cfg_ok(c)
    }

    open spec fn inv(c: Cfg, s: State) -> bool {
        inv(c, s)
    }

    open spec fn next_instr(c: Cfg, s: State) -> Option<Instr> {
        next_instr(c, s)
    }

    open spec fn fetched(c: Cfg, s: State, i: Instr) -> bool {
        fetch_ok(s, i)
    }

    open spec fn step(e: spec_fn(nat) -> nat, s: State, i: Instr) -> Option<State> {
        step(e, s, i)
    }

    open spec fn is_system(i: Instr) -> bool {
        is_system(i)
    }

    open spec fn loads_ok(c: Cfg, s: State, i: Instr) -> bool {
        loads_ok(c, s, i)
    }

    open spec fn stores_ok(c: Cfg, s: State, i: Instr) -> bool {
        stores_ok(c, s, i)
    }

    open spec fn reads_confined(c: Cfg, e: spec_fn(nat) -> nat, s: State, i: Instr) -> bool {
        reads_confined(c, e, s, i)
    }

    open spec fn writes_confined(c: Cfg, s: State, s2: State) -> bool {
        writes_confined(c, s, s2)
    }

    open spec fn is_exit(c: Cfg, s: State, i: Instr) -> bool {
        is_exit(c, s, i)
    }

    open spec fn exited(c: Cfg, s: State) -> bool {
        exited(c, s)
    }

    open spec fn reserved_same(s: State, s2: State) -> bool {
        reserved_same(s, s2)
    }
}

/// **The x86-64 confinement theorem, as a statement** (to be proven by
/// `super::x64proof`): [`confinement`] for [`X64`].
pub open spec fn x64_confinement() -> bool {
    confinement::<X64>()
}

/// **The corollary over every finite x86-64 execution**, as a statement.
pub open spec fn x64_run_confinement() -> bool {
    run_confinement::<X64>()
}

} // verus!
