//! **The A64 machine** of the confinement theorem
//! ([`crate::confine::machine::confinement`]): the configuration, the
//! machine-level invariant, and the observations, over `clazel_a64::spec`'s
//! `State` and `step` and `crate::a64::spec`'s acceptance spec. This file is
//! *statement only*: definitions and the [`Machine`] instance. The proof is in
//! the other modules of this directory (CLAUDE.md rule 3: the statement is
//! committed before it).
//!
//! It is the A64 counterpart of [`crate::confine::x64`] and the statement is
//! the same one; this header says where the two machines differ.
//!
//! # The configuration ([`Cfg`])
//!
//! What the sandbox hands over, as numbers: the blob and the instruction list
//! it decodes to, the entries; the address of the blob's first byte (`code`,
//! a multiple of 4: the program counter is aligned), of the context (`ctx`,
//! 512 bytes, jit.md J.0 and [`crate::a64::spec::abi`]); the 16 regions' bases
//! and bounds (as in the context's table); the value of `SP` on entry (`sp`),
//! and the return address the enter stub left in `x30` (`lr`).
//! [`cfg_ok`] says it is a configuration the sandbox may hand over: the blob
//! is accepted, everything lies in the positive canonical addresses
//! (`0 <= a < 2^47`, so that no address computation wraps modulo `2^64`), and
//! **the code, the context's table and each region are pairwise disjoint** (a
//! region may overlap another region and the exit area, which is harmless).
//! These are obligations of the enter stub and the sandbox (J.7, J.8), not of
//! the validator.
//!
//! # The machine-level invariant ([`inv`])
//!
//! Before an instruction ([`pos_inv`], at unit `j0`, `m` instructions into
//! it):
//!
//! - **the state is well formed** (`clazel_a64::spec::wf`);
//! - **the context register `x28` holds the context**, **the link register
//!   `x30` holds the stub's return address** and **`SP` holds the stub's
//!   stack pointer**;
//! - **the region table is intact**: the 16 base/bound words in memory are
//!   the configuration's;
//! - **the code is intact**: the blob's bytes are in memory at `code`;
//! - **the program counter is at the start of instruction `j0 + m`**, where
//!   `j0` is a *unit start* of the blob: a position the validator's scan
//!   reaches by taking units from 0 ([`start_facts`]);
//! - **the facts the scan tracks hold** ([`facts_hold`]): at a unit start
//!   (`m == 0`) those the scan has there, after forgetting at targets; inside
//!   an exit or bounds-check sequence (`m > 0`), the corresponding
//!   intermediate facts ([`mid_inv`]), including the carry and zero flags
//!   after `adds` and `cmp`.
//!
//! # Modelling choices
//!
//! - **The accesses are [`mem_access`]'s**, the validator's own account of
//!   what an instruction touches ([`loads_ok`], [`stores_ok`], at the address
//!   [`eff_addr`] computes from the registers); the proof ties it to the
//!   semantics: a write changes memory only inside the access it names
//!   ([`writes_confined`]), and a step's outcome depends only on the bytes of
//!   the read area ([`reads_confined`]).
//! - **`ret` reads no memory.** It branches to `x30`; the exit sequence's
//!   `ret` therefore returns to `lr` ([`exited`]). There is no stack slot
//!   and so no disjointness condition for one: the blob cannot touch the
//!   stack at all (`SP` is written by nothing the validator accepts, and no
//!   load or store has base `SP`).
//! - **No undefined state.** `clazel-a64`'s `step` is a function of the state
//!   and the instruction, so the choice `Env` the theorem quantifies over is
//!   the unit type.
//! - **The next instruction is found by offset**: [`next_instr`] looks the
//!   program counter's offset up among the instruction starts; [`inv`] has it
//!   at one.
//! - **No system instruction**: [`is_system`] is false for every [`Instr`];
//!   the match is spelled out so that a new variant forces a decision.
//! - **Addresses wrap modulo `2^64`** in the semantics; [`eff_addr`] is the
//!   wrapped address, and [`cfg_ok`] keeps every region and the context below
//!   `2^47` so no permitted access can wrap.
//! - **Facts about registers 0 to 30.** Register 31 is the zero register in
//!   every operand where facts matter, so no fact is ever about it
//!   ([`facts_hold`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The A64 machine: the marker the [`Machine`] instance is for.
pub struct A64;

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
    /// The value of `SP` on entry.
    pub sp: int,
    /// The value of `x30` on entry: where the exit sequence's `ret` returns.
    pub lr: int,
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
/// the code and the context's table.
pub open spec fn region_ok(c: Cfg, k: int) -> bool {
    0 <= c.bases[k] && 0 <= c.bounds[k] && c.bases[k] + c.bounds[k] <= lim() && disjoint(
        c.bases[k],
        c.bounds[k],
        c.code,
        c.blob.len() as int,
    ) && disjoint(c.bases[k], c.bounds[k], c.ctx, abi::table_end())
}

/// **A configuration the sandbox may hand over**: the blob is accepted (the
/// instruction list `ins` is its decoding and passes the policy at the
/// entries), and the layout is as the module documentation says.
pub open spec fn cfg_ok(c: Cfg) -> bool {
    decodes_to(c.blob, c.ins) && policy(c.ins, c.entries) && c.bases.len() == abi::num_regions()
        && c.bounds.len() == abi::num_regions() && 0 <= c.code && c.code % 4 == 0 && c.code
        + c.blob.len() <= lim() && 0 <= c.ctx && c.ctx + abi::ctx_size() <= lim() && disjoint(
        c.code,
        c.blob.len() as int,
        c.ctx,
        abi::ctx_size(),
    ) && (forall|k: int| 0 <= k < abi::num_regions() ==> #[trigger] region_ok(c, k)) && 0 <= c.sp
        && c.sp < p2(64) && 0 <= c.lr && c.lr < p2(64) && disjoint(
        c.lr,
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
/// holds an `i` with `i + n <= bound(k)`. Neither is ever a fact about
/// register 31, the zero register.
pub open spec fn facts_hold(c: Cfg, s: State, fs: Facts) -> bool {
    forall|r: u8|
        r < 32 ==> match #[trigger] fact_of(fs, r) {
            Fact::Unknown => true,
            Fact::Base(k) => r < 31 && 0 <= k < abi::num_regions() && x_read(s, r, 64)
                == c.bases[k],
            Fact::Idx(k, n) => r < 31 && 0 <= k < abi::num_regions() && 0 <= n && x_read(s, r, 64)
                + n <= c.bounds[k],
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

/// What is known after `movz t, #code` of an exit sequence starting at
/// instruction `j0`: `t` is overwritten.
pub open spec fn exit_mid_facts(ins: Seq<Instr>, j0: int, fs0: Facts) -> Facts {
    match ins[j0] {
        Instr::MoveWide { d, .. } => set_fact(fs0, d, Fact::Unknown),
        _ => fs0,
    }
}

/// The facts that hold throughout a bounds check `ch`: all of `fs0` except
/// for the three registers it writes.
pub open spec fn check_mid_facts(fs0: Facts, ch: Chk) -> Facts {
    set_fact(
        set_fact(set_fact(fs0, ch.t, Fact::Unknown), ch.bnd, Fact::Unknown),
        ch.i,
        Fact::Unknown,
    )
}

/// The invariant before instruction `m` (1 to 6) of the bounds check `ch`,
/// whose region's bound is `b` and which began with `fs0` (the instructions
/// are numbered as in [`check_instr`]). With `I` the index register's value,
/// `n` the size, `T` the scratch's and `B` the bound register's, `C` and `Z`
/// the carry and zero flags:
///
/// - 1: `B = b`;
/// - 2: `T = (I + n) mod 2^64` and `C` is set exactly when `I + n >= 2^64`;
/// - 3: `b.hs` fell through, so `I + n < 2^64` and `T = I + n`;
/// - 4: `cmp t, b` has set `C` for `T >= b` and `Z` for `T = b`;
/// - 5: `b.hi` fell through, so `I + n <= b`;
/// - 6: the same, and `C` is set exactly when `I >= b`.
///
/// (and `B = b` throughout).
pub open spec fn check_mid(c: Cfg, s: State, ch: Chk, fs0: Facts, m: int) -> bool {
    0 <= ch.k < abi::num_regions() && facts_hold(c, s, check_mid_facts(fs0, ch)) && {
        let i = x_read(s, ch.i, 64);
        let t = x_read(s, ch.t, 64);
        let bn = x_read(s, ch.bnd, 64);
        let n = ch.n;
        let b = c.bounds[ch.k];
        bn == b && if m == 1 {
            true
        } else if m == 2 {
            t == (i + n) % p2(64) && s.flag_c == (i + n >= p2(64))
        } else if m == 3 {
            i + n < p2(64) && t == i + n
        } else if m == 4 {
            t == i + n && s.flag_c == (t >= b) && s.flag_z == (t == b)
        } else if m == 5 {
            i + n <= b
        } else if m == 6 {
            i + n <= b && s.flag_c == (i >= b)
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
/// state is: the state is well formed, `x28` is the context, `x30` the stub's
/// return address, `SP` the stub's stack pointer, and the region table and the
/// code are intact in memory.
pub open spec fn base_inv(c: Cfg, s: State) -> bool {
    wf(s) && x_read(s, abi::ctx_reg(), 64) == c.ctx && x_read(s, abi::link_reg(), 64) == c.lr
        && s.sp as int == c.sp && (forall|k: int|
        0 <= k < abi::num_regions() ==> mem_read(s.mem, c.ctx + abi::base_off(k), 8) == Some(
            c.bases[k],
        ) && #[trigger] mem_read(s.mem, c.ctx + abi::bound_off(k), 8) == Some(c.bounds[k]))
        && (forall|q: int|
        0 <= q < c.blob.len() ==> #[trigger] s.mem.dom().contains(c.code + q) && s.mem[c.code + q]
            == c.blob[q])
}

/// **The invariant at a position**: the base invariant, and the program
/// counter is at instruction `j0 + m`, where `j0` is a unit start that the
/// scan reaches and `m` is within the unit; the facts hold as [`mid_inv`]
/// says.
pub open spec fn pos_inv(c: Cfg, s: State, j0: int, m: int) -> bool {
    base_inv(c, s) && match start_facts(c, j0) {
        None => false,
        Some(fs0) => match unit_at(c.ins, j0, fs0) {
            None => false,
            Some(u) => 0 <= j0 && j0 + u.len <= c.ins.len() && 0 <= m && m < u.len && s.pc as int
                == c.code + start_of(c.ins, j0 + m) && mid_inv(c, s, j0, fs0, m),
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

/// The index of the instruction whose first byte is at the program counter,
/// if there is one.
pub open spec fn index_at(c: Cfg, s: State) -> Option<int> {
    if exists|j: int| 0 <= j < c.ins.len() && start_of(c.ins, j) == s.pc as int - c.code {
        Some(choose|j: int| 0 <= j < c.ins.len() && start_of(c.ins, j) == s.pc as int - c.code)
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
        Instr::AddSubShiftedReg { .. } => false,
        Instr::AddSubImm { .. } => false,
        Instr::MulAddSub { .. } => false,
        Instr::Div { .. } => false,
        Instr::LogicalShiftedReg { .. } => false,
        Instr::ShiftVariable { .. } => false,
        Instr::Bitfield { .. } => false,
        Instr::MoveWide { .. } => false,
        Instr::CondSelect { .. } => false,
        Instr::LoadStoreImm { .. } => false,
        Instr::LoadStoreReg { .. } => false,
        Instr::FpLoadStoreImm { .. } => false,
        Instr::FpLoadStoreReg { .. } => false,
        Instr::B { .. } => false,
        Instr::BCond { .. } => false,
        Instr::CompareBranch { .. } => false,
        Instr::Ret => false,
        Instr::FAddSub { .. } => false,
        Instr::FMul { .. } => false,
        Instr::FDiv { .. } => false,
        Instr::FUnary { .. } => false,
        Instr::FCmp { .. } => false,
        Instr::FMovGen { .. } => false,
        Instr::Scvtf { .. } => false,
        Instr::Fcvtzs { .. } => false,
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

/// The address an access of `a` touches from `s`, as the semantics computes
/// it: the base register plus the immediate, or plus the (shifted) index
/// register (`ExtendReg` with `UXTX`), modulo `2^64`.
pub open spec fn eff_addr(s: State, a: Access) -> int {
    match a.index {
        None => trunc(64, x_read(s, a.base, 64) + a.off),
        Some(m) => trunc(
            64,
            x_read(s, a.base, 64) + extend_reg_uxtx(
                s,
                m,
                if a.scaled {
                    if a.size == 8 {
                        3nat
                    } else {
                        2nat
                    }
                } else {
                    0nat
                },
            ),
        ),
    }
}

/// Every load of `i` from `s` is to readable bytes (by [`mem_access`]).
pub open spec fn loads_ok(c: Cfg, s: State, i: Instr) -> bool {
    match mem_access(i) {
        None => true,
        Some(a) => a.store || readable(c, eff_addr(s, a), a.size),
    }
}

/// Every store of `i` from `s` is to writable bytes (by [`mem_access`]).
pub open spec fn stores_ok(c: Cfg, s: State, i: Instr) -> bool {
    match mem_access(i) {
        None => true,
        Some(a) => !a.store || writable(c, eff_addr(s, a), a.size),
    }
}

/// The byte at `a` may be observed by a step: it is readable.
pub open spec fn read_area(c: Cfg, a: int) -> bool {
    readable(c, a, 1)
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
    t.r == t2.r && t.sp == t2.sp && t.pc == t2.pc && t.flag_n == t2.flag_n && t.flag_z
        == t2.flag_z && t.flag_c == t2.flag_c && t.flag_v == t2.flag_v && t.vreg == t2.vreg
}

/// Two outcomes of a step agree but for memory: both fault, or neither does
/// and the states agree apart from memory.
pub open spec fn same_outcome(o: Option<State>, o2: Option<State>) -> bool {
    (o is Some == o2 is Some) && (o is Some ==> eq_mod_mem(o->Some_0, o2->Some_0))
}

/// **Reads are confined**: from every state that differs from `s` only in
/// memory outside the read area, the step of `i` has the same outcome (apart
/// from memory).
pub open spec fn reads_confined(c: Cfg, s: State, i: Instr) -> bool {
    forall|m2: Map<int, u8>|
        agree_on_read_area(c, s.mem, m2) ==> #[trigger] same_outcome(
            step(s, i),
            step(State { mem: m2, ..s }, i),
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
        exit_unit_at(c.ins, j) && i == c.ins[j + 2] && s.pc as int == c.code + start_of(
            c.ins,
            j + 2,
        )
}

/// `s` is the state after the exit sequence returned to the stub: the program
/// counter is the stub's return address, `x28` is still the context, `x30` the
/// return address, and `SP` the stub's.
pub open spec fn exited(c: Cfg, s: State) -> bool {
    s.pc as int == c.lr && x_read(s, abi::ctx_reg(), 64) == c.ctx && x_read(
        s,
        abi::link_reg(),
        64,
    ) == c.lr && s.sp as int == c.sp
}

/// The context register, the link register and the stack pointer hold the
/// same in `s` and `s2`.
pub open spec fn reserved_same(s: State, s2: State) -> bool {
    x_read(s, abi::ctx_reg(), 64) == x_read(s2, abi::ctx_reg(), 64) && x_read(
        s,
        abi::link_reg(),
        64,
    ) == x_read(s2, abi::link_reg(), 64) && s.sp == s2.sp
}

impl Machine for A64 {
    type Cfg = Cfg;
    type St = State;
    type Ins = Instr;
    type Env = ();

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

    open spec fn step(e: (), s: State, i: Instr) -> Option<State> {
        step(s, i)
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

    open spec fn reads_confined(c: Cfg, e: (), s: State, i: Instr) -> bool {
        reads_confined(c, s, i)
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

/// **The A64 confinement theorem, as a statement** (to be proven by
/// `super::proof`): [`confinement`] for [`A64`].
pub open spec fn a64_confinement() -> bool {
    confinement::<A64>()
}

/// **The corollary over every finite A64 execution**, as a statement.
pub open spec fn a64_run_confinement() -> bool {
    run_confinement::<A64>()
}

} // verus!
