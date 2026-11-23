//! The dataflow solver: control-flow graph, lattice, fixpoint. **Nothing is
//! proven about what it computes**; Verus checks only that it cannot panic
//! or overflow and that its loops end. Its answer is a certificate that
//! [`super::check::check_units`] verifies against the spec, so a bug here can
//! make the validator refuse and can never make it accept.
//!
//! # The analysis
//!
//! - **Units.** The same recognized sequences as the spec's scan (the exit
//!   sequence of 3 instructions, the bounds check of 8, any other single
//!   instruction), found by one left-to-right pass.
//! - **Basic blocks.** A unit starts a block if it is the first unit, an
//!   entry or a jump target, or follows a unit that ends a block (`jcc`, the
//!   bounds check with its two exits, `jmp`, the exit sequence).
//! - **The lattice.** Per register: `Bot` (no path has reached this yet,
//!   every fact vacuously), `Base(k)`, `Idx(k, n)`, and `Top` (nothing
//!   known). The join of two facts is the fact if they agree (`Idx` joins by
//!   the smaller size) and `Top` otherwise, with `Bot` the identity.
//! - **Edges.** A block that falls through into the next gives it its exit
//!   state. A jump or an entry gives the target the empty state (`Top`):
//!   jit.md says a check holds "earlier in the same basic block", and the
//!   spec forgets everything at a target, so no fact flows along a branch
//!   edge. A block that ends in `jmp` or an exit has no fall-through edge, so
//!   the unit after it is entered from outside too and starts at `Top`.
//! - **Transfer.** The exit sequence and `jmp` give `Top` everywhere; the
//!   bounds check makes its scratch registers `Top` and its index
//!   `Idx(k, n)`; a load of `[r15 + 16k]` in 64 bits makes its destination
//!   `Base(k)`; any other write makes its destination `Top`.
//! - **Fixpoint.** Round-robin passes over the blocks in order, joining each
//!   block's exit state into its fall-through successor, until a pass changes
//!   nothing or the pass budget (`units + 2`) runs out. With these edges the
//!   graph of non-`Top` flow is a chain, so one pass settles it and the
//!   second confirms; the loop is general all the same. If the budget runs out
//!   the last state is returned, and the checker decides whether it is a
//!   fixpoint: it is the checker, not this loop, that guarantees it.
//!
//! The result `inn` holds 16 slots per instruction index, `inn[16 * j + r]`
//! the state of register `r` at the unit that starts at instruction `j` (the
//! other slots are unused). `Bot` and `Top` both export as `Unknown`.

#[allow(unused_imports)]
use super::spec::*;
use crate::unit_exec::{FactE, base_load_region_e, check_at_e, exit_at_e, written_gpr_e};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the solver knows of one register.
#[derive(Clone, Copy)]
enum Lat {
    /// No path has reached here yet: every fact, vacuously.
    Bot,
    /// Nothing known.
    Top,
    /// The base of region `k`.
    Base(u8),
    /// Checked for `n` bytes of region `k`.
    Idx(u8, u8),
}

/// The least fact that follows from both.
fn join(a: Lat, b: Lat) -> Lat {
    match (a, b) {
        (Lat::Bot, x) => x,
        (x, Lat::Bot) => x,
        (Lat::Base(p), Lat::Base(q)) => if p == q {
            Lat::Base(p)
        } else {
            Lat::Top
        },
        (Lat::Idx(p, m), Lat::Idx(q, n)) => if p == q {
            Lat::Idx(p, if m < n {
                m
            } else {
                n
            })
        } else {
            Lat::Top
        },
        _ => Lat::Top,
    }
}

/// The two are the same fact.
fn same(a: Lat, b: Lat) -> bool {
    match (a, b) {
        (Lat::Bot, Lat::Bot) => true,
        (Lat::Top, Lat::Top) => true,
        (Lat::Base(p), Lat::Base(q)) => p == q,
        (Lat::Idx(p, m), Lat::Idx(q, n)) => p == q && m == n,
        _ => false,
    }
}

/// The exported form of a fact.
fn to_fact(l: Lat) -> FactE {
    match l {
        Lat::Base(k) => FactE::Base(k),
        Lat::Idx(k, n) => FactE::Idx(k, n),
        _ => FactE::Unknown,
    }
}

/// `v[i] = x` if `i` is in range.
fn put(v: &mut Vec<Lat>, i: usize, x: Lat) {
    if i < v.len() {
        v.set(i, x);
    }
}

/// `v[i]`, or `Top` if out of range.
fn get(v: &[Lat], i: usize) -> Lat {
    match v.get(i) {
        Some(x) => *x,
        None => Lat::Top,
    }
}

/// `v[i]`, or `false` if out of range.
fn get_flag(v: &[bool], i: usize) -> bool {
    match v.get(i) {
        Some(x) => *x,
        None => false,
    }
}

/// The length of the unit recorded at `i`, at least 1.
fn unit_len(v: &[u8], i: usize) -> (r: usize)
    ensures
        r >= 1,
{
    match v.get(i) {
        Some(x) => if *x == 0 {
            1
        } else {
            *x as usize
        },
        None => 1,
    }
}

/// What a single instruction does to the block: 0 nothing, 1 ends it and
/// falls through (`jcc`), 2 ends it with no fall-through (`jmp`).
fn plain_end(i: Option<&Instr>) -> u8 {
    match i {
        Some(Instr::Jmp { .. }) => 2,
        Some(Instr::Jcc { .. }) => 1,
        _ => 0,
    }
}

/// Makes every one of the 16 registers `x`.
fn set_all(cur: &mut Vec<Lat>, x: Lat) {
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
        decreases 16 - k,
    {
        put(cur, k, x);
        k = k.saturating_add(1);
    }
}

/// The transfer function of the unit that starts at instruction `j`.
fn step(ins: &[Instr], j: usize, cur: &mut Vec<Lat>)
    requires
        j < 0x8000_0000,
{
    if exit_at_e(ins, j) {
        set_all(cur, Lat::Top);
        return ;
    }
    match check_at_e(ins, j) {
        Some(c) => {
            put(cur, c.t as usize, Lat::Top);
            put(cur, c.z as usize, Lat::Top);
            put(cur, c.i as usize, Lat::Idx(c.k, c.n));
        },
        None => match ins.get(j) {
            Some(Instr::Jmp { .. }) => set_all(cur, Lat::Top),
            Some(i) => {
                if let Some(d) = written_gpr_e(i) {
                    let v = match base_load_region_e(i) {
                        Some(k) => Lat::Base(k),
                        None => Lat::Top,
                    };
                    put(cur, d as usize, v);
                }
            },
            None => {},
        },
    }
}

/// Copies the 16 slots of `cells` for the unit at `j` into `cur`.
fn load(cells: &[Lat], j: usize, cur: &mut Vec<Lat>) {
    let base = j.saturating_mul(16);
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
        decreases 16 - k,
    {
        put(cur, k, get(cells, base.saturating_add(k)));
        k = k.saturating_add(1);
    }
}

/// Copies `cur` into the 16 slots of `cells` for the unit at `j`.
fn store(cells: &mut Vec<Lat>, j: usize, cur: &[Lat]) {
    let base = j.saturating_mul(16);
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
        decreases 16 - k,
    {
        put(cells, base.saturating_add(k), get(cur, k));
        k = k.saturating_add(1);
    }
}

/// Joins `cur` into the slots of the unit at `j`; says whether any changed.
fn join_into(cells: &mut Vec<Lat>, j: usize, cur: &[Lat]) -> bool {
    let base = j.saturating_mul(16);
    let mut changed = false;
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
        decreases 16 - k,
    {
        let slot = base.saturating_add(k);
        let old = get(cells.as_slice(), slot);
        let new = join(old, get(cur, k));
        if !same(old, new) {
            changed = true;
        }
        put(cells, slot, new);
        k = k.saturating_add(1);
    }
    changed
}

/// Solves the analysis for `ins` (see the module comment). `st[j]` is the
/// start offset of instruction `j`, `mark` flags the entries and jump
/// targets by byte offset. Returns 16 slots per instruction index.
#[verifier::spinoff_prover]
pub fn solve(ins: &[Instr], st: &[usize], mark: &[bool]) -> (inn: Vec<FactE>)
    requires
        ins@.len() < 0x8000_0000,
{
    let n = ins.len();
    let cells_len = n.saturating_add(1).saturating_mul(16);
    // Pass 1: the units and how each ends its block.
    let mut ulen: Vec<u8> = vec![0; n];
    let mut ends: Vec<u8> = vec![0; n];
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            n == ins@.len(),
            n < 0x8000_0000,
            ulen@.len() == n,
            ends@.len() == n,
        decreases n - j,
    {
        let (l, e): (u8, u8) = if exit_at_e(ins, j) {
            (3, 2)
        } else if check_at_e(ins, j).is_some() {
            (8, 1)
        } else {
            (1, plain_end(ins.get(j)))
        };
        ulen.set(j, l);
        ends.set(j, e);
        let nj = j.saturating_add(l as usize);
        j = if nj < n {
            nj
        } else {
            n
        };
    }
    // Pass 2: the blocks. A leader starts a block; a seed is a leader that
    // is entered from outside, so starts at `Top`.
    let mut lead: Vec<bool> = vec![false; n];
    let mut seed: Vec<bool> = vec![false; n];
    let mut cells: Vec<Lat> = vec![Lat::Bot; cells_len];
    let mut prev_end: u8 = 2;
    j = 0;
    while j < n
        invariant
            j <= n,
            n == ins@.len(),
            ulen@.len() == n,
            ends@.len() == n,
            lead@.len() == n,
            seed@.len() == n,
        decreases n - j,
    {
        let marked = match st.get(j) {
            Some(h) => match mark.get(*h) {
                Some(b) => *b,
                None => true,
            },
            None => true,
        };
        let is_seed = marked || prev_end == 2;
        let is_lead = is_seed || prev_end == 1;
        lead.set(j, is_lead);
        seed.set(j, is_seed);
        if is_seed {
            let base = j.saturating_mul(16);
            let mut k: usize = 0;
            while k < 16
                invariant
                    k <= 16,
                decreases 16 - k,
            {
                put(&mut cells, base.saturating_add(k), Lat::Top);
                k = k.saturating_add(1);
            }
        }
        prev_end = match ends.get(j) {
            Some(e) => *e,
            None => 2,
        };
        let nj = j.saturating_add(unit_len(ulen.as_slice(), j));
        j = if nj < n {
            nj
        } else {
            n
        };
    }
    // Pass 3: the fixpoint.
    let budget = n.saturating_add(2);
    let mut pass: usize = 0;
    let mut stable = false;
    while pass < budget && !stable
        invariant
            pass <= budget,
            n == ins@.len(),
            n < 0x8000_0000,
        decreases budget - pass,
    {
        stable = true;
        let mut cur: Vec<Lat> = vec![Lat::Top; 16];
        j = 0;
        while j < n
            invariant
                j <= n,
                n == ins@.len(),
                n < 0x8000_0000,
            decreases n - j,
        {
            let l = unit_len(ulen.as_slice(), j);
            if get_flag(lead.as_slice(), j) {
                load(cells.as_slice(), j, &mut cur);
            } else {
                store(&mut cells, j, cur.as_slice());
            }
            step(ins, j, &mut cur);
            let nj = j.saturating_add(l);
            let flows = nj < n && get_flag(lead.as_slice(), nj) && !get_flag(seed.as_slice(), nj);
            if flows && join_into(&mut cells, nj, cur.as_slice()) {
                stable = false;
            }
            j = if nj < n {
                nj
            } else {
                n
            };
        }
        pass = pass.saturating_add(1);
    }
    // Export.
    let mut inn: Vec<FactE> = vec![FactE::Unknown; cells_len];
    let mut k: usize = 0;
    while k < cells_len
        invariant
            k <= cells_len,
            inn@.len() == cells_len,
        decreases cells_len - k,
    {
        inn.set(k, to_fact(get(cells.as_slice(), k)));
        k = k.saturating_add(1);
    }
    inn
}

} // verus!
