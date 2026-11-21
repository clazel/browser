//! **The confinement theorem, stated once over an abstract machine** (jit.md
//! exit criterion 2, item J.6: "It is stated once, over an abstract machine
//! interface, and proven for each instruction set's semantics").
//!
//! [`Machine`] is the interface: what a configuration, a state and an
//! instruction are, how the machine steps, and the handful of observations the
//! theorem needs (which accesses an instruction makes, what the machine-level
//! invariant is, what leaving through the exit sequence looks like). Each
//! instruction set implements it from its own semantics
//! ([`super::x64::X64`] is the only implementation so far; A64's is later work).
//!
//! The statement is [`confinement`], a closed spec function. A proof of it for
//! one machine is a proof function whose `ensures` is `confinement::<M>()`.
//! [`run_confinement`] is the corollary over every finite execution.
//!
//! # What the statement says
//!
//! Take a configuration the sandbox could hand over ([`Machine::cfg_ok`]: an
//! accepted blob, its entries, the context, the regions, the stack slot, laid
//! out disjointly), and a state that satisfies the machine-level invariant
//! ([`Machine::inv`]: the context register holds the context, the region table
//! and the code are intact, the program counter is at a unit start of the
//! blob, and what the validator's scan knows about the registers holds). Then
//! the next instruction ([`Machine::next_instr`], one whose bytes are at the
//! program counter, [`Machine::fetched`]) is:
//!
//! - **not a system or privileged instruction** ([`Machine::is_system`]);
//! - **a load only inside the context or a handed region**
//!   ([`Machine::loads_ok`]) and **a store only inside the context's exit area
//!   or a handed region** ([`Machine::stores_ok`]), whether or not the access
//!   faults;
//! - **blind to every other byte of memory**: what the step does (whether it
//!   faults, and what it leaves in the registers) does not depend on memory
//!   outside the readable areas and the stub's return slot
//!   ([`Machine::reads_confined`]). This is the machine-level reading of
//!   "only loads inside the regions": [`Machine::loads_ok`] is the
//!   validator's own account of the access, and this ties it to the
//!   semantics;
//!
//! and, if the step does not fault, it
//!
//! - **changes no memory outside the writable areas**
//!   ([`Machine::writes_confined`]); and
//! - either **is the last instruction of the exit sequence**
//!   ([`Machine::is_exit`]) and the machine has left through it
//!   ([`Machine::exited`]: control is back in the enter stub, no instruction
//!   of the blob is next), **or keeps the invariant** ([`Machine::inv`]) **and
//!   leaves the reserved registers as they were** ([`Machine::reserved_same`]).
//!
//! # What it does not say
//!
//! - It is about the *semantics* the machine implements. That the semantics
//!   is faithful to the hardware, and that the bytes at the program counter
//!   are decoded by the hardware as the instruction [`Machine::next_instr`]
//!   names (the decoder is unique, `clazel-x64`'s `canonical_prefix_free`),
//!   is the TCB jit.md lists.
//! - **Termination**: a blob may loop for ever.
//! - Each machine's own modelling choices; see its documentation.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An abstract machine, as far as the confinement theorem needs one.
pub trait Machine: Sized {
    /// What the sandbox hands over: the code blob and its entries, where the
    /// code, the context, the regions and the stack slot are.
    type Cfg;
    /// The machine state: registers, flags, program counter, memory.
    type St;
    /// One instruction.
    type Ins;
    /// What the semantics leaves unspecified (x86-64: the value of an
    /// undefined flag). The theorem holds for every one.
    type Env;

    /// The configuration is one the sandbox may hand over.
    spec fn cfg_ok(c: Self::Cfg) -> bool;

    /// **The machine-level invariant**, which a state must satisfy for the
    /// theorem to say anything about the step that starts from it. It holds at
    /// every entry the validator accepted, if the context invariant holds
    /// there.
    spec fn inv(c: Self::Cfg, s: Self::St) -> bool;

    /// The instruction the machine executes next from `s`, if the program
    /// counter is at one.
    spec fn next_instr(c: Self::Cfg, s: Self::St) -> Option<Self::Ins>;

    /// The bytes at the program counter of `s` are the encoding of `i`.
    spec fn fetched(c: Self::Cfg, s: Self::St, i: Self::Ins) -> bool;

    /// The semantics: one step, or `None` for a fault (an unmapped access).
    spec fn step(e: Self::Env, s: Self::St, i: Self::Ins) -> Option<Self::St>;

    /// `i` is a system or privileged instruction.
    spec fn is_system(i: Self::Ins) -> bool;

    /// Every load `i` makes from `s` lies in the context or a handed region.
    spec fn loads_ok(c: Self::Cfg, s: Self::St, i: Self::Ins) -> bool;

    /// Every store `i` makes from `s` lies in the context's exit area or a
    /// handed region.
    spec fn stores_ok(c: Self::Cfg, s: Self::St, i: Self::Ins) -> bool;

    /// **Reads are confined**: the step of `i` from `s` is the same, apart
    /// from memory, from every state that differs from `s` only in memory
    /// outside the readable areas (the context, the handed regions) and the
    /// stub's return slot: it faults in one if and only if in the other, and
    /// leaves the same registers, flags and program counter. The step reads
    /// nothing else.
    spec fn reads_confined(c: Self::Cfg, e: Self::Env, s: Self::St, i: Self::Ins) -> bool;

    /// Going from `s` to `s2` changed no memory outside the writable areas
    /// (the exit area and the handed regions).
    spec fn writes_confined(c: Self::Cfg, s: Self::St, s2: Self::St) -> bool;

    /// `i`, executed from `s`, is the last instruction of an exit sequence.
    spec fn is_exit(c: Self::Cfg, s: Self::St, i: Self::Ins) -> bool;

    /// `s` is the state after leaving through the exit sequence: control is
    /// in the enter stub.
    spec fn exited(c: Self::Cfg, s: Self::St) -> bool;

    /// The reserved registers (the context register, the stack pointer) are
    /// the same in `s` and `s2`.
    spec fn reserved_same(s: Self::St, s2: Self::St) -> bool;
}

/// **One step is confined**: from a state satisfying the invariant, the next
/// instruction is in the subset, its accesses lie where they may, and the step
/// either keeps the invariant or leaves through the exit sequence (after which
/// no instruction of the blob is next).
pub open spec fn confined_step<M: Machine>(c: M::Cfg, e: M::Env, s: M::St) -> bool {
    M::inv(c, s) ==> match M::next_instr(c, s) {
        None => false,
        Some(i) => M::fetched(c, s, i) && !M::is_system(i) && M::loads_ok(c, s, i) && M::stores_ok(
            c,
            s,
            i,
        ) && M::reads_confined(c, e, s, i) && match M::step(e, s, i) {
            None => true,
            Some(s2) => M::writes_confined(c, s, s2) && if M::is_exit(c, s, i) {
                M::exited(c, s2) && M::next_instr(c, s2) is None
            } else {
                M::inv(c, s2) && M::reserved_same(s, s2)
            },
        },
    }
}

/// **The confinement theorem** (jit.md exit criterion 2, item J.6): for every
/// configuration the sandbox may hand over, every choice the semantics leaves
/// open and every state, one step is confined.
pub open spec fn confinement<M: Machine>() -> bool {
    forall|c: M::Cfg, e: M::Env, s: M::St| M::cfg_ok(c) ==> #[trigger] confined_step::<M>(c, e, s)
}

/// The machine steps from `s` to `s2`: `s` has a next instruction, and its
/// semantics takes `s` to `s2`.
pub open spec fn steps_to<M: Machine>(c: M::Cfg, e: M::Env, s: M::St, s2: M::St) -> bool {
    exists|i: M::Ins| M::next_instr(c, s) == Some(i) && #[trigger] M::step(e, s, i) == Some(s2)
}

/// `ex` is an execution of the machine: the machine steps from each state but
/// the last to the following one.
pub open spec fn is_run<M: Machine>(c: M::Cfg, e: M::Env, ex: Seq<M::St>) -> bool {
    forall|k: int|
        0 <= k && k + 1 < ex.len() ==> #[trigger] steps_to::<M>(c, e, ex[k], ex[k + 1])
}

/// **What the corollary says of an execution**: every state but the last
/// satisfies the invariant (so every instruction executed was one of the
/// blob, confined as [`confined_step`] says), and the last either satisfies it
/// too, or the execution got there by the exit sequence (and so ends).
pub open spec fn run_confined<M: Machine>(c: M::Cfg, ex: Seq<M::St>) -> bool {
    (forall|k: int| 0 <= k && k + 1 < ex.len() ==> #[trigger] M::inv(c, ex[k])) && (ex.len() > 0
        ==> M::inv(c, ex.last()) || (ex.len() >= 2 && M::exited(c, ex.last()) && exists|i: M::Ins|
        M::is_exit(c, ex[ex.len() - 2], i) && M::next_instr(c, ex[ex.len() - 2]) == Some(i)))
}

/// **The corollary over every finite execution**: an execution from a state
/// satisfying the invariant, of a configuration the sandbox may hand over,
/// stays in the invariant and ends only by the exit sequence (or is cut off
/// while still inside).
pub open spec fn run_confinement<M: Machine>() -> bool {
    forall|c: M::Cfg, e: M::Env, ex: Seq<M::St>|
        M::cfg_ok(c) && ex.len() > 0 && #[trigger] is_run::<M>(c, e, ex) && M::inv(c, ex[0])
            ==> run_confined::<M>(c, ex)
}

} // verus!
