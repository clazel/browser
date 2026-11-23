//! LIR's semantics (docs/phases/jit.md item J.5): a big-step, fuelled
//! interpreter written as a `spec fn`, `eval`.
//!
//! It transcribes the numeric, variable, parametric, memory and control
//! instructions of the WebAssembly core specification, release 2.0
//! ("Execution", §4.3 numeric operators and §4.4 instructions). The Wasm
//! specification is **not vendored**, and the section numbers below are
//! from the 2.0 release as remembered by the author: they name the
//! instruction or operator exactly, and a reviewer should check the number
//! against the text. Wasm's own presentation is a small-step reduction
//! relation on configurations with administrative instructions (`label`,
//! `frame`); the first modelling choice below explains the change.
//!
//! # Modelling choices
//!
//! Everything here where the *form* differs from the standard, or where LIR
//! differs from Wasm in *meaning*:
//!
//! 1. **Big-step with fuel instead of small-step reduction.** Wasm §4.4.8
//!    reduces `label` administrative instructions; here a structured
//!    instruction evaluates its body and then handles the outcome. A branch
//!    is the outcome `Branch(l, state)`, and the enclosing `block`, `loop` or
//!    `if` that is label `l` catches it (§4.4.8, `br l` with label `L`: "pop
//!    the top `n` values, discard the rest of the label's stack, push them,
//!    continue after the label, or at its start for a `loop`"). Divergence is
//!    `OutOfFuel`: every recursive call spends one unit of fuel, so `eval` is
//!    a total function, and "the program runs for ever" is "`OutOfFuel` at
//!    every fuel". Results are deterministic by construction.
//! 2. **A block's body runs on a fresh stack holding only its parameters.**
//!    Wasm's label records the stack height; here the outer values below the
//!    parameters are set aside (`base`) and put back, below the results,
//!    when the block ends or is branched to. The meaning is the same
//!    because Wasm's validation forbids a body from reaching below its
//!    parameters.
//! 3. **No function calls, no tables, no globals, no `memory.grow`.** There
//!    is one function body, run by `run`, whose label `0` (outermost) is
//!    "return". Wasm's trap is the outcome `Exit` (jit.md: services and
//!    traps are exits); an `exit` is also LIR's only way to stop other than
//!    falling off the end or a return.
//! 4. **Memory is regions.** The layout (a `Seq<Region>`, each a base and a
//!    bound) is a constant parameter of the semantics, not part of the
//!    state: the blob is entered once with a fixed table (jit.md: "Regions
//!    are passed afresh at each entry"). Memory is a map from addresses to
//!    bytes, with absent bytes reading as 0, which is Wasm's initial memory
//!    content; Wasm §4.3.1 stores integers and floats little-endian, as
//!    here. A load or store whose region does not exist, or whose
//!    `index + size` exceeds the bound, is `Stuck`: a semantics has no
//!    meaning for it, and the typing proves it never happens. Wasm would
//!    trap; LIR code is required to have checked (`bounds_check`) before.
//! 5. **`bounds_check` and the index mask are LIR's, not Wasm's.** After a
//!    passing check, the address is `base + masked(bound, i)`, where
//!    `masked(bound, i) = if i < bound { i } else { 0 }` (jit.md: "Indexes
//!    are masked after the check"). Under a passing check with `size > 0`
//!    the mask is the identity; it is in the semantics so that the back
//!    end's masking is a refinement of it, not an addition to it.
//! 6. **`f64` arithmetic is uninterpreted.** `add`, `sub`, `mul`, `div`,
//!    `sqrt` and the integer-to-float conversions are the uninterpreted
//!    functions `f64_add` and so on, over bit patterns. IEEE 754 rounding
//!    is not transcribed (the JS engine's `spec` does the same, and the
//!    hardware semantics in `clazel-x64` and `clazel-a64` is what the back
//!    ends are proven against). Wasm leaves the sign and payload of a NaN
//!    result nondeterministic (§4.3.3, `nans`); one fixed function is a
//!    refinement of that, and no more. Comparison, `neg` and `abs` are
//!    exact (§4.3.3: `feq`, `flt`..., `fneg`, `fabs`), on the bits.
//! 7. **Integers are `u32` and `u64`**, signedness is in the operator, as
//!    in Wasm (§4.3.1 "Integers", `signed_N`). Arithmetic is on `int`
//!    followed by reduction modulo `2^N`, which is the definition of
//!    `iadd`, `isub`, `imul` (§4.3.2).
//! 8. **`select` is the untyped form**, and `if` takes its condition from
//!    the stack of the *enclosing* body, as Wasm does.

/// The syntax, re-exported so that every module sees one namespace.
pub use crate::syntax::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `2^n`: vstd's `pow2`, under a short name.
pub open spec fn pow2(n: nat) -> nat {
    vstd::arithmetic::power2::pow2(n)
}

// ---------------------------------------------------------------------
// Layout and memory
// ---------------------------------------------------------------------

/// A region: where it starts in the address space and how many bytes it has.
pub struct Region {
    /// The address of the region's first byte.
    pub base: nat,
    /// The region's size in bytes.
    pub bound: nat,
}

/// The table of regions a blob is entered with (jit.md: "a fixed table of
/// (base, bound) pairs").
pub type Layout = Seq<Region>;

/// Every region lies below `2^64`, so every address the semantics forms is a
/// machine address.
pub open spec fn layout_wf(lay: Layout) -> bool {
    forall|r: int| 0 <= r < lay.len() ==> (#[trigger] lay[r]).base + lay[r].bound <= 0x1_0000_0000_0000_0000
}

/// Byte-addressed memory. Absent addresses read as 0.
pub type Mem = Map<nat, u8>;

/// The byte at `a`.
pub open spec fn byte_at(m: Mem, a: nat) -> u8 {
    if m.dom().contains(a) {
        m[a]
    } else {
        0
    }
}

/// `n` bytes from `a`, little-endian, as a number (Wasm core §4.3.1
/// "Bytes": `bytes_t`, little-endian, and its inverse).
pub open spec fn read_le(m: Mem, a: nat, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        byte_at(m, a) as nat + 256 * read_le(m, a + 1, (n - 1) as nat)
    }
}

/// Store the low `n` bytes of `v` at `a`, little-endian.
pub open spec fn write_le(m: Mem, a: nat, v: nat, n: nat) -> Mem
    decreases n,
{
    if n == 0 {
        m
    } else {
        write_le(m.insert(a, (v % 256) as u8), a + 1, v / 256, (n - 1) as nat)
    }
}

/// The index after the mask (modelling choice 5).
pub open spec fn masked(bound: nat, i: nat) -> nat {
    if i < bound {
        i
    } else {
        0
    }
}

/// The size in bytes of a value of type `t` in memory (Wasm core §4.3.1,
/// `|t|/8`). 0 for `Idx`, which is not a storable type.
pub open spec fn ty_size(t: Ty) -> nat {
    match t {
        Ty::I32 => 4,
        Ty::I64 => 8,
        Ty::F64 => 8,
        Ty::Idx(_, _) => 0,
    }
}

/// The bits of a value, as stored.
pub open spec fn val_bits(v: Val) -> nat {
    match v {
        Val::I32(x) => x as nat,
        Val::I64(x) => x as nat,
        Val::F64(x) => x as nat,
    }
}

/// The value of type `t` whose stored bits are `n`.
pub open spec fn val_of_bits(t: Ty, n: nat) -> Val {
    match t {
        Ty::I32 => Val::I32(n as u32),
        Ty::I64 => Val::I64(n as u64),
        Ty::F64 => Val::F64(n as u64),
        Ty::Idx(_, _) => Val::I64(n as u64),
    }
}

/// The value has the base type `t` (`Idx` is not a base type: no value has
/// it by its shape alone, see `typing::conforms`).
pub open spec fn val_has_base_ty(v: Val, t: Ty) -> bool {
    match (v, t) {
        (Val::I32(_), Ty::I32) => true,
        (Val::I64(_), Ty::I64) => true,
        (Val::F64(_), Ty::F64) => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------
// Integer and floating-point operators (Wasm core §4.3)
// ---------------------------------------------------------------------

/// `signed_N` (Wasm core §4.3.1 "Integers"): the two's-complement reading
/// of the `bits`-bit unsigned number `x`.
pub open spec fn signed_of(bits: nat, x: int) -> int {
    if x < pow2(bits) / 2 {
        x
    } else {
        x - pow2(bits)
    }
}

/// Reduction modulo `2^bits`.
pub open spec fn wrap(bits: nat, n: int) -> int {
    n % (pow2(bits) as int)
}

/// The arithmetic and shift integer operators on `bits`-bit unsigned numbers
/// `x`, `y` (Wasm core §4.3.2). The bitwise `and`, `or`, `xor` are
/// not here: they are on `u32` and `u64` directly, see [`ibin32`].
/// A shift or rotate count is taken modulo `bits` (§4.3.2, `ishl`: "`k` is
/// `j2 mod N`").
pub open spec fn iarith(op: IBin, bits: nat, x: int, y: int) -> int {
    let k = (y % (bits as int)) as nat;
    match op {
        // iadd: "(i1 + i2) mod 2^N"
        IBin::Add => wrap(bits, x + y),
        // isub: "(i1 - i2 + 2^N) mod 2^N"
        IBin::Sub => wrap(bits, x - y),
        // imul: "(i1 * i2) mod 2^N"
        IBin::Mul => wrap(bits, x * y),
        // ishl: "ibits_N^-1 (ibits_N(i1) << k)" = i1 * 2^k mod 2^N
        IBin::Shl => wrap(bits, x * pow2(k) as int),
        // ishr_u: "(i1 >> k)" with zeros shifted in = floor(i1 / 2^k)
        IBin::ShrU => x / (pow2(k) as int),
        // ishr_s: the sign bit is shifted in = floor(signed(i1) / 2^k), mod 2^N
        IBin::ShrS => wrap(bits, signed_of(bits, x) / (pow2(k) as int)),
        // irotl: the bits shifted out of the left come back on the right
        IBin::Rotl => wrap(
            bits,
            wrap(bits, x * pow2(k) as int) + x / (pow2((bits - k) as nat) as int),
        ),
        // irotr: the bits shifted out of the right come back on the left
        IBin::Rotr => wrap(
            bits,
            x / (pow2(k) as int) + wrap(bits, x * pow2((bits - k) as nat) as int),
        ),
        // and, or, xor are handled by the caller on fixed-width values
        _ => 0,
    }
}

/// An `i32` binary operator.
pub open spec fn ibin32(op: IBin, x: u32, y: u32) -> u32 {
    match op {
        IBin::And => x & y,
        IBin::Or => x | y,
        IBin::Xor => x ^ y,
        _ => iarith(op, 32, x as int, y as int) as u32,
    }
}

/// An `i64` binary operator.
pub open spec fn ibin64(op: IBin, x: u64, y: u64) -> u64 {
    match op {
        IBin::And => x & y,
        IBin::Or => x | y,
        IBin::Xor => x ^ y,
        _ => iarith(op, 64, x as int, y as int) as u64,
    }
}

/// An integer comparison on `bits`-bit unsigned numbers (Wasm core §4.3.2:
/// `ieq`, `ine`, `ilt_s`, `ilt_u`, ...).
pub open spec fn icmp(op: ICmp, bits: nat, x: int, y: int) -> bool {
    match op {
        ICmp::Eq => x == y,
        ICmp::Ne => x != y,
        ICmp::LtS => signed_of(bits, x) < signed_of(bits, y),
        ICmp::LtU => x < y,
        ICmp::GtS => signed_of(bits, x) > signed_of(bits, y),
        ICmp::GtU => x > y,
        ICmp::LeS => signed_of(bits, x) <= signed_of(bits, y),
        ICmp::LeU => x <= y,
        ICmp::GeS => signed_of(bits, x) >= signed_of(bits, y),
        ICmp::GeU => x >= y,
    }
}

/// A comparison's result as an `i32` (Wasm core §4.4.1 `t.relop`: "push the
/// `i32` value `c`", 1 if true).
pub open spec fn bool_i32(b: bool) -> u32 {
    if b {
        1
    } else {
        0
    }
}

/// The `f64` bit pattern is a NaN (Wasm core §4.3.3 "Floating-Point
/// Operations", `nans`): exponent all ones, fraction non-zero.
pub open spec fn f64_is_nan(b: u64) -> bool {
    (b >> 52) & 0x7FF == 0x7FF && b & 0xF_FFFF_FFFF_FFFF != 0
}

/// The order key of a non-NaN `f64`: the sign-magnitude reading of its bits.
/// `+0` and `-0` both have key 0, so they compare equal; the keys of the
/// others order as the numbers do.
pub open spec fn f64_key(b: u64) -> int {
    let mag = (b & 0x7FFF_FFFF_FFFF_FFFF) as int;
    if b >> 63 == 1 {
        -mag
    } else {
        mag
    }
}

/// An `f64` comparison (Wasm core §4.3.3 `feq`, `fne`, `flt`, `fgt`, `fle`,
/// `fge`): false if either operand is a NaN, except `ne`, which is true.
pub open spec fn fcmp(op: FCmp, a: u64, b: u64) -> bool {
    if f64_is_nan(a) || f64_is_nan(b) {
        op == FCmp::Ne
    } else {
        match op {
            FCmp::Eq => f64_key(a) == f64_key(b),
            FCmp::Ne => f64_key(a) != f64_key(b),
            FCmp::Lt => f64_key(a) < f64_key(b),
            FCmp::Gt => f64_key(a) > f64_key(b),
            FCmp::Le => f64_key(a) <= f64_key(b),
            FCmp::Ge => f64_key(a) >= f64_key(b),
        }
    }
}

/// `fadd` (Wasm core §4.3.3), the rounded sum, with the NaN choice of
/// modelling choice 6. Uninterpreted.
pub uninterp spec fn f64_add(a: u64, b: u64) -> u64;

/// `fsub`. Uninterpreted.
pub uninterp spec fn f64_sub(a: u64, b: u64) -> u64;

/// `fmul`. Uninterpreted.
pub uninterp spec fn f64_mul(a: u64, b: u64) -> u64;

/// `fdiv`. Uninterpreted.
pub uninterp spec fn f64_div(a: u64, b: u64) -> u64;

/// `fsqrt`. Uninterpreted.
pub uninterp spec fn f64_sqrt(a: u64) -> u64;

/// `convert_{s,u}` (Wasm core §4.3.4 "Conversions", `convert_{N,M}^{sx}`):
/// the nearest `f64` to the integer `n`, ties to even. Uninterpreted.
pub uninterp spec fn f64_of_int(n: int) -> u64;

/// An `f64` binary operator.
pub open spec fn fbin(op: FBin, a: u64, b: u64) -> u64 {
    match op {
        FBin::Add => f64_add(a, b),
        FBin::Sub => f64_sub(a, b),
        FBin::Mul => f64_mul(a, b),
        FBin::Div => f64_div(a, b),
    }
}

/// A binary numeric instruction on two values; `None` if the operands are
/// not of the operator's type (the instruction is then stuck).
/// Wasm core §4.4.1 `t.binop` and `t.relop`.
pub open spec fn bin_eval(op: BinOp, a: Val, b: Val) -> Option<Val> {
    match (op, a, b) {
        // t.binop: "Let c be the result of binop_t(c1, c2). Push t.const c".
        (BinOp::I32(o), Val::I32(x), Val::I32(y)) => Some(Val::I32(ibin32(o, x, y))),
        (BinOp::I64(o), Val::I64(x), Val::I64(y)) => Some(Val::I64(ibin64(o, x, y))),
        (BinOp::F64(o), Val::F64(x), Val::F64(y)) => Some(Val::F64(fbin(o, x, y))),
        // t.relop: "Let c be the result of relop_t(c1, c2). Push i32.const c".
        (BinOp::I32Cmp(o), Val::I32(x), Val::I32(y)) => Some(
            Val::I32(bool_i32(icmp(o, 32, x as int, y as int))),
        ),
        (BinOp::I64Cmp(o), Val::I64(x), Val::I64(y)) => Some(
            Val::I32(bool_i32(icmp(o, 64, x as int, y as int))),
        ),
        (BinOp::F64Cmp(o), Val::F64(x), Val::F64(y)) => Some(Val::I32(bool_i32(fcmp(o, x, y)))),
        _ => None,
    }
}

/// A unary numeric instruction on a value; `None` if the operand is not of
/// the operator's type. Wasm core §4.4.1 `t.unop`, `t.testop`, `t2.cvtop`.
pub open spec fn un_eval(op: UnOp, a: Val) -> Option<Val> {
    match (op, a) {
        // t.testop, ieqz (§4.3.2): 1 if the operand is 0.
        (UnOp::I32Eqz, Val::I32(x)) => Some(Val::I32(bool_i32(x == 0))),
        (UnOp::I64Eqz, Val::I64(x)) => Some(Val::I32(bool_i32(x == 0))),
        // fneg, fabs (§4.3.3): flip, or clear, the sign bit; NaNs included.
        (UnOp::F64Neg, Val::F64(x)) => Some(Val::F64(x ^ 0x8000_0000_0000_0000)),
        (UnOp::F64Abs, Val::F64(x)) => Some(Val::F64(x & 0x7FFF_FFFF_FFFF_FFFF)),
        (UnOp::F64Sqrt, Val::F64(x)) => Some(Val::F64(f64_sqrt(x))),
        // wrap_{M,N} (§4.3.4): "i mod 2^N".
        (UnOp::I32WrapI64, Val::I64(x)) => Some(Val::I32((x & 0xFFFF_FFFF) as u32)),
        // extend_{M,N}^{sx} (§4.3.4): sx = s keeps the signed value.
        (UnOp::I64ExtendI32S, Val::I32(x)) => Some(Val::I64(wrap(64, signed_of(32, x as int)) as u64)),
        (UnOp::I64ExtendI32U, Val::I32(x)) => Some(Val::I64(x as u64)),
        // convert_{M,N}^{sx} (§4.3.4).
        (UnOp::F64ConvertI32S, Val::I32(x)) => Some(Val::F64(f64_of_int(signed_of(32, x as int)))),
        (UnOp::F64ConvertI32U, Val::I32(x)) => Some(Val::F64(f64_of_int(x as int))),
        (UnOp::F64ConvertI64S, Val::I64(x)) => Some(Val::F64(f64_of_int(signed_of(64, x as int)))),
        (UnOp::F64ConvertI64U, Val::I64(x)) => Some(Val::F64(f64_of_int(x as int))),
        // reinterpret_{t1,t2} (§4.3.4): the same bits.
        (UnOp::F64ReinterpretI64, Val::I64(x)) => Some(Val::F64(x)),
        (UnOp::I64ReinterpretF64, Val::F64(x)) => Some(Val::I64(x)),
        _ => None,
    }
}

// ---------------------------------------------------------------------
// The machine and the interpreter
// ---------------------------------------------------------------------

/// The machine state: the operand stack (top is the last element), the
/// locals and memory. Wasm core §4.2 "Runtime Structure" (frames hold the
/// locals; the store holds memory).
pub struct St {
    /// The operand stack, top last.
    pub stack: Seq<Val>,
    /// The locals.
    pub locals: Seq<Val>,
    /// Memory.
    pub mem: Mem,
}

/// What evaluating an instruction does (modelling choice 1).
pub enum Outcome {
    /// Finished and fell through, with the new state.
    Normal(St),
    /// A `br` to the label `n` levels out (0 is the innermost). The stack of
    /// the state is the stack of the code that branched.
    Branch(nat, St),
    /// An `exit` with its code and operand values, and the state after the
    /// operands were popped.
    Exit(nat, Seq<Val>, St),
    /// No meaning: a type error, or an access outside its region. The typing
    /// proves it unreachable.
    Stuck,
    /// The fuel ran out.
    OutOfFuel,
}

/// The top `k` elements of `s`.
pub open spec fn top<A>(s: Seq<A>, k: nat) -> Seq<A> {
    s.skip(s.len() - k)
}

/// `s` without its top `k` elements.
pub open spec fn below<A>(s: Seq<A>, k: nat) -> Seq<A> {
    s.take(s.len() - k)
}

impl St {
    /// The state with another stack.
    pub open spec fn with_stack(self, s: Seq<Val>) -> St {
        St { stack: s, locals: self.locals, mem: self.mem }
    }

    /// The state with another memory.
    pub open spec fn with_mem(self, m: Mem) -> St {
        St { stack: self.stack, locals: self.locals, mem: m }
    }

    /// The state with another set of locals.
    pub open spec fn with_locals(self, l: Seq<Val>) -> St {
        St { stack: self.stack, locals: l, mem: self.mem }
    }
}

/// The result of a block-like instruction's body, for the instruction that
/// is label 0 (Wasm core §4.4.8 "Blocks" and `br`): `base` is what was set
/// aside under the block's parameters, `arity` the number of values a
/// branch to this label carries, and `again` is what to do on a branch to
/// the label (`Some(i)` for a `loop`, which restarts at its start) or `None`
/// (a `block` or `if`, which continue after their end).
pub open spec fn finish_label(
    lay: Layout,
    base: Seq<Val>,
    arity: nat,
    restart: Option<Instr>,
    o: Outcome,
    fuel: nat,
) -> Outcome
    decreases fuel, 0nat,
{
    match o {
        // 'end' reached: all the body's stack is the results.
        Outcome::Normal(s) => Outcome::Normal(s.with_stack(base + s.stack)),
        Outcome::Branch(n, s) => {
            if n > 0 {
                // A branch to an outer label: pass it on.
                Outcome::Branch((n - 1) as nat, s)
            } else if s.stack.len() < arity {
                Outcome::Stuck
            } else {
                let carried = base + top(s.stack, arity);
                match restart {
                    // `loop`: branching to it restarts the loop.
                    Some(i) => {
                        if fuel == 0 {
                            Outcome::OutOfFuel
                        } else {
                            eval(lay, i, s.with_stack(carried), (fuel - 1) as nat)
                        }
                    },
                    // `block`, `if`: continue after `end`.
                    None => Outcome::Normal(s.with_stack(carried)),
                }
            }
        },
        other => other,
    }
}

/// Evaluate `i` in state `st` with at most `fuel` steps. Every call spends
/// one unit.
///
/// Each arm cites Wasm core 2.0. `Stuck` is returned where Wasm validation
/// would have excluded the case (a missing operand, an operand of the wrong
/// type, a bad local index).
pub open spec fn eval(lay: Layout, i: Instr, st: St, fuel: nat) -> Outcome
    decreases fuel, 1nat,
{
    if fuel == 0 {
        Outcome::OutOfFuel
    } else {
        let f = (fuel - 1) as nat;
        let n = st.stack.len();
        match i {
            // Wasm core §4.4.8 `nop`: "Do nothing."
            Instr::Nop => Outcome::Normal(st),
            // Wasm core §4.4.8 instruction sequences: the first, then the
            // rest, unless the first branched or exited.
            Instr::Then(a, b) => {
                match eval(lay, *a, st, f) {
                    Outcome::Normal(s1) => eval(lay, *b, s1, f),
                    other => other,
                }
            },
            // Wasm core §4.4.1 `t.const c`: "Push the value t.const c".
            Instr::Const(v) => Outcome::Normal(st.with_stack(st.stack.push(v))),
            // Wasm core §4.4.4 `local.get x`: "Push the value val to the stack".
            Instr::LocalGet(x) => {
                if x < st.locals.len() {
                    Outcome::Normal(st.with_stack(st.stack.push(st.locals[x as int])))
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.4 `local.set x`: "Pop the value val from the
            // stack. Replace the local".
            Instr::LocalSet(x) => {
                if n >= 1 && x < st.locals.len() {
                    Outcome::Normal(
                        St {
                            stack: st.stack.drop_last(),
                            locals: st.locals.update(x as int, st.stack.last()),
                            mem: st.mem,
                        },
                    )
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.4 `local.tee x`: "Assert: ... a value val on the
            // top of the stack. Push val, then `local.set x`".
            Instr::LocalTee(x) => {
                if n >= 1 && x < st.locals.len() {
                    Outcome::Normal(st.with_locals(st.locals.update(x as int, st.stack.last())))
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.3 `drop`: "Pop the value val from the stack."
            Instr::Drop => {
                if n >= 1 {
                    Outcome::Normal(st.with_stack(st.stack.drop_last()))
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.3 `select`: pop c (an i32), then val2, then
            // val1; "If c is not 0, push val1, else push val2".
            Instr::Select => {
                if n >= 3 {
                    match st.stack[n - 1] {
                        Val::I32(c) => {
                            let v1 = st.stack[n - 3];
                            let v2 = st.stack[n - 2];
                            Outcome::Normal(
                                st.with_stack(
                                    below(st.stack, 3).push(if c != 0 {
                                        v1
                                    } else {
                                        v2
                                    }),
                                ),
                            )
                        },
                        _ => Outcome::Stuck,
                    }
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.1 `t.binop`, `t.relop`: pop c2, then c1.
            Instr::Bin(op) => {
                if n >= 2 {
                    match bin_eval(op, st.stack[n - 2], st.stack[n - 1]) {
                        Some(v) => Outcome::Normal(st.with_stack(below(st.stack, 2).push(v))),
                        None => Outcome::Stuck,
                    }
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.1 `t.unop`, `t.testop`, `t2.cvtop`.
            Instr::Un(op) => {
                if n >= 1 {
                    match un_eval(op, st.stack[n - 1]) {
                        Some(v) => Outcome::Normal(st.with_stack(below(st.stack, 1).push(v))),
                        None => Outcome::Stuck,
                    }
                } else {
                    Outcome::Stuck
                }
            },
            // LIR's `bounds_check` (modelling choice 5): pop the index; push
            // it back if `i + size <= bound`, else exit with the code.
            Instr::BoundsCheck { region, size, code } => {
                if n >= 1 && region < lay.len() {
                    match st.stack[n - 1] {
                        Val::I64(ix) => {
                            if ix as nat + size <= lay[region as int].bound {
                                Outcome::Normal(st)
                            } else {
                                Outcome::Exit(code, seq![], st.with_stack(below(st.stack, 1)))
                            }
                        },
                        _ => Outcome::Stuck,
                    }
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.6 `t.load`: pop the address i; "let ea be i +
            // offset"; "If ea + N/8 is larger than the length of mem.data,
            // trap"; else read the bytes and push the value. Here the
            // address is `base + masked(bound, i)` and the out-of-region
            // case is Stuck (modelling choice 4).
            Instr::Load { region, ty } => {
                if n >= 1 && region < lay.len() && ty_size(ty) > 0 {
                    match st.stack[n - 1] {
                        Val::I64(ix) => {
                            let r = lay[region as int];
                            if ix as nat + ty_size(ty) <= r.bound {
                                let a = r.base + masked(r.bound, ix as nat);
                                Outcome::Normal(
                                    st.with_stack(
                                        below(st.stack, 1).push(
                                            val_of_bits(ty, read_le(st.mem, a, ty_size(ty))),
                                        ),
                                    ),
                                )
                            } else {
                                Outcome::Stuck
                            }
                        },
                        _ => Outcome::Stuck,
                    }
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.6 `t.store`: pop the value c, then the address
            // i; write `bytes_t(c)` at `ea`.
            Instr::Store { region, ty } => {
                if n >= 2 && region < lay.len() && ty_size(ty) > 0 && val_has_base_ty(
                    st.stack[n - 1],
                    ty,
                ) {
                    match st.stack[n - 2] {
                        Val::I64(ix) => {
                            let r = lay[region as int];
                            if ix as nat + ty_size(ty) <= r.bound {
                                let a = r.base + masked(r.bound, ix as nat);
                                Outcome::Normal(
                                    st.with_stack(below(st.stack, 2)).with_mem(
                                        write_le(
                                            st.mem,
                                            a,
                                            val_bits(st.stack[n - 1]),
                                            ty_size(ty),
                                        ),
                                    ),
                                )
                            } else {
                                Outcome::Stuck
                            }
                        },
                        _ => Outcome::Stuck,
                    }
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.8 `block bt instr* end`: "Let L be the label
            // whose arity is m [the results] ... Enter the block with the
            // values val^n [the parameters] on the stack".
            Instr::Block(bt, body) => {
                if n >= bt.params.len() {
                    let base = below(st.stack, bt.params.len());
                    let o = eval(lay, *body, st.with_stack(top(st.stack, bt.params.len())), f);
                    finish_label(lay, base, bt.results.len(), None, o, f)
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.8 `loop bt instr* end`: the label's arity is the
            // number of *parameters* (a branch restarts the loop).
            Instr::Loop(bt, body) => {
                if n >= bt.params.len() {
                    let base = below(st.stack, bt.params.len());
                    let o = eval(lay, *body, st.with_stack(top(st.stack, bt.params.len())), f);
                    finish_label(lay, base, bt.params.len(), Some(Instr::Loop(bt, body)), o, f)
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.8 `if bt instr1* else instr2* end`: "Pop the
            // value i32.const c from the stack. If c is non-zero, ... block
            // bt instr1* end, else ... block bt instr2* end."
            Instr::If(bt, t, e) => {
                if n >= 1 {
                    match st.stack[n - 1] {
                        Val::I32(c) => eval(
                            lay,
                            Instr::Block(bt, if c != 0 {
                                t
                            } else {
                                e
                            }),
                            st.with_stack(below(st.stack, 1)),
                            f,
                        ),
                        _ => Outcome::Stuck,
                    }
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.8 `br l`: the branch itself; the label that is
            // `l` levels out handles it (see `finish_label`).
            Instr::Br(l) => Outcome::Branch(l, st),
            // Wasm core §4.4.8 `br_if l`: "Pop the value i32.const c. If c is
            // non-zero, then branch l; else do nothing."
            Instr::BrIf(l) => {
                if n >= 1 {
                    match st.stack[n - 1] {
                        Val::I32(c) => {
                            let s1 = st.with_stack(below(st.stack, 1));
                            if c != 0 {
                                Outcome::Branch(l, s1)
                            } else {
                                Outcome::Normal(s1)
                            }
                        },
                        _ => Outcome::Stuck,
                    }
                } else {
                    Outcome::Stuck
                }
            },
            // Wasm core §4.4.8 `br_table l* l_N`: "If i is less than the
            // length of l*, then branch l*[i]; else branch l_N."
            Instr::BrTable(ls, d) => {
                if n >= 1 {
                    match st.stack[n - 1] {
                        Val::I32(c) => Outcome::Branch(
                            if (c as nat) < ls.len() {
                                ls[c as int]
                            } else {
                                d
                            },
                            st.with_stack(below(st.stack, 1)),
                        ),
                        _ => Outcome::Stuck,
                    }
                } else {
                    Outcome::Stuck
                }
            },
            // LIR's `exit` (modelling choice 3): stop with the code and the
            // top values.
            Instr::Exit(code, tys) => {
                if n >= tys.len() {
                    Outcome::Exit(code, top(st.stack, tys.len()), st.with_stack(below(st.stack, tys.len())))
                } else {
                    Outcome::Stuck
                }
            },
        }
    }
}

/// Run a function body: the body is `body`, with label 0 being the function's
/// own end, so a `br` to it is a return (Wasm core §4.4.9 "Function Calls":
/// the function body is a block whose label is the return). The state is the
/// entry state: the stack holds the arguments, the locals are the
/// parameters and the declared locals.
pub open spec fn run(lay: Layout, body: Instr, st: St, fuel: nat) -> Outcome {
    match eval(lay, body, st, fuel) {
        Outcome::Branch(n, s) => if n == 0 {
            Outcome::Normal(s)
        } else {
            Outcome::Stuck
        },
        other => other,
    }
}

} // verus!
