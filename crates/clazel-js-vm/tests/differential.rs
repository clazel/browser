//! A differential test: the interpreter against a model of `spec fn step`.
//!
//! `spec::step` is a Verus `spec fn`: it does not run, so there is no
//! executable form of it to compare against. This test therefore carries
//! `model`, a second transcription of `spec::fast_step` for the core ops and
//! the guarded ops on their fast paths, written from the spec's text over raw
//! `u64` bit patterns (the spec's own representation) with integer arithmetic
//! in `i64`/`i128` where `src/numeric.rs` uses checked `i32` operations and
//! `rem_euclid`, so that the two are not copies of each other. The spec's
//! uninterpreted rounding (`f64_add_finite` and the others) is the hardware's
//! `f64`, the assumption `spec.rs` lists.
//!
//! Random straight-line programs (with forward jumps) over eight registers
//! are built directly as bytecode, run by the interpreter and by the model,
//! and every register's bits are compared, so the encoding rule (int32 versus
//! double) is checked, not only the Number. The generator keeps the operands
//! of an arithmetic op Numbers, so every op takes its fast path, where the
//! spec defines the result.
//!
//! What this is not: a proof that the interpreter refines `step`. It covers
//! the ops listed in `OPS` below, on 8 registers, with edge-case operands; the
//! handler ops (calls, properties, globals) are outside it, as `step` leaves
//! them uninterpreted.

use clazel_js_heap::value::Value;
use clazel_js_vm::bytecode::{
    Const, FunctionCode, FunctionKind, Instr, Program, Span, check_program,
};
use clazel_js_vm::interp::{Config, Vm};

/// The model of `spec::fast_step`.
mod model {
    pub const UNDEFINED: u64 = 0xFFFA_0000_0000_0000;
    pub const NULL: u64 = 0xFFFA_0000_0000_0001;
    pub const FALSE: u64 = 0xFFFA_0000_0000_0002;
    pub const TRUE: u64 = 0xFFFA_0000_0000_0003;
    pub const CANON_NAN: u64 = 0x7FF8_0000_0000_0000;

    pub fn enc_int32(i: i32) -> u64 {
        0xFFF9_0000_0000_0000 | u64::from(i as u32)
    }
    pub fn enc_bool(b: bool) -> u64 {
        if b { TRUE } else { FALSE }
    }
    pub fn enc_double(bits: u64) -> u64 {
        if f64::from_bits(bits).is_nan() {
            CANON_NAN
        } else {
            bits
        }
    }
    pub fn is_int32(v: u64) -> bool {
        v >> 48 == 0xFFF9 && (v >> 32) & 0xFFFF == 0
    }
    pub fn is_double(v: u64) -> bool {
        v >> 48 < 0xFFF9
    }
    pub fn is_number(v: u64) -> bool {
        is_int32(v) || is_double(v)
    }
    pub fn int32_of(v: u64) -> i64 {
        i64::from(v as u32 as i32)
    }
    /// `spec::num_bits`: the double that represents the same Number.
    pub fn num_bits(v: u64) -> u64 {
        if is_int32(v) {
            (int32_of(v) as f64).to_bits()
        } else {
            v
        }
    }
    pub fn fits_i32(n: i64) -> bool {
        (-2_147_483_648..=2_147_483_647).contains(&n)
    }
    fn f(v: u64) -> f64 {
        f64::from_bits(num_bits(v))
    }

    // The int32 operands are widened to `i64`, where no operation below can
    // overflow (|a * b| <= 2^62), so the wrapping forms are the exact ones.
    pub fn arith_add(a: u64, b: u64) -> u64 {
        let sum = int32_of(a).wrapping_add(int32_of(b));
        if is_int32(a) && is_int32(b) && fits_i32(sum) {
            enc_int32(sum as i32)
        } else {
            enc_double((f(a) + f(b)).to_bits())
        }
    }
    pub fn arith_sub(a: u64, b: u64) -> u64 {
        let diff = int32_of(a).wrapping_sub(int32_of(b));
        if is_int32(a) && is_int32(b) && fits_i32(diff) {
            enc_int32(diff as i32)
        } else {
            enc_double((f(a) - f(b)).to_bits())
        }
    }
    pub fn arith_mul(a: u64, b: u64) -> u64 {
        let p = int32_of(a).wrapping_mul(int32_of(b));
        if is_int32(a)
            && is_int32(b)
            && fits_i32(p)
            && !(p == 0 && (int32_of(a) < 0 || int32_of(b) < 0))
        {
            enc_int32(p as i32)
        } else {
            enc_double((f(a) * f(b)).to_bits())
        }
    }
    pub fn arith_div(a: u64, b: u64) -> u64 {
        enc_double((f(a) / f(b)).to_bits())
    }
    /// The truncated remainder of two integers, `d != 0` (`spec::int_rem_trunc`).
    fn int_rem_trunc(n: i64, d: i64) -> i64 {
        let m = n.abs().checked_rem(d.abs()).unwrap_or(0);
        if n < 0 { m.wrapping_neg() } else { m }
    }
    pub fn arith_mod(a: u64, b: u64) -> u64 {
        if is_int32(a)
            && is_int32(b)
            && int32_of(b) != 0
            && !(int_rem_trunc(int32_of(a), int32_of(b)) == 0 && int32_of(a) < 0)
        {
            enc_int32(int_rem_trunc(int32_of(a), int32_of(b)) as i32)
        } else {
            enc_double((f(a) % f(b)).to_bits())
        }
    }
    pub fn arith_neg(a: u64) -> u64 {
        if is_int32(a) && int32_of(a) != 0 && int32_of(a) != -2_147_483_648 {
            enc_int32(int32_of(a).wrapping_neg() as i32)
        } else {
            enc_double((-f(a)).to_bits())
        }
    }

    /// `spec::f64_int32bit`: the integral part of a finite non-zero double,
    /// modulo 2^32, from the bit fields (not through `f64` arithmetic).
    fn int32bit(bits: u64) -> u32 {
        let neg = bits >> 63 == 1;
        let exp = ((bits >> 52) & 0x7FF) as i64;
        let frac = bits & 0xF_FFFF_FFFF_FFFF;
        let (m, e) = if exp == 0 {
            (frac, -1074i64)
        } else {
            (frac | (1 << 52), exp.wrapping_sub(1075))
        };
        let magnitude: u128 = if e >= 0 {
            u128::from(m)
                .checked_shl(e as u32)
                .filter(|_| e < 32)
                .unwrap_or(0)
        } else {
            m.checked_shr(e.unsigned_abs() as u32).map_or(0, u128::from)
        };
        let low = (magnitude & 0xFFFF_FFFF) as u32;
        if neg { low.wrapping_neg() } else { low }
    }
    fn finite_nonzero(bits: u64) -> bool {
        let x = f64::from_bits(bits);
        x.is_finite() && x != 0.0
    }
    pub fn to_int32(v: u64) -> i32 {
        let b = num_bits(v);
        if finite_nonzero(b) {
            int32bit(b) as i32
        } else {
            0
        }
    }
    pub fn to_uint32(v: u64) -> u32 {
        let b = num_bits(v);
        if finite_nonzero(b) { int32bit(b) } else { 0 }
    }
    fn wrap_i32(n: i64) -> i32 {
        n.rem_euclid(1i64 << 32) as u32 as i32
    }

    pub fn bit_and(a: u64, b: u64) -> u64 {
        enc_int32(to_int32(a) & to_int32(b))
    }
    pub fn bit_or(a: u64, b: u64) -> u64 {
        enc_int32(to_int32(a) | to_int32(b))
    }
    pub fn bit_xor(a: u64, b: u64) -> u64 {
        enc_int32(to_int32(a) ^ to_int32(b))
    }
    pub fn shl(a: u64, b: u64) -> u64 {
        let count = to_uint32(b) & 31;
        enc_int32(wrap_i32(i64::from(to_int32(a)).wrapping_mul(1i64 << count)))
    }
    pub fn shr(a: u64, b: u64) -> u64 {
        let count = to_uint32(b) & 31;
        enc_int32(i64::from(to_int32(a)).div_euclid(1i64 << count) as i32)
    }
    pub fn ushr(a: u64, b: u64) -> u64 {
        let count = to_uint32(b) & 31;
        let n = i64::from(to_uint32(a))
            .checked_div(1i64 << count)
            .unwrap_or(0);
        if fits_i32(n) {
            enc_int32(n as i32)
        } else {
            enc_double((n as f64).to_bits())
        }
    }
    pub fn bit_not(a: u64) -> u64 {
        enc_int32((-1i64).wrapping_sub(i64::from(to_int32(a))) as i32)
    }

    /// `number_less_than`: `None` when either is NaN.
    fn less_than(x: u64, y: u64) -> Option<bool> {
        f(x).partial_cmp(&f(y))
            .map(|o| o == std::cmp::Ordering::Less)
    }
    pub fn rel_lt(x: u64, y: u64) -> bool {
        less_than(x, y).unwrap_or(false)
    }
    pub fn rel_gt(x: u64, y: u64) -> bool {
        less_than(y, x).unwrap_or(false)
    }
    pub fn rel_le(x: u64, y: u64) -> bool {
        less_than(y, x).map(|r| !r).unwrap_or(false)
    }
    pub fn rel_ge(x: u64, y: u64) -> bool {
        less_than(x, y).map(|r| !r).unwrap_or(false)
    }

    /// `spec::strict_eq_fast` on values with no heap references.
    pub fn strict_eq(a: u64, b: u64) -> bool {
        if is_number(a) && is_number(b) {
            f(a) == f(b)
        } else {
            a == b
        }
    }
    /// `spec::to_boolean_fast`.
    pub fn to_boolean(v: u64) -> bool {
        if is_int32(v) {
            int32_of(v) != 0
        } else if is_double(v) {
            let x = f64::from_bits(v);
            !(x == 0.0 || x.is_nan())
        } else {
            v == TRUE
        }
    }
}

/// What a register holds, for the generator.
#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Number,
    Other,
}

fn kind_of(kinds: &[Kind], r: u32) -> Kind {
    kinds.get(r as usize).copied().unwrap_or(Kind::Other)
}

fn set_kind(kinds: &mut [Kind], r: u32, k: Kind) {
    if let Some(slot) = kinds.get_mut(r as usize) {
        *slot = k;
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next().checked_rem(n).unwrap_or(0)
    }
    fn pick<T: Copy + Default>(&mut self, xs: &[T]) -> T {
        let i = self.below(xs.len() as u64) as usize;
        xs.get(i).copied().unwrap_or_default()
    }
}

const NREGS: u32 = 8;
const INTS: [i32; 14] = [
    0,
    1,
    -1,
    2,
    7,
    31,
    32,
    33,
    65_536,
    46_341,
    i32::MAX,
    i32::MIN,
    1 << 30,
    -(1 << 30),
];
const DOUBLES: [f64; 16] = [
    0.5,
    -0.5,
    -0.0,
    0.0,
    1.5,
    -2.5,
    1e300,
    1e-300,
    2_147_483_648.0,
    -2_147_483_649.0,
    4_294_967_296.5,
    4_294_967_295.0,
    9_007_199_254_740_992.0,
    f64::INFINITY,
    f64::NEG_INFINITY,
    123_456_789.75,
];

/// The model's loader: an integral Number in int32 range other than `-0` is
/// an int32 (the documented rule of `Vm::load`), else the double.
fn model_const(bits: u64) -> u64 {
    let d = f64::from_bits(bits);
    if d == d.trunc() && d.abs() < 2_147_483_648.0 && bits != (-0.0f64).to_bits() {
        model::enc_int32(d as i32)
    } else {
        bits
    }
}

/// One generated program, and the model's final registers.
fn generate(seed: u64, len: usize) -> (Program, [u64; NREGS as usize]) {
    let mut rng = Rng(seed | 1);
    let mut consts = Vec::new();
    for d in DOUBLES {
        consts.push(Const::Number(d.to_bits()));
    }
    let mut instrs: Vec<Instr> = Vec::new();
    let mut kinds = [Kind::Other; NREGS as usize];
    // Every register starts as a Number, so any op may use any register.
    for r in 0..NREGS {
        if rng.below(2) == 0 {
            instrs.push(Instr::LoadInt {
                dst: r,
                imm: rng.pick(&INTS),
            });
        } else {
            instrs.push(Instr::LoadConst {
                dst: r,
                k: rng.below(DOUBLES.len() as u64) as u32,
            });
        }
        set_kind(&mut kinds, r, Kind::Number);
    }
    let numbers = |kinds: &[Kind; NREGS as usize]| -> Vec<u32> {
        (0..NREGS)
            .filter(|&r| kind_of(kinds, r) == Kind::Number)
            .collect()
    };
    while instrs.len() < len {
        let nums = numbers(&kinds);
        let any = |rng: &mut Rng| rng.below(u64::from(NREGS)) as u32;
        let dst = any(&mut rng);
        if nums.is_empty() {
            // No register holds a Number: make one, so every operand pick is
            // a Number and every arithmetic op takes its fast path.
            instrs.push(Instr::LoadInt {
                dst,
                imm: rng.pick(&INTS),
            });
            set_kind(&mut kinds, dst, Kind::Number);
            continue;
        }
        let (a, b) = (rng.pick(&nums), rng.pick(&nums));
        let (ins, kind) = match rng.below(26) {
            0 => (Instr::Add { dst, a, b }, Kind::Number),
            1 => (Instr::Sub { dst, a, b }, Kind::Number),
            2 => (Instr::Mul { dst, a, b }, Kind::Number),
            3 => (Instr::Div { dst, a, b }, Kind::Number),
            4 => (Instr::Mod { dst, a, b }, Kind::Number),
            5 => (Instr::Neg { dst, src: a }, Kind::Number),
            6 => (Instr::Inc { dst, src: a }, Kind::Number),
            7 => (Instr::Dec { dst, src: a }, Kind::Number),
            8 => (Instr::BitAnd { dst, a, b }, Kind::Number),
            9 => (Instr::BitOr { dst, a, b }, Kind::Number),
            10 => (Instr::BitXor { dst, a, b }, Kind::Number),
            11 => (Instr::Shl { dst, a, b }, Kind::Number),
            12 => (Instr::Shr { dst, a, b }, Kind::Number),
            13 => (Instr::UShr { dst, a, b }, Kind::Number),
            14 => (Instr::BitNot { dst, src: a }, Kind::Number),
            15 => (Instr::Lt { dst, a, b }, Kind::Other),
            16 => (Instr::Le { dst, a, b }, Kind::Other),
            17 => (Instr::Gt { dst, a, b }, Kind::Other),
            18 => (Instr::Ge { dst, a, b }, Kind::Other),
            19 => {
                let (x, y) = (any(&mut rng), any(&mut rng));
                if rng.below(2) == 0 {
                    (Instr::StrictEq { dst, a: x, b: y }, Kind::Other)
                } else {
                    (Instr::StrictNe { dst, a: x, b: y }, Kind::Other)
                }
            }
            20 => (
                Instr::Not {
                    dst,
                    src: any(&mut rng),
                },
                Kind::Other,
            ),
            21 => (Instr::ToNumeric { dst, src: a }, Kind::Number),
            22 => match rng.below(5) {
                0 => (Instr::LoadUndefined { dst }, Kind::Other),
                1 => (Instr::LoadNull { dst }, Kind::Other),
                2 => (
                    Instr::LoadBool {
                        dst,
                        flag: rng.below(2) == 0,
                    },
                    Kind::Other,
                ),
                3 => (
                    Instr::LoadInt {
                        dst,
                        imm: rng.pick(&INTS),
                    },
                    Kind::Number,
                ),
                _ => (
                    Instr::LoadConst {
                        dst,
                        k: rng.below(DOUBLES.len() as u64) as u32,
                    },
                    Kind::Number,
                ),
            },
            23 => {
                let src = any(&mut rng);
                (Instr::Move { dst, src }, kind_of(&kinds, src))
            }
            24 => {
                // A forward jump over the next one to three ops (the target
                // is fixed up below); the kinds after it are those of the
                // fall-through path only if the ops it skips keep them, so
                // the generator uses the weaker of both: it emits the jump,
                // and the skipped ops are then limited to ones that do not
                // change a register's kind.
                let src = any(&mut rng);
                (
                    Instr::JumpIfTrue {
                        cond: src,
                        target: 0,
                    },
                    kind_of(&kinds, dst),
                )
            }
            _ => {
                let src = any(&mut rng);
                (
                    Instr::JumpIfNullish { src, target: 0 },
                    kind_of(&kinds, dst),
                )
            }
        };
        let is_jump = ins.target().is_some();
        instrs.push(ins.clone());
        if is_jump {
            // The ops the jump may skip write the same kinds as before: use
            // `Move` of a register onto itself and plain arithmetic on
            // Numbers into Number registers.
            let skip = (rng.below(3) as usize).saturating_add(1);
            let n = instrs.len();
            for _ in 0..skip {
                let nums = numbers(&kinds);
                let d = rng.pick(&nums);
                let (p, q) = (rng.pick(&nums), rng.pick(&nums));
                instrs.push(match rng.below(3) {
                    0 => Instr::Add { dst: d, a: p, b: q },
                    1 => Instr::Mul { dst: d, a: p, b: q },
                    _ => Instr::BitXor { dst: d, a: p, b: q },
                });
            }
            let target = u32::try_from(instrs.len()).unwrap_or(0);
            if let Some(j) = instrs.get_mut(n.saturating_sub(1)) {
                j.set_target(target);
            }
        } else {
            set_kind(&mut kinds, dst, kind);
        }
    }
    instrs.push(Instr::Return { src: 0 });
    // The jump targets of a trailing jump point at the Return, which exists.
    let n = instrs.len();
    let program = Program {
        functions: vec![FunctionCode {
            name: Vec::new(),
            kind: FunctionKind::Script,
            strict: false,
            span: Span { start: 0, end: 0 },
            nparams: 0,
            length: 0,
            nregs: NREGS,
            nics: 0,
            instrs,
            spans: vec![Span { start: 0, end: 0 }; n],
            consts,
            handlers: Vec::new(),
        }],
        main: 0,
    };
    let regs = model_run(&program);
    (program, regs)
}

/// The model's run of the (single, straight-line) function.
fn model_run(p: &Program) -> [u64; NREGS as usize] {
    let mut regs = [model::UNDEFINED; NREGS as usize];
    let mut pc = 0usize;
    macro_rules! rd {
        ($i:expr) => {
            regs.get($i as usize).copied().unwrap_or(model::UNDEFINED)
        };
    }
    macro_rules! wr {
        ($i:expr, $v:expr) => {{
            let v = $v;
            if let Some(slot) = regs.get_mut($i as usize) {
                *slot = v;
            }
        }};
    }
    let Some(f) = p.functions.first() else {
        return regs;
    };
    while let Some(ins) = f.instrs.get(pc) {
        let mut next = pc.saturating_add(1);
        match *ins {
            Instr::Move { dst, src } => wr!(dst, rd!(src)),
            Instr::LoadConst { dst, k } => {
                if let Some(Const::Number(bits)) = f.consts.get(k as usize) {
                    wr!(dst, model_const(*bits));
                }
            }
            Instr::LoadInt { dst, imm } => wr!(dst, model::enc_int32(imm)),
            Instr::LoadUndefined { dst } => wr!(dst, model::UNDEFINED),
            Instr::LoadNull { dst } => wr!(dst, model::NULL),
            Instr::LoadBool { dst, flag } => wr!(dst, model::enc_bool(flag)),
            Instr::JumpIfTrue { cond, target } => {
                if model::to_boolean(rd!(cond)) {
                    next = target as usize;
                }
            }
            Instr::JumpIfNullish { src, target } => {
                if rd!(src) == model::UNDEFINED || rd!(src) == model::NULL {
                    next = target as usize;
                }
            }
            Instr::Add { dst, a, b } => wr!(dst, model::arith_add(rd!(a), rd!(b))),
            Instr::Sub { dst, a, b } => wr!(dst, model::arith_sub(rd!(a), rd!(b))),
            Instr::Mul { dst, a, b } => wr!(dst, model::arith_mul(rd!(a), rd!(b))),
            Instr::Div { dst, a, b } => wr!(dst, model::arith_div(rd!(a), rd!(b))),
            Instr::Mod { dst, a, b } => wr!(dst, model::arith_mod(rd!(a), rd!(b))),
            Instr::Neg { dst, src } => wr!(dst, model::arith_neg(rd!(src))),
            Instr::Inc { dst, src } => wr!(dst, model::arith_add(rd!(src), model::enc_int32(1))),
            Instr::Dec { dst, src } => wr!(dst, model::arith_sub(rd!(src), model::enc_int32(1))),
            Instr::BitAnd { dst, a, b } => wr!(dst, model::bit_and(rd!(a), rd!(b))),
            Instr::BitOr { dst, a, b } => wr!(dst, model::bit_or(rd!(a), rd!(b))),
            Instr::BitXor { dst, a, b } => wr!(dst, model::bit_xor(rd!(a), rd!(b))),
            Instr::Shl { dst, a, b } => wr!(dst, model::shl(rd!(a), rd!(b))),
            Instr::Shr { dst, a, b } => wr!(dst, model::shr(rd!(a), rd!(b))),
            Instr::UShr { dst, a, b } => wr!(dst, model::ushr(rd!(a), rd!(b))),
            Instr::BitNot { dst, src } => wr!(dst, model::bit_not(rd!(src))),
            Instr::Lt { dst, a, b } => wr!(dst, model::enc_bool(model::rel_lt(rd!(a), rd!(b)))),
            Instr::Le { dst, a, b } => wr!(dst, model::enc_bool(model::rel_le(rd!(a), rd!(b)))),
            Instr::Gt { dst, a, b } => wr!(dst, model::enc_bool(model::rel_gt(rd!(a), rd!(b)))),
            Instr::Ge { dst, a, b } => wr!(dst, model::enc_bool(model::rel_ge(rd!(a), rd!(b)))),
            Instr::StrictEq { dst, a, b } => {
                wr!(dst, model::enc_bool(model::strict_eq(rd!(a), rd!(b))));
            }
            Instr::StrictNe { dst, a, b } => {
                wr!(dst, model::enc_bool(!model::strict_eq(rd!(a), rd!(b))));
            }
            Instr::Not { dst, src } => wr!(dst, model::enc_bool(!model::to_boolean(rd!(src)))),
            Instr::ToNumeric { dst, src } => wr!(dst, rd!(src)),
            Instr::Return { .. } => break,
            _ => break,
        }
        pc = next;
    }
    regs
}

/// Runs a generated program in the interpreter and compares every register.
fn check(seed: u64, len: usize) -> Result<(), String> {
    let (program, expected) = generate(seed, len);
    check_program(&program).map_err(|e| format!("seed {seed}: ill-formed: {e}"))?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let script = vm
        .load(&program)
        .map_err(|e| format!("seed {seed}: {e:?}"))?;
    vm.run(&script).map_err(|e| format!("seed {seed}: {e:?}"))?;
    for (r, want) in expected.iter().enumerate() {
        // The script's frame is at slot 0: four header slots, then registers.
        let got = vm
            .region_slot(r.saturating_add(4))
            .ok_or_else(|| format!("seed {seed}: no slot for register {r}"))?;
        if got.bits() != *want {
            return Err(format!(
                "seed {seed}, register {r}: interpreter {:#018x} ({:?}), model {:#018x}\nprogram: {:#?}",
                got.bits(),
                got.decode(),
                want,
                program.functions.first().map(|f| &f.instrs)
            ));
        }
    }
    Ok(())
}

#[test]
fn the_interpreter_matches_the_model_of_step() -> Result<(), String> {
    let (programs, len) = if cfg!(miri) { (6, 30) } else { (3000, 60) };
    for seed in 0..programs as u64 {
        check(
            seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1),
            len,
        )?;
    }
    Ok(())
}

#[test]
fn the_model_is_checked_by_known_results() {
    // The model is itself a transcription: pin it to values worked out by hand
    // from ECMA-262, so that a mistake common to the model and the
    // interpreter's `numeric.rs` would have to also be a mistake of the
    // standard's worked examples.
    use model::*;
    assert_eq!(
        arith_add(enc_int32(i32::MAX), enc_int32(1)),
        (2_147_483_648.0f64).to_bits()
    );
    assert_eq!(arith_mul(enc_int32(0), enc_int32(-3)), (-0.0f64).to_bits());
    assert_eq!(arith_mod(enc_int32(-4), enc_int32(2)), (-0.0f64).to_bits());
    assert_eq!(
        arith_neg(enc_int32(i32::MIN)),
        (2_147_483_648.0f64).to_bits()
    );
    assert_eq!(to_int32(4_294_967_301.0f64.to_bits()), 5);
    assert_eq!(to_int32((-1.9f64).to_bits()), -1);
    assert_eq!(to_int32(1e300f64.to_bits()), 0);
    assert_eq!(to_uint32((-1.0f64).to_bits()), u32::MAX);
    assert_eq!(shl(enc_int32(1), enc_int32(31)), enc_int32(i32::MIN));
    assert_eq!(shr(enc_int32(-9), enc_int32(1)), enc_int32(-5));
    assert_eq!(
        ushr(enc_int32(-1), enc_int32(0)),
        4_294_967_295.0f64.to_bits()
    );
    assert_eq!(bit_not(enc_int32(5)), enc_int32(-6));
    assert!(!rel_lt(CANON_NAN, enc_int32(1)) && !rel_ge(CANON_NAN, enc_int32(1)));
    assert!(rel_le(enc_int32(0), (-0.0f64).to_bits()));
    assert!(strict_eq(enc_int32(0), (-0.0f64).to_bits()));
    assert!(!strict_eq(CANON_NAN, CANON_NAN));
    assert_eq!(
        Value::from_bits(arith_div(enc_int32(1), enc_int32(0))).map(Value::bits),
        Some(f64::INFINITY.to_bits())
    );
}
