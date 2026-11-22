//! Kani harnesses, compiled only under `cargo kani`.
//!
//! Small pieces of the interpreter (item 7.8, first slice), each finishing in
//! seconds to minutes. They are evidence, not a tier claim: the crate stays at
//! tier 0, as `Cargo.toml` says.
//!
//! - [`add_sub_mul_int32`]: for any two int32 operands, `+`, `-` and `*`
//!   give the int32 exactly when the exact result fits (and is not `-0` for
//!   `*`), and a double otherwise: `spec::arith_add`, `arith_sub`,
//!   `arith_mul`'s encoding rule. Overflow never panics.
//! - [`neg_int32`], [`rem_int32`]: unary minus and `%` on int32, including the
//!   two operand pairs that overflow `i32` arithmetic (`-(-2^31)`,
//!   `-2^31 % -1`).
//! - [`shifts_int32`]: `<<`, `>>`, `>>>` on int32 against the exact integer
//!   results of §6.1.6.1.9 to .11.
//! - [`frame_indexing`]: for any frame base, register and slot, the
//!   region accessors return `Ok` for a slot inside the region and `Err`
//!   otherwise, and never panic or overflow, over regions of up to 6 slots.
//! - [`return_address_round_trip`]: `unpack_ret` inverts `pack_ret` for every
//!   base and `pc` below `RET_LIMIT`, and `pack_ret` refuses the rest.
//! - [`argc_round_trip`]: `dec_argc` inverts `enc_argc`.
//!
//! Not covered: doubles (CBMC's floating-point reasoning is too slow for the
//! bitwise conversions; `ToInt32` on doubles is covered by the differential
//! test), and the loop and the handlers, which touch the heap's collections.

use crate::frame::{
    HDR_SLOTS, KIND_CONSTRUCT, KIND_PLAIN, KIND_SUSPENDABLE, RET_LIMIT, Region, Ret, dec_argc,
    enc_argc, pack_ret, reg_slot, unpack_ret,
};
use crate::numeric::{self, Num};
use clazel_js_heap::value::{Decoded, Value};

#[kani::proof]
fn add_sub_mul_int32() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    let (a, b) = (Num::I(x), Num::I(y));
    let (wx, wy) = (i64::from(x), i64::from(y));
    for (got, exact) in [
        (numeric::add(a, b), wx + wy),
        (numeric::sub(a, b), wx - wy),
        (numeric::mul(a, b), wx * wy),
    ] {
        match got.decode() {
            Decoded::Int32(r) => assert!(i64::from(r) == exact),
            // A double only when the exact result does not fit, or for a
            // multiplication that is `-0`.
            Decoded::Double(_) => {
                assert!(i32::try_from(exact).is_err() || (exact == 0 && (x < 0 || y < 0)));
            }
            _ => assert!(false),
        }
    }
}

#[kani::proof]
fn neg_int32() {
    let x: i32 = kani::any();
    match numeric::neg(Num::I(x)).decode() {
        Decoded::Int32(r) => assert!(x != 0 && x != i32::MIN && i64::from(r) == -i64::from(x)),
        Decoded::Double(_) => assert!(x == 0 || x == i32::MIN),
        _ => assert!(false),
    }
}

#[kani::proof]
fn rem_int32() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    match numeric::rem(Num::I(x), Num::I(y)).decode() {
        Decoded::Int32(r) => {
            assert!(y != 0);
            assert!(i64::from(r) == i64::from(x) % i64::from(y));
            assert!(!(r == 0 && x < 0));
        }
        // A double for a zero divisor, or a zero remainder of a negative
        // dividend (`-0`); the operands are never both converted wrongly.
        Decoded::Double(_) => assert!(y == 0 || (i64::from(x) % i64::from(y) == 0 && x < 0)),
        _ => assert!(false),
    }
}

#[kani::proof]
fn shifts_int32() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    let count = (y as u32) % 32;
    let (a, b) = (Num::I(x), Num::I(y));
    // `<<`: x * 2^count, reduced to 32 bits.
    let l = i64::from(x) * (1i64 << count);
    assert!(numeric::shl(a, b) == Value::int32(l as i32));
    // `>>`: floor(x / 2^count).
    let r = i64::from(x).div_euclid(1i64 << count);
    assert!(numeric::shr(a, b) == Value::int32(r as i32));
    // `>>>`: floor(x as u32 / 2^count), an int32 when it fits.
    let u = i64::from(x as u32) / (1i64 << count);
    match numeric::ushr(a, b).decode() {
        Decoded::Int32(v) => assert!(i64::from(v) == u),
        Decoded::Double(d) => assert!(d == u as f64 && u > i64::from(i32::MAX)),
        _ => assert!(false),
    }
}

#[kani::proof]
#[kani::unwind(8)]
fn frame_indexing() {
    let limit: usize = kani::any();
    kani::assume(limit <= 6);
    let mut region = Region::new(limit);
    let base: usize = kani::any();
    let size: usize = kani::any();
    kani::assume(base <= 8 && size <= 8);
    let hdr = [Value::NULL, Value::TRUE, Value::int32(0), Value::UNDEFINED];
    let pushed = region.push_frame(base, size, hdr);
    // A push succeeds exactly when the frame fits the limit.
    assert!(pushed.is_ok() == (base + size <= limit));
    if pushed.is_ok() {
        assert!(region.len() >= base + size);
    }
    let fp: usize = kani::any();
    let r: u32 = kani::any();
    match reg_slot(fp, r) {
        Some(slot) => {
            assert!(slot == fp + HDR_SLOTS + (r as usize));
            assert!(region.reg(fp, r).is_ok() == (slot < region.len()));
            assert!(region.set_reg(fp, r, Value::NULL).is_ok() == (slot < region.len()));
        }
        None => assert!(region.reg(fp, r).is_err()),
    }
    let i: usize = kani::any();
    assert!(region.get(i).is_ok() == (i < region.len()));
    assert!(region.header(fp, 3).is_ok() == fp.checked_add(3).is_some_and(|s| s < region.len()));
}

#[kani::proof]
fn return_address_round_trip() {
    let base: usize = kani::any();
    let pc: usize = kani::any();
    match pack_ret(base, pc) {
        Some(v) => {
            assert!(base < RET_LIMIT && pc < RET_LIMIT);
            assert!(unpack_ret(v) == Some(Ret::Caller { base, pc }));
        }
        None => assert!(base >= RET_LIMIT || pc >= RET_LIMIT),
    }
}

#[kani::proof]
fn argc_round_trip() {
    let argc: u32 = kani::any();
    let kind: u32 = kani::any();
    kani::assume(argc < (1 << 28));
    kani::assume(kind == KIND_PLAIN || kind == KIND_CONSTRUCT || kind == KIND_SUSPENDABLE);
    let v = enc_argc(argc, kind);
    assert!(v.is_some());
    assert!(v.and_then(dec_argc) == Some((argc, kind)));
}
