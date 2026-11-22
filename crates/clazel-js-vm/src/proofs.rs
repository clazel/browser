//! Kani harnesses, compiled only under `cargo kani`.
//!
//! Small pieces of the interpreter (item 7.8, first slice), each finishing in
//! seconds to minutes. They are evidence, not a tier claim: the crate stays at
//! tier 0, as `Cargo.toml` says.
//!
//! - [`add_sub_int32_fits`], [`add_sub_int32_overflow`], [`mul_int32_fits`],
//!   [`mul_negative_zero_is_a_double`]: for any two int32 operands, `+` and
//!   `-` give the int32 when the exact result fits and a double when it does
//!   not; `*` is checked for 16-bit operands (a 32 x 32 bit symbolic product
//!   does not finish) and for the `-0` cases: `spec::arith_add`, `arith_sub`,
//!   `arith_mul`'s encoding rule. Overflow never panics. The values of the
//!   doubles, and an overflowing `*`, are left to the differential test.
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
fn add_sub_int32_fits() {
    // The exact result fits an int32: the result is that int32. (Assuming it
    // prunes the double path, whose floating-point arithmetic CBMC is slow
    // on.)
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    let sum = i64::from(x) + i64::from(y);
    kani::assume(i32::try_from(sum).is_ok());
    assert!(numeric::add(Num::I(x), Num::I(y)) == Value::int32(sum as i32));
    let diff = i64::from(x) - i64::from(y);
    kani::assume(i32::try_from(diff).is_ok());
    assert!(numeric::sub(Num::I(x), Num::I(y)) == Value::int32(diff as i32));
}

#[kani::proof]
fn mul_int32_fits() {
    // A symbolic 32 x 32 bit multiplication does not finish in minutes under
    // CBMC, so the operands are any 16-bit values (whose product always
    // fits): the result is the exact int32.
    let p: i16 = kani::any();
    let q: i16 = kani::any();
    let m = i32::from(p) * i32::from(q);
    // Not the `-0` case, which is `mul_negative_zero_is_a_double`'s (its
    // double path has a symbolic floating-point product).
    kani::assume(!(m == 0 && (p < 0 || q < 0)));
    let got = numeric::mul(Num::I(i32::from(p)), Num::I(i32::from(q)));
    assert!(got == Value::int32(m));
}

#[kani::proof]
fn add_sub_int32_overflow() {
    // The exact result does not fit: a double (the value is the `f64` sum,
    // which the differential test checks).
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    kani::assume(i32::try_from(i64::from(x) + i64::from(y)).is_err());
    assert!(matches!(
        numeric::add(Num::I(x), Num::I(y)).decode(),
        Decoded::Double(_)
    ));
    let z: i32 = kani::any();
    let w: i32 = kani::any();
    kani::assume(i32::try_from(i64::from(z) - i64::from(w)).is_err());
    assert!(matches!(
        numeric::sub(Num::I(z), Num::I(w)).decode(),
        Decoded::Double(_)
    ));
}

#[kani::proof]
fn mul_negative_zero_is_a_double() {
    // `0 * y` and `x * 0` with a negative operand are `-0`, not the int32 0.
    for y in [-1i32, i32::MIN] {
        assert!(numeric::mul(Num::I(0), Num::I(y)) == Value::double(-0.0));
        assert!(numeric::mul(Num::I(y), Num::I(0)) == Value::double(-0.0));
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
    // A symbolic 64-bit remainder by a symbolic divisor does not finish in
    // minutes under CBMC, so the divisor is any value in -8..=8 (and the
    // overflowing pair `-2^31 % -1` is its own case); the dividend is any
    // int32.
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    kani::assume((-8..=8).contains(&y));
    match numeric::rem(Num::I(x), Num::I(y)).decode() {
        Decoded::Int32(r) => {
            assert!(y != 0);
            assert!(!(r == 0 && x < 0));
            // |r| < |y| and the sign of the dividend.
            assert!(i64::from(r).abs() < i64::from(y).abs());
            assert!(r == 0 || (r < 0) == (x < 0));
        }
        // A double for a zero divisor, or a zero remainder of a negative
        // dividend (`-0`).
        Decoded::Double(_) => assert!(y == 0 || x < 0),
        _ => assert!(false),
    }
    // The pair that overflows i32 arithmetic is `-0`, a double.
    assert!(matches!(
        numeric::rem(Num::I(i32::MIN), Num::I(-1)).decode(),
        Decoded::Double(_)
    ));
}

#[kani::proof]
#[kani::unwind(34)]
fn shifts_int32() {
    // Each shift count in turn (a symbolic divisor 2^count is as slow as
    // above), with any int32 operand; the left operand's count is
    // `b mod 32`, which the harness reaches through `b = count + 32 * k`.
    let x: i32 = kani::any();
    let k: i32 = kani::any();
    kani::assume((-4..=4).contains(&k));
    let mut count = 0u32;
    while count < 32 {
        let y = (count as i32) + 32 * k;
        let (a, b) = (Num::I(x), Num::I(y));
        let l = i64::from(x) * (1i64 << count);
        assert!(numeric::shl(a, b) == Value::int32(l as i32));
        let r = i64::from(x) >> count; // arithmetic shift: floor division
        assert!(numeric::shr(a, b) == Value::int32(r as i32));
        let u = i64::from(x as u32) >> count;
        match numeric::ushr(a, b).decode() {
            Decoded::Int32(v) => assert!(i64::from(v) == u),
            Decoded::Double(d) => assert!(d == u as f64 && u > i64::from(i32::MAX)),
            _ => assert!(false),
        }
        count += 1;
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
