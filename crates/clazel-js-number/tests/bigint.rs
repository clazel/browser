//! BigInt parsing and printing against a deliberately simple reference.
//!
//! The reference holds a value as a `Vec<u32>` (little-endian, base 2^32),
//! parses by multiply-and-add one digit at a time, and prints by repeated
//! schoolbook division by the radix, one digit at a time. It shares no code
//! with the crate's chunked, `u64`-limb conversion or its power-of-two fast
//! path. Tests cover random values in every radix 2 to 36, the limb
//! boundaries, and the syntax of StringToBigInt and BigInt literals.
//!
//! The workspace lints apply here, so lookups use `get` and a failed one
//! gives a value the assertion that follows rejects.

use clazel_js_number::bigint::Big;
use clazel_js_number::format::RangeError;
use clazel_js_number::js_bigint::{BigInt, bigint_literal_value, string_to_bigint};

/// SplitMix64: a fixed-seed generator, so a failure reproduces.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next().checked_rem(n).unwrap_or(0)
    }
}

/// Miri is about 1000 times slower than a debug build: it checks the paths
/// for undefined behaviour and does not repeat the volume.
fn count(normal: usize) -> usize {
    if cfg!(miri) {
        (normal / 1000).saturating_add(2)
    } else {
        normal
    }
}

const DIGITS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";

fn digit_of(d: u32) -> char {
    DIGITS.get(d as usize).map_or('?', |&b| char::from(b))
}

fn value_of(c: char) -> u32 {
    c.to_digit(36).unwrap_or(99)
}

// ---- the reference ----

/// Parse `digits` (no sign) in `radix`: `v = v * radix + d` on `Vec<u32>`.
fn ref_parse(digits: &str, radix: u32) -> Vec<u32> {
    let mut v: Vec<u32> = Vec::new();
    for c in digits.chars() {
        let mut carry = u64::from(value_of(c));
        for limb in &mut v {
            let t = u64::from(*limb)
                .wrapping_mul(u64::from(radix))
                .wrapping_add(carry);
            *limb = t as u32;
            carry = t >> 32;
        }
        if carry != 0 {
            v.push(carry as u32);
        }
    }
    v
}

/// Print in `radix` by repeated division of the whole number by the radix.
fn ref_print(v: &[u32], radix: u32) -> String {
    let mut v: Vec<u32> = v.to_vec();
    while v.last() == Some(&0) {
        v.pop();
    }
    if v.is_empty() {
        return "0".to_string();
    }
    let mut out: Vec<char> = Vec::new();
    while !v.is_empty() {
        let mut rem: u64 = 0;
        for limb in v.iter_mut().rev() {
            let cur = (rem << 32) | u64::from(*limb);
            *limb = cur.checked_div(u64::from(radix)).unwrap_or(0) as u32;
            rem = cur.checked_rem(u64::from(radix)).unwrap_or(0);
        }
        out.push(digit_of(rem as u32));
        while v.last() == Some(&0) {
            v.pop();
        }
    }
    out.iter().rev().collect()
}

// ---- helpers ----

fn random_digits(rng: &mut Rng, radix: u32, len: usize) -> String {
    let mut s = String::new();
    for i in 0..len {
        let d = if i == 0 && len > 1 {
            // No leading zero, so the printed form is the input.
            rng.below(u64::from(radix).saturating_sub(1))
                .saturating_add(1)
        } else {
            rng.below(u64::from(radix))
        };
        s.push(digit_of(d as u32));
    }
    s
}

fn parse(digits: &str, radix: u32) -> BigInt {
    let r = BigInt::parse_radix(digits.as_bytes(), radix);
    assert!(
        r.is_some(),
        "parse_radix rejected {digits} in radix {radix}"
    );
    r.unwrap_or_default()
}

fn show(v: &BigInt, radix: u32) -> String {
    let r = v.to_string_radix(radix);
    assert!(r.is_ok(), "radix {radix}");
    r.unwrap_or_default()
}

fn dec(s: &str) -> String {
    let r = string_to_bigint(s);
    assert!(r.is_some(), "{s:?} should parse");
    show(&r.unwrap_or_default(), 10)
}

fn undefined(s: &str) {
    assert!(string_to_bigint(s).is_none(), "{s:?} should be undefined");
}

fn lit(s: &str) -> String {
    let r = bigint_literal_value(s);
    assert!(r.is_some(), "{s:?} should be a literal");
    show(&r.unwrap_or_default(), 10)
}

fn not_lit(s: &str) {
    assert!(
        bigint_literal_value(s).is_none(),
        "{s:?} should not be a literal"
    );
}

// ---- random round trips ----

/// Random digit strings in every radix: our parse then print equals the
/// input, and printing in any other radix equals the reference's.
#[test]
fn random_round_trips_every_radix() {
    let mut rng = Rng(0x00B1_6B1C);
    for radix in 2..=36u32 {
        for _ in 0..count(60) {
            let len = 1 + rng.below(if cfg!(miri) { 40 } else { 150 }) as usize;
            let s = random_digits(&mut rng, radix, len);
            let v = parse(&s, radix);
            assert_eq!(show(&v, radix), s, "radix {radix}");
            let reference = ref_parse(&s, radix);
            for out in [2u32, 3, 8, 10, 16, 32, 36, radix] {
                assert_eq!(
                    show(&v, out),
                    ref_print(&reference, out),
                    "{s} radix {radix} to {out}"
                );
            }
        }
    }
}

/// Every pair of radixes, on values a few limbs long.
#[test]
fn all_radix_pairs() {
    let mut rng = Rng(0xFA11);
    // Miri: every seventh target radix and short values.
    let stride = if cfg!(miri) { 7 } else { 1 };
    let max_len = if cfg!(miri) { 30 } else { 90 };
    for from in 2..=36u32 {
        for to in (2..=36u32).step_by(stride) {
            for _ in 0..count(2) {
                let len = 1 + rng.below(max_len) as usize;
                let s = random_digits(&mut rng, from, len);
                let v = parse(&s, from);
                assert_eq!(show(&v, to), ref_print(&ref_parse(&s, from), to));
            }
        }
    }
}

/// Upper-case digits parse to the same value as lower-case.
#[test]
fn digit_case_is_ignored() {
    let mut rng = Rng(77);
    for radix in 11..=36u32 {
        for _ in 0..count(5) {
            let s = random_digits(&mut rng, radix, 40);
            assert_eq!(parse(&s, radix), parse(&s.to_uppercase(), radix));
        }
    }
}

/// Values around 2^k for every k up to 300, in every radix, in both signs.
#[test]
fn limb_boundaries() {
    let top = if cfg!(miri) { 130 } else { 300 };
    let radixes: &[u32] = if cfg!(miri) {
        &[2, 10, 16, 36]
    } else {
        &[2, 3, 7, 8, 10, 16, 32, 36]
    };
    for k in (0..=top).step_by(if cfg!(miri) { 7 } else { 1 }) {
        // 2^k as binary digits, then +-1 around it.
        let pow = format!("1{}", "0".repeat(k));
        let reference = ref_parse(&pow, 2);
        let v = parse(&pow, 2);
        for &r in radixes {
            assert_eq!(show(&v, r), ref_print(&reference, r), "2^{k} radix {r}");
        }
        let neg = v.negated();
        assert_eq!(show(&neg, 10), format!("-{}", ref_print(&reference, 10)));
        if k >= 1 {
            let ones = "1".repeat(k);
            let w = parse(&ones, 2);
            let rw = ref_parse(&ones, 2);
            for &r in radixes {
                assert_eq!(show(&w, r), ref_print(&rw, r), "2^{k}-1 radix {r}");
            }
        }
    }
}

/// Small values against Rust's own formatting of `u128`.
#[test]
fn matches_u128_formatting() {
    let mut rng = Rng(5);
    for _ in 0..count(2000) {
        let hi = rng.next();
        let lo = rng.next();
        let shift = rng.below(128);
        let x = ((u128::from(hi) << 64) | u128::from(lo)) >> shift;
        let v = BigInt::from_parts(false, Big::from_u128(x));
        assert_eq!(show(&v, 10), x.to_string());
        assert_eq!(show(&v, 16), format!("{x:x}"));
        assert_eq!(show(&v, 8), format!("{x:o}"));
        assert_eq!(show(&v, 2), format!("{x:b}"));
        assert_eq!(dec(&x.to_string()), x.to_string());
        assert_eq!(dec(&format!("0x{x:X}")), x.to_string());
        assert_eq!(dec(&format!("0o{x:o}")), x.to_string());
        assert_eq!(dec(&format!("0b{x:b}")), x.to_string());
    }
}

#[test]
fn matches_i64_formatting() {
    let mut rng = Rng(6);
    for x in [i64::MIN, i64::MIN + 1, -1, 0, 1, i64::MAX] {
        assert_eq!(show(&BigInt::from_i64(x), 10), x.to_string());
    }
    for _ in 0..count(500) {
        let x = rng.next() as i64;
        assert_eq!(show(&BigInt::from_i64(x), 10), x.to_string());
        assert_eq!(dec(&x.to_string()), x.to_string());
    }
}

// ---- edge cases: printing ----

#[test]
fn printing_edges() {
    let zero = BigInt::zero();
    for r in 2..=36 {
        assert_eq!(show(&zero, r), "0");
        assert_eq!(show(&zero.negated(), r), "0");
        assert_eq!(show(&BigInt::from_u64(1), r), "1");
        assert_eq!(show(&BigInt::from_i64(-1), r), "-1");
        // The radix itself is "10".
        assert_eq!(show(&BigInt::from_u64(u64::from(r)), r), "10");
        assert_eq!(
            show(&BigInt::from_u64(u64::from(r) - 1), r),
            digit_of(r - 1).to_string()
        );
    }
    assert_eq!(show(&BigInt::from_i64(-35), 36), "-z");
    assert_eq!(show(&BigInt::from_u64(u64::MAX), 16), "ffffffffffffffff");
    assert_eq!(
        show(&BigInt::from_u64(u64::MAX), 10),
        "18446744073709551615"
    );
    assert_eq!(
        show(&BigInt::from_i64(i64::MIN), 2),
        format!("-1{}", "0".repeat(63))
    );
    // Chunks that are all zero in the middle: 10^60 and 36^40.
    let p = format!("1{}", "0".repeat(60));
    assert_eq!(show(&parse(&p, 10), 10), p);
    let q = format!("1{}", "0".repeat(40));
    assert_eq!(show(&parse(&q, 36), 36), q);
    for r in [0u32, 1, 37, 100, u32::MAX] {
        assert_eq!(zero.to_string_radix(r), Err(RangeError));
    }
}

#[test]
fn large_values() {
    // 10^2000 and 2^8192 round trip.
    let (dec_zeros, bin_zeros) = if cfg!(miri) { (200, 512) } else { (2000, 8192) };
    let p = format!("1{}", "0".repeat(dec_zeros));
    let v = parse(&p, 10);
    assert_eq!(show(&v, 10), p);
    assert_eq!(show(&v, 16), ref_print(&ref_parse(&p, 10), 16));
    let b = format!("1{}", "0".repeat(bin_zeros));
    assert_eq!(
        show(&parse(&b, 2), 16),
        format!("1{}", "0".repeat(bin_zeros / 4))
    );
    // 2^bin_zeros in radix 32: bin_zeros % 5 leftover bits make the top digit.
    let top = 1u32 << (bin_zeros % 5);
    assert_eq!(
        show(&parse(&b, 2), 32),
        format!("{}{}", digit_of(top), "0".repeat(bin_zeros / 5))
    );
}

// ---- edge cases: StringToBigInt ----

#[test]
fn string_to_bigint_accepts() {
    assert_eq!(dec(""), "0");
    assert_eq!(dec("   "), "0");
    assert_eq!(
        dec(
            "\t\n\u{b}\u{c}\r \u{a0}\u{1680}\u{2000}\u{200a}\u{2028}\u{2029}\u{202f}\u{205f}\u{3000}\u{feff}"
        ),
        "0"
    );
    assert_eq!(dec("0"), "0");
    assert_eq!(dec("-0"), "0");
    assert_eq!(dec("+0"), "0");
    assert_eq!(dec("000"), "0");
    assert_eq!(dec("007"), "7");
    assert_eq!(dec("+5"), "5");
    assert_eq!(dec("-5"), "-5");
    assert_eq!(dec("  \n12\t "), "12");
    assert_eq!(dec("\u{feff}-12\u{2028}"), "-12");
    assert_eq!(
        dec("123456789012345678901234567890"),
        "123456789012345678901234567890"
    );
    assert_eq!(
        dec("-123456789012345678901234567890"),
        "-123456789012345678901234567890"
    );
    assert_eq!(dec("0xff"), "255");
    assert_eq!(dec("0XFF"), "255");
    assert_eq!(dec("0xFf"), "255");
    assert_eq!(dec("0o17"), "15");
    assert_eq!(dec("0O17"), "15");
    assert_eq!(dec("0b101"), "5");
    assert_eq!(dec("0B101"), "5");
    assert_eq!(dec("0x0"), "0");
    assert_eq!(dec("0x000ff"), "255");
    assert_eq!(dec(" 0x10 "), "16");
    assert_eq!(
        dec("0xffffffffffffffffffffffffffffffff"),
        "340282366920938463463374607431768211455"
    );
    // Exactly one limb, one limb plus one.
    assert_eq!(dec("18446744073709551616"), "18446744073709551616");
    assert_eq!(dec("0x10000000000000000"), "18446744073709551616");
}

#[test]
fn string_to_bigint_rejects() {
    for s in [
        "-",
        "+",
        "--1",
        "+-1",
        "-+1",
        "- 1",
        "+ 1",
        "1 2",
        "1_0",
        "1n",
        "n",
        "1e3",
        "1E3",
        "1.0",
        "1.",
        ".1",
        "0.0",
        "-.0",
        "Infinity",
        "NaN",
        "0x",
        "0X",
        "0o",
        "0b",
        "0x ",
        "0xg",
        "0o8",
        "0b2",
        "0b12",
        "-0x1",
        "+0x1",
        "- 0x1",
        "0x-1",
        "0x+1",
        "0x1_0",
        "0x1n",
        "0x1.8",
        "0 x1",
        "1x",
        "x1",
        "00x1",
        "0xx1",
        "０",
        "１２",
        "1\u{0}",
        "\u{85}1",
        "\u{200b}1",
        "\u{180e}1",
        "1\u{200b}",
        "١٢",
        "0x١",
        "(1)",
        "1,2",
        "1 ",
        "\u{1}1",
    ] {
        // "1 " is valid (trailing white space): checked below, not here.
        if s == "1 " {
            continue;
        }
        undefined(s);
    }
    assert_eq!(dec("1 "), "1");
}

// ---- edge cases: literals ----

#[test]
fn literals_accept() {
    assert_eq!(lit("0n"), "0");
    assert_eq!(lit("1n"), "1");
    assert_eq!(lit("10n"), "10");
    assert_eq!(lit("1_0n"), "10");
    assert_eq!(lit("1_000_000n"), "1000000");
    assert_eq!(
        lit("123456789012345678901234567890n"),
        "123456789012345678901234567890"
    );
    assert_eq!(lit("0xFFn"), "255");
    assert_eq!(lit("0xffn"), "255");
    assert_eq!(lit("0XFFn"), "255");
    assert_eq!(lit("0x0n"), "0");
    assert_eq!(lit("0x00n"), "0");
    assert_eq!(lit("0x1n"), "1");
    assert_eq!(lit("0xF_Fn"), "255");
    assert_eq!(lit("0o7_7n"), "63");
    assert_eq!(lit("0O17n"), "15");
    assert_eq!(lit("0b1_0n"), "2");
    assert_eq!(lit("0B11n"), "3");
    assert_eq!(lit("0b0n"), "0");
    assert_eq!(lit("0xffffffffffffffffn"), "18446744073709551615");
    assert_eq!(lit("0x1_0000_0000_0000_0000n"), "18446744073709551616");
}

#[test]
fn literals_reject() {
    for s in [
        "", "n", "0", "1", "10", "0x1", "0xn", "0x_n", "0bn", "0on", "00n", "01n", "07n", "09n",
        "0_0n", "0_1n", "1_n", "_1n", "1__0n", "0x_1n", "0x1_n", "0x1__0n", "0b2n", "0o8n", "0xgn",
        "1.0n", "1e3n", ".1n", "1nn", "-1n", "+1n", "1 n", " 1n", "1n ", "0x1.8n", "0b1_n",
        "0_xFn", "1_0_n", "1N", "0XN", "１n",
    ] {
        not_lit(s);
    }
}

#[test]
fn literal_separators_do_not_change_the_value() {
    let mut rng = Rng(9);
    for (radix, prefix) in [(10u32, ""), (16, "0x"), (8, "0o"), (2, "0b")] {
        for _ in 0..count(100) {
            let len = 1 + rng.below(60) as usize;
            let s = random_digits(&mut rng, radix, len);
            let mut with_sep = String::new();
            for (i, c) in s.chars().enumerate() {
                if i > 0 && rng.below(3) == 0 {
                    with_sep.push('_');
                }
                with_sep.push(c);
            }
            let plain = format!("{prefix}{s}n");
            let sep = if radix == 10 {
                format!("{with_sep}n")
            } else {
                format!("{prefix}{with_sep}n")
            };
            let a = bigint_literal_value(&plain);
            let b = bigint_literal_value(&sep);
            assert!(a.is_some() && b.is_some(), "{plain} {sep}");
            assert_eq!(a, b);
            assert_eq!(show(&a.unwrap_or_default(), radix), s);
        }
    }
}

/// `string_to_bigint` agrees with the literal parser on every plain
/// literal's digits.
#[test]
fn string_and_literal_agree() {
    let mut rng = Rng(10);
    for _ in 0..count(300) {
        let len = 1 + rng.below(80) as usize;
        let s = random_digits(&mut rng, 16, len);
        let text = format!("0x{s}");
        assert_eq!(
            string_to_bigint(&text),
            bigint_literal_value(&format!("{text}n"))
        );
    }
}

#[test]
fn parse_radix_rejects() {
    assert!(BigInt::parse_radix(b"", 10).is_none());
    assert!(BigInt::parse_radix(b"1", 1).is_none());
    assert!(BigInt::parse_radix(b"1", 37).is_none());
    assert!(BigInt::parse_radix(b"z", 35).is_none());
    assert!(BigInt::parse_radix(b"z", 36).is_some());
    assert!(BigInt::parse_radix(b"2", 2).is_none());
    assert!(BigInt::parse_radix(b"-1", 10).is_none());
    assert!(BigInt::parse_radix("é".as_bytes(), 36).is_none());
}

#[test]
fn zero_is_never_negative() {
    assert!(!BigInt::from_i64(0).is_negative());
    assert!(!BigInt::zero().negated().is_negative());
    assert!(!BigInt::from_parts(true, Big::zero()).is_negative());
    let r = string_to_bigint("-0").unwrap_or_default();
    assert!(!r.is_negative() && r.is_zero());
    assert_eq!(r, BigInt::zero());
    assert!(BigInt::from_i64(-1).is_negative());
}
