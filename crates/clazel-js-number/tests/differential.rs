//! Differential tests against Rust's own `f64` parsing and formatting, which
//! are correctly rounded (`str::parse`) and shortest (`Display`, `LowerExp`).
//!
//! - every `f32` widened to `f64`, at a stride (all 2^32 with
//!   `CLAZEL_F32_STRIDE=1` in a release build; the default is sized for a
//!   debug `cargo test`, and Miri uses a far larger one), plus every
//!   exponent field with its edge mantissas at stride 1;
//! - random doubles from a fixed-seed generator, and random decimal strings,
//!   including exact halfway cases between neighbouring doubles (the hard
//!   inputs for a parser) and their neighbours.
//!
//! The workspace lints apply to this file too, so the helpers below (`head`,
//! `tail`, `split`, `parse_f64`) stand in for slicing and `unwrap`: a failed
//! lookup gives an empty string or NaN, and the assertion that follows fails.

use clazel_js_number::fixed::FixedBig;
use clazel_js_number::shortest::shortest_digits;
use clazel_js_number::{
    RangeError, number_to_string, string_to_number, to_exponential, to_fixed, to_precision,
};

/// Room for the exact decimal expansions of the midpoints (about 2,600 bits).
type Big = FixedBig<64>;

/// SplitMix64 (Steele, Lea and Flood 2014): a fixed-seed generator, so a
/// failure reproduces.
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

/// How many cases a randomised test runs. Miri runs a ten-thousandth: it
/// is about 1000 times slower than a debug build, and is there to find
/// undefined behaviour in the paths the tests exercise, not to repeat them.
fn count(normal: usize) -> usize {
    if cfg!(miri) {
        (normal / 10_000).saturating_add(2)
    } else {
        normal
    }
}

/// The first `n` bytes of an ASCII string.
fn head(s: &str, n: usize) -> &str {
    s.get(..n).unwrap_or("")
}

/// All but the first `n` bytes of an ASCII string.
fn tail(s: &str, n: usize) -> &str {
    s.get(n..).unwrap_or("")
}

/// Split at the first `c`.
fn split(s: &str, c: char) -> (&str, &str) {
    s.split_once(c).unwrap_or((s, ""))
}

/// Rust's own parse, which is correctly rounded.
fn parse_f64(s: &str) -> f64 {
    let r = s.parse::<f64>();
    assert!(r.is_ok(), "Rust cannot parse {s}");
    r.unwrap_or(f64::NAN)
}

fn parse_i64(s: &str) -> i64 {
    s.parse::<i64>().unwrap_or(i64::MIN)
}

fn zeros(n: i64) -> String {
    "0".repeat(usize::try_from(n).unwrap_or(0))
}

fn sign_of(e: i64) -> char {
    if e < 0 { '-' } else { '+' }
}

/// What JavaScript prints for a finite nonzero `x`, built from Rust's
/// shortest `LowerExp` digits and an independent transcription of the layout.
fn expected_to_string(x: f64) -> String {
    let neg = x < 0.0;
    let s = format!("{:e}", x.abs());
    let (mant, exp) = split(&s, 'e');
    let e = parse_i64(exp);
    let digits: String = mant.chars().filter(|c| *c != '.').collect();
    let k = digits.len() as i64;
    let n = e.saturating_add(1);
    let nu = usize::try_from(n).unwrap_or(0);
    let body = if k <= n && n <= 21 {
        format!("{digits}{}", zeros(n.saturating_sub(k)))
    } else if 0 < n && n <= 21 {
        format!("{}.{}", head(&digits, nu), tail(&digits, nu))
    } else if -6 < n && n <= 0 {
        format!("0.{}{digits}", zeros(n.saturating_neg()))
    } else {
        let ex = n.saturating_sub(1);
        let sign = sign_of(ex);
        let ex = ex.saturating_abs();
        if k == 1 {
            format!("{digits}e{sign}{ex}")
        } else {
            format!("{}.{}e{sign}{ex}", head(&digits, 1), tail(&digits, 1))
        }
    };
    if neg { format!("-{body}") } else { body }
}

/// Whether the digits after the first `kept` digits of an exact expansion
/// are a lone 5 and zeros (a rounding tie).
fn is_tie(rest: &str) -> bool {
    let mut it = rest.chars();
    it.next() == Some('5') && it.all(|c| c == '0')
}

/// The exact decimal digits of `x` (all of them), without the point.
fn exact_digits(x: f64) -> String {
    let exact = format!("{:.1100e}", x.abs());
    let (m, _) = split(&exact, 'e');
    m.chars().filter(|c| *c != '.').collect()
}

fn last_digit(s: &str) -> u8 {
    s.bytes().last().unwrap_or(0).wrapping_sub(b'0')
}

/// Whether our shortest digits equal Rust's. They may differ in one case
/// only, and this asserts it is that case: the exact value of `d` is halfway
/// between two shortest candidates. ECMA-262 chooses the even one (Number::
/// toString step 5, "choose the one that is even"), and Rust's `LowerExp`
/// rounds the tie up.
fn digits_agree(d: f64) -> bool {
    let (digits, e10) = shortest_digits(d.abs()).unwrap_or((0, 0));
    let ours = digits.to_string();
    let our_exp = i64::from(e10)
        .saturating_add(ours.len() as i64)
        .saturating_sub(1);
    let rust = format!("{:e}", d.abs());
    let (m, e) = split(&rust, 'e');
    let theirs: String = m.chars().filter(|c| *c != '.').collect();
    let their_exp = parse_i64(e);
    if ours == theirs && our_exp == their_exp {
        return true;
    }
    assert_eq!(our_exp, their_exp, "exponent of {d:e}");
    assert_eq!(ours.len(), theirs.len(), "digit count of {d:e}");
    let n = ours.len().saturating_sub(1);
    assert_eq!(head(&ours, n), head(&theirs, n), "{d:e}");
    assert_eq!(
        last_digit(&theirs),
        last_digit(&ours).wrapping_add(1),
        "{d:e}"
    );
    assert_eq!(
        last_digit(&ours) % 2,
        0,
        "the tie must go to the even digit: {d:e}"
    );
    assert!(
        is_tie(tail(&exact_digits(d), ours.len())),
        "not an exact tie: {d:e}"
    );
    false
}

fn check_double(d: f64) {
    if !d.is_finite() {
        return;
    }
    // Number::toString against Rust's shortest digits.
    if d != 0.0 {
        let ours = number_to_string(d);
        if digits_agree(d) {
            assert_eq!(ours, expected_to_string(d), "toString of {d:e}");
            // In the range where JavaScript prints plain digits, `Display`
            // is the same string.
            let a = d.abs();
            if (1e-6..1e21).contains(&a) {
                assert_eq!(ours, format!("{d}"), "Display of {d:e}");
            }
        }
    }
    // StringToNumber round-trips Rust's shortest, and its exact, output.
    for s in [format!("{d:e}"), format!("{d}"), format!("{d:?}")] {
        let got = string_to_number(&s);
        assert_eq!(got.to_bits(), d.to_bits(), "parse of {s}");
    }
    // JavaScript prints -0 as "0", so only nonzero values round-trip.
    if d != 0.0 {
        let js = number_to_string(d);
        assert_eq!(
            string_to_number(&js).to_bits(),
            d.to_bits(),
            "parse of {js}"
        );
    }
}

/// A stride through the `f32` bit patterns.
fn f32_stride() -> u64 {
    if let Some(s) = std::env::var("CLAZEL_F32_STRIDE")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
    {
        return s.max(1);
    }
    if cfg!(miri) {
        1 << 25
    } else if cfg!(debug_assertions) {
        2039
    } else {
        61
    }
}

fn check_f32(x: f32) {
    if !x.is_finite() {
        return;
    }
    check_double(f64::from(x));
    // The shortest `f32` text is a hard decimal for the `f64` parser: it is
    // far from the double nearest it. Compare with Rust's parse.
    for s in [format!("{x}"), format!("{x:e}")] {
        let want = parse_f64(&s);
        assert_eq!(
            string_to_number(&s).to_bits(),
            want.to_bits(),
            "parse of {s}"
        );
    }
}

#[test]
fn every_f32_widened() {
    let stride = f32_stride();
    let mut bits: u64 = 0;
    while bits <= u64::from(u32::MAX) {
        check_f32(f32::from_bits(bits as u32));
        bits = bits.saturating_add(stride);
    }
    // Every exponent field with its edge mantissas, both signs, at stride 1.
    for exp in 0u32..=255 {
        for frac in [
            0u32, 1, 2, 3, 0x3F_FFFF, 0x40_0000, 0x40_0001, 0x7F_FFFE, 0x7F_FFFF,
        ] {
            for sign in [0u32, 1] {
                check_f32(f32::from_bits((sign << 31) | (exp << 23) | frac));
            }
        }
        if cfg!(miri) {
            break;
        }
    }
}

#[test]
fn random_doubles() {
    let mut rng = Rng(0x2026_1121_C1A2_E100);
    for _ in 0..count(300_000) {
        check_double(f64::from_bits(rng.next()));
    }
    // Every exponent field with random fractions.
    for exp in 0u64..2047 {
        for _ in 0..count(40) {
            let frac = rng.next() & ((1 << 52) - 1);
            check_double(f64::from_bits((exp << 52) | frac));
        }
        if cfg!(miri) && exp > 4 {
            break;
        }
    }
    // Small integers, eighths, and values near powers of ten.
    for i in 0..count(5_000) as u64 {
        check_double(i as f64);
        check_double(i as f64 / 8.0);
        check_double(10f64.powi(i as i32 % 300) * (1.0 + (i % 7) as f64));
    }
}

fn random_decimal(rng: &mut Rng) -> String {
    let cap = if rng.below(4) == 0 { 60 } else { 25 };
    let nd = 1usize.saturating_add(rng.below(cap) as usize);
    let mut digits = String::new();
    for _ in 0..nd {
        digits.push(char::from(b'0'.wrapping_add(rng.below(10) as u8)));
    }
    let mut s = String::new();
    match rng.below(4) {
        0 => s.push_str(&digits),
        1 => {
            let at = rng.below((nd as u64).saturating_add(1)) as usize;
            s.push_str(head(&digits, at));
            s.push('.');
            s.push_str(tail(&digits, at));
            if s == "." {
                s.push('0');
            }
        }
        _ => {
            let at = 1usize.saturating_add(rng.below(nd as u64) as usize);
            s.push_str(head(&digits, at));
            s.push('.');
            s.push_str(tail(&digits, at));
        }
    }
    if rng.below(3) != 0 {
        let e = (rng.below(800) as i64).saturating_sub(400);
        let e = if rng.below(3) == 0 { e / 10 } else { e };
        s.push_str(&format!("e{e}"));
    }
    s
}

#[test]
fn random_decimal_strings() {
    let mut rng = Rng(0xDEC1_0000_0000_0001);
    for _ in 0..count(400_000) {
        let s = random_decimal(&mut rng);
        let want = parse_f64(&s);
        let got = string_to_number(&s);
        assert_eq!(got.to_bits(), want.to_bits(), "parse of {s}");
        let neg = format!("-{s}");
        assert_eq!(
            string_to_number(&neg).to_bits(),
            (-want).to_bits(),
            "parse of {neg}"
        );
    }
}

/// The exact midpoint between `d` and the next double up, as a decimal
/// string `digits` and a decimal exponent (value = digits * 10^exp10).
fn midpoint(d: f64) -> (String, i64) {
    let bits = d.to_bits();
    let frac = bits & ((1 << 52) - 1);
    let exp = ((bits >> 52) & 0x7FF) as i64;
    let (m, e2) = if exp == 0 {
        (frac, -1074)
    } else {
        (frac | (1 << 52), exp.saturating_sub(1075))
    };
    // (2m + 1) * 2^(e2 - 1)
    let m2 = Big::from_u64(m.wrapping_mul(2).wrapping_add(1));
    let sh = e2.saturating_sub(1);
    if sh >= 0 {
        (m2.shl(sh as u64).to_decimal(), 0)
    } else {
        let mut b = m2;
        b.mul_pow5(sh.unsigned_abs() as u32);
        (b.to_decimal(), sh)
    }
}

fn big_of(digits: &str) -> Big {
    let mut b = Big::zero();
    for c in digits.bytes() {
        b.mul_small(10);
        b.add_small(u64::from(c.wrapping_sub(b'0')));
    }
    b
}

#[test]
fn halfway_cases() {
    let mut rng = Rng(0x4A1F_4A1F_4A1F_0001);
    for i in 0..count(40_000) {
        // Mostly modest exponents (short exact decimals), some extreme ones.
        let bits = if i % 8 == 0 {
            rng.next() & 0x7FEF_FFFF_FFFF_FFFF
        } else {
            let e = rng.below(140).saturating_add(953);
            (e << 52) | (rng.next() & ((1 << 52) - 1))
        };
        let d = f64::from_bits(bits);
        let (digits, e10) = midpoint(d);
        let tie = format!("{digits}e{e10}");
        // The tie, plus one unit in a much lower place, and minus one.
        let above = format!("{digits}1e{}", e10.saturating_sub(1));
        let mut b = big_of(&digits);
        b.mul_small(10);
        b.sub_assign(&Big::from_u64(1));
        let below = format!("{}e{}", b.to_decimal(), e10.saturating_sub(1));
        for s in [tie, above, below] {
            let want = parse_f64(&s);
            assert_eq!(
                string_to_number(&s).to_bits(),
                want.to_bits(),
                "parse of {s}"
            );
        }
    }
}

#[test]
fn parse_grammar() {
    let nan = |s: &str| string_to_number(s).is_nan();
    let val = |s: &str| string_to_number(s);
    // StrWhiteSpace around, and empty.
    assert_eq!(val(""), 0.0);
    assert_eq!(
        val(" \t\n\r\u{b}\u{c}\u{a0}\u{feff}\u{2028}\u{2029}\u{3000}"),
        0.0
    );
    assert_eq!(val("\u{feff} 12 \u{a0}"), 12.0);
    assert!(nan("\u{85}1"), "U+0085 is not white space");
    assert!(nan("\u{180e}1"), "U+180E is not white space");
    assert!(val("-0").is_sign_negative() && val("-0") == 0.0);
    assert!(val("+0").is_sign_positive());
    assert_eq!(val("Infinity"), f64::INFINITY);
    assert_eq!(val("-Infinity"), f64::NEG_INFINITY);
    assert_eq!(val("+Infinity"), f64::INFINITY);
    for s in [
        "infinity",
        "inf",
        "INFINITY",
        "Infinit",
        "Infinityx",
        "NaN",
        "nan",
    ] {
        assert!(nan(s), "{s}");
    }
    for (s, v) in [
        ("1", 1.0),
        ("1.", 1.0),
        (".5", 0.5),
        ("5.e1", 50.0),
        (".5E-1", 0.05),
        ("0.0", 0.0),
        ("00012", 12.0),
        ("1e3", 1000.0),
        ("1E+3", 1000.0),
        ("+1.5", 1.5),
        ("-1.5", -1.5),
    ] {
        assert_eq!(val(s), v, "{s}");
    }
    for s in [
        ".", "+", "-", "e5", "1e", "1e+", "1e-", "1_0", "1 2", "--1", "+-1", "1.2.3", "0x", "0b2",
        "0o8", "-0x10", "+0x10", "0xg", "0x_1", "1n", "0x1n", "1e1.5", "\u{663}",
    ] {
        assert!(nan(s), "{s}");
    }
    // Non-decimal integers, rounded to nearest-even when they do not fit.
    assert_eq!(val("0x10"), 16.0);
    assert_eq!(val("0XfF"), 255.0);
    assert_eq!(val("0o17"), 15.0);
    assert_eq!(val("0b101"), 5.0);
    assert_eq!(val("0x0"), 0.0);
    assert_eq!(val("0x20000000000001"), 9_007_199_254_740_992.0); // 2^53 + 1 ties to even
    assert_eq!(val("0x20000000000003"), 9_007_199_254_740_996.0);
    assert_eq!(val("0x20000000000001000"), 9_007_199_254_740_992.0 * 4096.0);
    assert_eq!(
        val("0x20000000000001001"),
        (9_007_199_254_740_992.0 + 2.0) * 4096.0
    );
    assert_eq!(val(&format!("0x{}", "f".repeat(300))), f64::INFINITY);
    assert_eq!(val(&format!("0x{}", "0".repeat(300))), 0.0);
    let max_bits = format!("{}{}", "1".repeat(53), "0".repeat(971));
    assert_eq!(val(&format!("0b{max_bits}")), f64::MAX);
    assert_eq!(
        val(&format!("0b{}", "1".repeat(1024))),
        f64::INFINITY,
        "2^1024 - 1 rounds up"
    );
    assert_eq!(val(&format!("0b{}", "1".repeat(1025))), f64::INFINITY);
    // Limits.
    assert_eq!(val("1.7976931348623157e308"), f64::MAX);
    assert_eq!(val("1.7976931348623158e308"), f64::MAX);
    assert_eq!(val("1.7976931348623159e308"), f64::INFINITY);
    assert_eq!(val("5e-324"), 5e-324);
    assert_eq!(val("2.4703282292062327e-324"), 0.0);
    assert_eq!(val("2.4703282292062328e-324"), 5e-324);
    assert_eq!(val("1e-400"), 0.0);
    assert_eq!(val("1e400"), f64::INFINITY);
    assert_eq!(val("0e999999999999999999999"), 0.0);
    assert_eq!(val("1e999999999999999999999"), f64::INFINITY);
    assert_eq!(val("1e-999999999999999999999"), 0.0);
    // Very long inputs.
    let long = format!("0.{}1e1", "0".repeat(100_000));
    assert_eq!(val(&long), 0.0);
    let long = format!("1{}", "0".repeat(400));
    assert_eq!(val(&long), f64::INFINITY);
    let long = format!("{}.5e-5000", "9".repeat(5000));
    assert_eq!(val(&long), parse_f64(&long));
    let long = format!("0.{}e1", "9".repeat(5000));
    assert_eq!(val(&long), parse_f64(&long));
}

#[test]
fn to_string_cases() {
    for (x, s) in [
        (0.0, "0"),
        (-0.0, "0"),
        (1.0, "1"),
        (-1.5, "-1.5"),
        (0.1, "0.1"),
        (123456789012345680000.0, "123456789012345680000"),
        (1e21, "1e+21"),
        (1.5e21, "1.5e+21"),
        (1e-6, "0.000001"),
        (1e-7, "1e-7"),
        (1.5e-7, "1.5e-7"),
        (123.456, "123.456"),
        (f64::MAX, "1.7976931348623157e+308"),
        (5e-324, "5e-324"),
        (f64::MIN_POSITIVE, "2.2250738585072014e-308"),
        (9007199254740993.0, "9007199254740992"),
        (f64::NAN, "NaN"),
        (f64::INFINITY, "Infinity"),
        (f64::NEG_INFINITY, "-Infinity"),
    ] {
        assert_eq!(number_to_string(x), s);
    }
}

/// The result of a call that must not be a `RangeError`.
fn ok(r: Result<String, RangeError>) -> String {
    assert!(r.is_ok());
    r.unwrap_or_default()
}

#[test]
fn fixed_cases() {
    let f = |x: f64, d: i64| ok(to_fixed(x, d));
    assert_eq!(f(0.5, 0), "1", "ties pick the larger n");
    assert_eq!(f(1.5, 0), "2");
    assert_eq!(f(2.5, 0), "3");
    assert_eq!(f(-2.5, 0), "-3");
    assert_eq!(f(1.005, 2), "1.00", "1.005 is below the tie");
    assert_eq!(f(1.45, 1), "1.4");
    assert_eq!(f(0.0, 2), "0.00");
    assert_eq!(f(-0.0, 2), "0.00");
    assert_eq!(f(-0.0000001, 2), "-0.00");
    assert_eq!(f(123.456, 0), "123");
    assert_eq!(f(123.456, 10), "123.4560000000");
    assert_eq!(f(1e21, 2), "1e+21");
    assert_eq!(f(-1e21, 2), "-1e+21");
    assert_eq!(f(999999999999999900000.0, 1), "999999999999999868928.0");
    assert_eq!(f(f64::NAN, 2), "NaN");
    assert_eq!(f(f64::INFINITY, 2), "Infinity");
    assert_eq!(f(0.000001, 7), "0.0000010");
    assert_eq!(to_fixed(1.0, 101), Err(RangeError));
    assert_eq!(to_fixed(1.0, -1), Err(RangeError));
    assert_eq!(to_fixed(f64::NAN, 101), Err(RangeError));
    assert_eq!(to_fixed(1.0, i64::MAX), Err(RangeError));
    assert_eq!(f(1.0, 100).len(), 102);
}

#[test]
fn exponential_cases() {
    let f = |x: f64, d: Option<i64>| ok(to_exponential(x, d));
    assert_eq!(f(123456.0, Some(2)), "1.23e+5");
    assert_eq!(f(123456.0, None), "1.23456e+5");
    assert_eq!(f(0.0, None), "0e+0");
    assert_eq!(f(0.0, Some(3)), "0.000e+0");
    assert_eq!(f(-0.0, Some(1)), "0.0e+0");
    assert_eq!(f(1.0, Some(0)), "1e+0");
    assert_eq!(f(-1.5, Some(0)), "-2e+0");
    assert_eq!(f(2.5, Some(0)), "3e+0", "ties pick the larger n");
    assert_eq!(f(0.00001, Some(1)), "1.0e-5");
    assert_eq!(f(9.99, Some(1)), "1.0e+1");
    assert_eq!(f(99.99, Some(0)), "1e+2");
    assert_eq!(f(f64::MAX, Some(5)), "1.79769e+308");
    assert_eq!(f(5e-324, Some(3)), "4.941e-324");
    assert_eq!(f(f64::NAN, Some(500)), "NaN");
    assert_eq!(f(f64::INFINITY, Some(500)), "Infinity");
    assert_eq!(to_exponential(1.0, Some(101)), Err(RangeError));
    assert_eq!(to_exponential(1.0, Some(-1)), Err(RangeError));
}

#[test]
fn precision_cases() {
    let f = |x: f64, d: Option<i64>| ok(to_precision(x, d));
    assert_eq!(f(123.456, Some(4)), "123.5");
    assert_eq!(f(123.456, Some(2)), "1.2e+2");
    assert_eq!(f(123.456, Some(3)), "123");
    assert_eq!(f(0.000123, Some(2)), "0.00012");
    assert_eq!(f(0.00000123, Some(2)), "0.0000012");
    assert_eq!(f(0.000000123, Some(2)), "1.2e-7");
    assert_eq!(f(1e21, Some(3)), "1.00e+21");
    assert_eq!(f(0.0, Some(3)), "0.00");
    assert_eq!(f(-0.0, Some(1)), "0");
    assert_eq!(f(1.25, Some(2)), "1.3", "ties pick the larger n");
    assert_eq!(f(1.35, Some(2)), "1.4");
    assert_eq!(f(99.99, Some(3)), "100");
    assert_eq!(f(99.99, Some(1)), "1e+2");
    assert_eq!(f(15.0, Some(1)), "2e+1");
    assert_eq!(f(123.456, None), "123.456");
    assert_eq!(f(f64::NAN, Some(0)), "NaN");
    assert_eq!(to_precision(1.0, Some(0)), Err(RangeError));
    assert_eq!(to_precision(1.0, Some(101)), Err(RangeError));
    assert_eq!(f(1.0, Some(100)).len(), 101);
}

fn random_finite(rng: &mut Rng) -> f64 {
    loop {
        let x = match rng.below(4) {
            0 => f64::from_bits(rng.next()),
            1 => (rng.next() >> 11) as f64 / 2f64.powi(rng.below(40) as i32),
            2 => (rng.below(2_000_001) as f64 - 1_000_000.0) / 1000.0,
            _ => {
                (rng.below(100_000) as f64) * 10f64.powi((rng.below(40) as i32).saturating_sub(20))
            }
        };
        if x.is_finite() {
            return x;
        }
    }
}

#[test]
fn fixed_differential() {
    let mut rng = Rng(0xF1ED_0000_0000_0002);
    for _ in 0..count(60_000) {
        let x = random_finite(&mut rng);
        if x == 0.0 {
            continue;
        }
        let f = rng.below(25) as usize;
        let ours = ok(to_fixed(x, f as i64));
        if x.abs() >= 1e21 {
            assert_eq!(ours, number_to_string(x));
            continue;
        }
        let exact = format!("{:.1100}", x.abs());
        let (_, frac) = split(&exact, '.');
        if is_tie(tail(frac, f)) {
            continue;
        }
        assert_eq!(ours, format!("{x:.f$}"), "toFixed({x:e}, {f})");
    }
}

fn js_exponent(rust: &str) -> String {
    let (m, e) = split(rust, 'e');
    let e = parse_i64(e);
    format!("{m}e{}{}", sign_of(e), e.saturating_abs())
}

#[test]
fn exponential_differential() {
    let mut rng = Rng(0xE0E0_0000_0000_0003);
    for _ in 0..count(60_000) {
        let x = random_finite(&mut rng);
        if x == 0.0 {
            continue;
        }
        let f = rng.below(30) as usize;
        let ours = ok(to_exponential(x, Some(f as i64)));
        if is_tie(tail(&exact_digits(x), f.saturating_add(1))) {
            continue;
        }
        let want = js_exponent(&format!("{x:.f$e}"));
        assert_eq!(ours, want, "toExponential({x:e}, {f})");
        // And with `undefined`: the shortest digits.
        let s = ok(to_exponential(x, None));
        assert_eq!(string_to_number(&s).to_bits(), x.to_bits(), "{s}");
        if digits_agree(x) {
            assert_eq!(s, js_exponent(&format!("{x:e}")));
        }
    }
}

#[test]
fn precision_differential() {
    let mut rng = Rng(0x9EC1_0000_0000_0004);
    for _ in 0..count(60_000) {
        let x = random_finite(&mut rng);
        if x == 0.0 {
            continue;
        }
        let p = 1usize.saturating_add(rng.below(30) as usize);
        let ours = ok(to_precision(x, Some(p as i64)));
        if is_tie(tail(&exact_digits(x), p)) {
            continue;
        }
        let rust = format!("{:.*e}", p.saturating_sub(1), x.abs());
        let (m, e) = split(&rust, 'e');
        let e = parse_i64(e);
        let digs: String = m.chars().filter(|c| *c != '.').collect();
        let pi = p as i64;
        let body = if e < -6 || e >= pi {
            let mant = if p == 1 {
                digs.clone()
            } else {
                format!("{}.{}", head(&digs, 1), tail(&digs, 1))
            };
            format!("{mant}e{}{}", sign_of(e), e.saturating_abs())
        } else if e == pi.saturating_sub(1) {
            digs.clone()
        } else if e >= 0 {
            let at = usize::try_from(e.saturating_add(1)).unwrap_or(0);
            format!("{}.{}", head(&digs, at), tail(&digs, at))
        } else {
            format!("0.{}{digs}", zeros(e.saturating_add(1).saturating_neg()))
        };
        let want = if x < 0.0 { format!("-{body}") } else { body };
        assert_eq!(ours, want, "toPrecision({x:e}, {p})");
    }
}
