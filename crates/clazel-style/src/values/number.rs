//! Numbers, dimensions and their units: CSS Values 4 §5 (`<integer>`, `<number>`,
//! `<percentage>`), §6 (`<length>`) and §7.1 (`<angle>`), at
//! <https://www.w3.org/TR/2024/WD-css-values-4-20240312/>†.
//!
//! A number is kept as a whole count of millionths in an `i64` ([`Num`]), read once from the
//! strings "consume a number" builds (CSS Syntax 3 §4.3.12) with the rounding stated on
//! [`Num::from_parts`]. A used length is a whole count of 1/64 px in an `i32`
//! ([`to_px64`]). Both clamp: CSS Values 4 §5.1 lets an implementation clamp a value outside
//! the range it supports to the nearest value it supports.

/// Millionths in one.
pub const SCALE: i64 = 1_000_000;

/// The largest magnitude a [`Num`] holds, in millionths: one thousand million. Larger
/// values clamp to it (CSS Values 4 §5.1, "clamp to the closest supported value").
pub const MAX_NUM: i64 = 1_000_000_000 * SCALE;

/// The largest magnitude of a used length, in 1/64 px: 2^30 - 1, about 16.7 million px.
/// Larger lengths clamp to it, which leaves layout room to add two without overflow.
pub const MAX_PX64: i32 = (1 << 30) - 1;

/// A number as written: its value in millionths, rounded and clamped by
/// [`Num::from_parts`], and its type flag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Num {
    /// The value times [`SCALE`].
    pub millionths: i64,
    /// CSS Syntax 3's type flag: true for "integer".
    pub is_integer: bool,
}

/// The value of an ASCII digit, if it is one.
fn digit(c: u32) -> Option<u32> {
    c.checked_sub(0x30).filter(|d| *d <= 9)
}

/// `10^k` for `k <= 38`, the largest power that fits a `u128`.
fn pow10(k: u32) -> Option<u128> {
    10u128.checked_pow(k)
}

/// Clamp a count of millionths to [`MAX_NUM`].
fn clamp_num(v: i128) -> i64 {
    let m = i128::from(MAX_NUM);
    let c = if v > m {
        m
    } else if v < m.saturating_neg() {
        m.saturating_neg()
    } else {
        v
    };
    i64::try_from(c).unwrap_or(0)
}

impl Num {
    /// Zero, as an integer.
    pub const ZERO: Num = Num {
        millionths: 0,
        is_integer: true,
    };

    /// The number CSS Syntax 3 §4.3.12 step 6 means by "number part" and "exponent part"
    /// ("interpreting number part as a base-10 number", times 10 to the exponent), rounded
    /// to the nearest millionth, ties away from zero, and clamped to [`MAX_NUM`].
    ///
    /// Only the first 30 significant digits are read; later ones change the value by less
    /// than 10^-24 of it, and since a value that is not clamped is below 10^9, they can
    /// change the rounding only of a value within 10^-15 of a tie. An exponent above 10^6
    /// in magnitude is read as 10^6, which already clamps or rounds to zero. Code points that
    /// are not the digits, `.`, `+` and `-` the tokenizer puts there are ignored.
    pub fn from_parts(number_part: &[u32], exponent_part: &[u32], is_integer: bool) -> Num {
        let negative = number_part.first() == Some(&0x2D);
        // value = mantissa * 10^exp10.
        let mut mantissa: u128 = 0;
        let mut exp10: i64 = 0;
        let mut fraction = false;
        let limit = pow10(30).unwrap_or(u128::MAX);
        for &c in number_part {
            if c == 0x2E {
                fraction = true;
                continue;
            }
            let Some(d) = digit(c) else { continue };
            if mantissa < limit {
                mantissa = mantissa.saturating_mul(10).saturating_add(u128::from(d));
                if fraction {
                    exp10 = exp10.saturating_sub(1);
                }
            } else if !fraction {
                exp10 = exp10.saturating_add(1);
            }
        }
        let mut exponent: i64 = 0;
        for &c in exponent_part {
            if let Some(d) = digit(c) {
                exponent = exponent
                    .saturating_mul(10)
                    .saturating_add(i64::from(d))
                    .min(1_000_000);
            }
        }
        if exponent_part.first() == Some(&0x2D) {
            exponent = exponent.saturating_neg();
        }
        // millionths = mantissa * 10^(exp10 + exponent + 6).
        let k = exp10.saturating_add(exponent).saturating_add(6);
        let magnitude: u128 = if mantissa == 0 {
            0
        } else if k >= 0 {
            match u32::try_from(k).ok().and_then(pow10) {
                Some(p) => mantissa.saturating_mul(p),
                None => u128::MAX,
            }
        } else {
            match u32::try_from(k.unsigned_abs()).ok().and_then(pow10) {
                Some(p) => {
                    let q = mantissa.checked_div(p).unwrap_or(0);
                    let r = mantissa.checked_rem(p).unwrap_or(0);
                    if r.saturating_mul(2) >= p {
                        q.saturating_add(1)
                    } else {
                        q
                    }
                }
                None => 0,
            }
        };
        let m = i128::try_from(magnitude).unwrap_or(i128::MAX);
        let signed = if negative { m.saturating_neg() } else { m };
        Num {
            millionths: clamp_num(signed),
            is_integer,
        }
    }

    /// A whole number of units, as a [`Num`] (clamped).
    pub fn from_int(v: i64) -> Num {
        Num {
            millionths: clamp_num(i128::from(v).saturating_mul(i128::from(SCALE))),
            is_integer: true,
        }
    }

    /// True if the value is zero.
    pub fn is_zero(self) -> bool {
        self.millionths == 0
    }

    /// True if the value is below zero.
    pub fn is_negative(self) -> bool {
        self.millionths < 0
    }

    /// The value, if it is an integer of type "integer".
    pub fn integer(self) -> Option<i64> {
        if self.is_integer && self.millionths.checked_rem(SCALE) == Some(0) {
            self.millionths.checked_div(SCALE)
        } else {
            None
        }
    }

    /// The value rounded to the nearest whole number, ties toward positive infinity (CSS
    /// Values 4 §5.2 "round to the nearest integer").
    pub fn round(self) -> i64 {
        let floor = self.millionths.div_euclid(SCALE);
        let rem = self.millionths.rem_euclid(SCALE);
        if rem.saturating_mul(2) >= SCALE {
            floor.saturating_add(1)
        } else {
            floor
        }
    }
}

/// Append CSSOM's serialization of a number ("serialize a CSS component value", for
/// `<number>`): the shortest decimal form, here of the value in millionths, with no
/// exponent and no trailing zeros.
pub fn write_num(out: &mut String, n: Num) {
    let negative = n.millionths < 0;
    let abs = n.millionths.unsigned_abs();
    let scale = SCALE.unsigned_abs();
    let whole = abs.checked_div(scale).unwrap_or(0);
    let mut frac = abs.checked_rem(scale).unwrap_or(0);
    if negative && abs != 0 {
        out.push('-');
    }
    out.push_str(&whole.to_string());
    if frac != 0 {
        let mut digits = 6usize;
        while frac.checked_rem(10) == Some(0) {
            frac = frac.checked_div(10).unwrap_or(0);
            digits = digits.saturating_sub(1);
        }
        out.push('.');
        let text = frac.to_string();
        for _ in text.len()..digits {
            out.push('0');
        }
        out.push_str(&text);
    }
}

/// The units of `<length>` in the subset: CSS Values 4 §6.1 (`em`, `ex`, `rem`) and §6.2
/// (the absolute units). Viewport and container units are not in the subset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum LengthUnit {
    /// `px`.
    Px,
    /// `pt`, 1/72 in.
    Pt,
    /// `pc`, 12 pt.
    Pc,
    /// `in`, 96 px.
    In,
    /// `cm`, 96/2.54 px.
    Cm,
    /// `mm`, 1/10 cm.
    Mm,
    /// `Q`, 1/40 cm.
    Q,
    /// `em`, the font size.
    Em,
    /// `ex`, the x-height, taken as 0.5 em (CSS Values 4 §6.1.1 allows it "in the cases
    /// where it is impossible or impractical to determine the x-height").
    Ex,
    /// `rem`, the root element's font size.
    Rem,
}

/// Each unit's name, as CSSOM serializes it.
pub const LENGTH_UNITS: &[(&str, LengthUnit)] = &[
    ("px", LengthUnit::Px),
    ("pt", LengthUnit::Pt),
    ("pc", LengthUnit::Pc),
    ("in", LengthUnit::In),
    ("cm", LengthUnit::Cm),
    ("mm", LengthUnit::Mm),
    ("q", LengthUnit::Q),
    ("em", LengthUnit::Em),
    ("ex", LengthUnit::Ex),
    ("rem", LengthUnit::Rem),
];

impl LengthUnit {
    /// The unit's canonical name (CSS Values 4 writes `Q` in upper case; units are ASCII
    /// case-insensitive, and CSSOM serializes the canonical form).
    pub fn name(self) -> &'static str {
        match self {
            LengthUnit::Px => "px",
            LengthUnit::Pt => "pt",
            LengthUnit::Pc => "pc",
            LengthUnit::In => "in",
            LengthUnit::Cm => "cm",
            LengthUnit::Mm => "mm",
            LengthUnit::Q => "Q",
            LengthUnit::Em => "em",
            LengthUnit::Ex => "ex",
            LengthUnit::Rem => "rem",
        }
    }

    /// Pixels per unit as (numerator, denominator), for the absolute units (CSS Values 4
    /// §6.2, table of absolute lengths); `None` for the font-relative ones.
    pub fn px_ratio(self) -> Option<(i128, i128)> {
        match self {
            LengthUnit::Px => Some((1, 1)),
            LengthUnit::Pt => Some((4, 3)),
            LengthUnit::Pc => Some((16, 1)),
            LengthUnit::In => Some((96, 1)),
            // 96 / 2.54 = 4800 / 127.
            LengthUnit::Cm => Some((4800, 127)),
            LengthUnit::Mm => Some((480, 127)),
            // 96 / 101.6 = 120 / 127.
            LengthUnit::Q => Some((120, 127)),
            LengthUnit::Em | LengthUnit::Ex | LengthUnit::Rem => None,
        }
    }
}

/// A `<length>` as written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Length {
    /// The number.
    pub value: Num,
    /// The unit.
    pub unit: LengthUnit,
}

/// `n * num / den` rounded to the nearest whole number, ties away from zero, as 1/64 px
/// clamped to [`MAX_PX64`]. `den` must be positive; zero gives zero.
fn scale_px64(millionths: i128, num: i128, den: i128) -> i32 {
    // px64 = millionths * 64 * num / (den * SCALE).
    let n = millionths.saturating_mul(64).saturating_mul(num);
    let d = den.saturating_mul(i128::from(SCALE));
    if d <= 0 {
        return 0;
    }
    let q = n.checked_div(d).unwrap_or(0);
    let r = n.checked_rem(d).unwrap_or(0);
    let rounded = if r.unsigned_abs().saturating_mul(2) >= d.unsigned_abs() {
        if n < 0 {
            q.saturating_sub(1)
        } else {
            q.saturating_add(1)
        }
    } else {
        q
    };
    let max = i128::from(MAX_PX64);
    i32::try_from(rounded.clamp(max.saturating_neg(), max)).unwrap_or(0)
}

/// A length in 1/64 px (CSS Values 4 §6, "absolute lengths" and "font-relative lengths"),
/// given the used font size of the element (`em_px64`) and of the root (`rem_px64`), both in
/// 1/64 px. Rounded to the nearest 1/64 px, ties away from zero, and clamped to
/// [`MAX_PX64`]; never overflows.
pub fn to_px64(length: Length, em_px64: i32, rem_px64: i32) -> i32 {
    let v = i128::from(length.value.millionths);
    match length.unit.px_ratio() {
        Some((num, den)) => scale_px64(v, num, den),
        None => {
            // In px: millionths * base64 / 64, so px64 = millionths * base64 / SCALE,
            // which is scale_px64 with num = base64 and den = 64.
            let (base, den) = match length.unit {
                LengthUnit::Rem => (rem_px64, 64),
                LengthUnit::Ex => (em_px64, 128),
                _ => (em_px64, 64),
            };
            scale_px64(v, i128::from(base), den)
        }
    }
}

/// `p` percent of `basis_px64`, in 1/64 px, rounded and clamped as [`to_px64`].
pub fn percentage_px64(p: Num, basis_px64: i32) -> i32 {
    scale_px64(i128::from(p.millionths), i128::from(basis_px64), 6400)
}

/// The units of `<angle>`: CSS Values 4 §7.1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum AngleUnit {
    /// `deg`.
    Deg,
    /// `grad`, 400 to the turn.
    Grad,
    /// `rad`, 2π to the turn.
    Rad,
    /// `turn`.
    Turn,
}

/// Each angle unit's name.
pub const ANGLE_UNITS: &[(&str, AngleUnit)] = &[
    ("deg", AngleUnit::Deg),
    ("grad", AngleUnit::Grad),
    ("rad", AngleUnit::Rad),
    ("turn", AngleUnit::Turn),
];

/// An `<angle>` as written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Angle {
    /// The number.
    pub value: Num,
    /// The unit.
    pub unit: AngleUnit,
}

impl AngleUnit {
    /// The unit's name.
    pub fn name(self) -> &'static str {
        match self {
            AngleUnit::Deg => "deg",
            AngleUnit::Grad => "grad",
            AngleUnit::Rad => "rad",
            AngleUnit::Turn => "turn",
        }
    }
}

/// The angle in millionths of a degree, clamped to [`MAX_NUM`]. A radian is taken as
/// 57.295779513 degrees, 180/π to nine places.
pub fn degrees(a: Angle) -> i64 {
    let v = i128::from(a.value.millionths);
    let d = match a.unit {
        AngleUnit::Deg => v,
        AngleUnit::Grad => v.saturating_mul(9).checked_div(10).unwrap_or(0),
        AngleUnit::Rad => v
            .saturating_mul(57_295_779_513)
            .checked_div(1_000_000_000)
            .unwrap_or(0),
        AngleUnit::Turn => v.saturating_mul(360),
    };
    clamp_num(d)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(t: &str) -> Vec<u32> {
        t.chars().map(u32::from).collect()
    }

    fn num(part: &str, exp: &str) -> i64 {
        Num::from_parts(&s(part), &s(exp), exp.is_empty() && !part.contains('.')).millionths
    }

    #[test]
    fn reads_numbers() {
        assert_eq!(num("10", ""), 10_000_000);
        assert_eq!(num("-1.5", ""), -1_500_000);
        assert_eq!(num("+.25", ""), 250_000);
        assert_eq!(num("1", "3"), 1_000_000_000);
        assert_eq!(num("1", "-3"), 1_000);
        assert_eq!(num("1", "-7"), 0);
        assert_eq!(num("5", "-7"), 1);
        assert_eq!(num("-5", "-7"), -1);
        assert_eq!(num("1", "100"), MAX_NUM);
        assert_eq!(num("-1", "1000000000000"), -MAX_NUM);
        assert_eq!(num("0.0000004", ""), 0);
        assert_eq!(num("123456789012345678901234567890123", "-30"), 123_456_789);
    }

    #[test]
    fn writes_numbers() {
        let w = |m| {
            let mut o = String::new();
            write_num(
                &mut o,
                Num {
                    millionths: m,
                    is_integer: false,
                },
            );
            o
        };
        assert_eq!(w(0), "0");
        assert_eq!(w(1_500_000), "1.5");
        assert_eq!(w(-250_000), "-0.25");
        assert_eq!(w(1), "0.000001");
        assert_eq!(w(150_250_000), "150.25");
        assert_eq!(w(i64::MIN), "-9223372036854.775808");
    }

    #[test]
    fn converts_lengths() {
        let l = |m: i64, unit| Length {
            value: Num {
                millionths: m,
                is_integer: false,
            },
            unit,
        };
        assert_eq!(to_px64(l(10 * SCALE, LengthUnit::Px), 0, 0), 640);
        assert_eq!(to_px64(l(12 * SCALE, LengthUnit::Pt), 0, 0), 1024);
        assert_eq!(to_px64(l(SCALE, LengthUnit::In), 0, 0), 96 * 64);
        assert_eq!(to_px64(l(254 * SCALE / 100, LengthUnit::Cm), 0, 0), 96 * 64);
        assert_eq!(to_px64(l(2 * SCALE, LengthUnit::Em), 16 * 64, 0), 32 * 64);
        assert_eq!(to_px64(l(2 * SCALE, LengthUnit::Ex), 16 * 64, 0), 16 * 64);
        assert_eq!(to_px64(l(MAX_NUM, LengthUnit::In), 0, 0), MAX_PX64);
        assert_eq!(to_px64(l(-MAX_NUM, LengthUnit::Em), i32::MAX, 0), -MAX_PX64);
        assert_eq!(to_px64(l(-15_625, LengthUnit::Px), 0, 0), -1);
        assert_eq!(to_px64(l(-7_812, LengthUnit::Px), 0, 0), 0);
        assert_eq!(percentage_px64(Num::from_int(50), 640), 320);
    }
}
