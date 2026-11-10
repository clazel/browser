//! `<color>` of the subset: CSS Color 4, <https://www.w3.org/TR/2025/CRD-css-color-4-20250424/>†:
//! §4.1 `<color>` (the keywords `transparent` and `currentcolor`), §5.1 and §5.2 `rgb()` and
//! `rgba()` in their legacy and modern syntaxes, §5.2 hex notation, §6.1 named colours, §7
//! `hsl()` and `hsla()`, and §15 (serializing sRGB values). With the Quirks Mode Standard's
//! hashless hex colour quirk (§3.6†).
//!
//! Modelling choices:
//! - A colour is resolved when parsed, to 8-bit sRGB channels and alpha, as browsers store
//!   specified sRGB colours: a channel is clamped to [0, 255] and rounded to the nearest
//!   integer, ties toward +∞ (§5.1 "rounded to the nearest integer"), and alpha is
//!   `round(alpha × 255)`. `hsl()` converts to RGB first (§7.1's algorithm, in millionths).
//! - A named colour keeps its name, which CSSOM serializes as written in lower case, as
//!   every engine the WPT cases expect does; other forms serialize as `rgb()` or `rgba()`.
//! - `none` in the modern syntax is zero (§4.4, "missing components" in legacy colour
//!   spaces).
//! - System colours, `hwb()`, `lab()`, `lch()`, `oklab()`, `oklch()`, `color()`,
//!   `color-mix()`, relative colours and `light-dark()` are not in the subset.

use super::items::{Cursor, Item, Src, eq_ignore_case, lookup, lower};
use super::number::{ANGLE_UNITS, Angle, Num, SCALE, degrees};

/// A specified colour.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Color {
    /// `currentcolor`.
    CurrentColor,
    /// `transparent`: rgba(0, 0, 0, 0).
    Transparent,
    /// A named colour (§6.1), by its index in [`NAMED`].
    Named(u8),
    /// Red, green, blue and alpha.
    Rgba([u8; 4]),
}

impl Color {
    /// The red, green, blue and alpha this colour resolves to, or `None` for
    /// `currentcolor`.
    pub fn rgba(self) -> Option<[u8; 4]> {
        match self {
            Color::CurrentColor => None,
            Color::Transparent => Some([0, 0, 0, 0]),
            Color::Named(i) => NAMED
                .get(usize::from(i))
                .map(|(_, rgb)| [rgb[0], rgb[1], rgb[2], 255]),
            Color::Rgba(c) => Some(c),
        }
    }
}

/// §6.1 the named colours, with their sRGB values.
pub const NAMED: &[(&str, [u8; 3])] = &[
    ("aliceblue", [240, 248, 255]),
    ("antiquewhite", [250, 235, 215]),
    ("aqua", [0, 255, 255]),
    ("aquamarine", [127, 255, 212]),
    ("azure", [240, 255, 255]),
    ("beige", [245, 245, 220]),
    ("bisque", [255, 228, 196]),
    ("black", [0, 0, 0]),
    ("blanchedalmond", [255, 235, 205]),
    ("blue", [0, 0, 255]),
    ("blueviolet", [138, 43, 226]),
    ("brown", [165, 42, 42]),
    ("burlywood", [222, 184, 135]),
    ("cadetblue", [95, 158, 160]),
    ("chartreuse", [127, 255, 0]),
    ("chocolate", [210, 105, 30]),
    ("coral", [255, 127, 80]),
    ("cornflowerblue", [100, 149, 237]),
    ("cornsilk", [255, 248, 220]),
    ("crimson", [220, 20, 60]),
    ("cyan", [0, 255, 255]),
    ("darkblue", [0, 0, 139]),
    ("darkcyan", [0, 139, 139]),
    ("darkgoldenrod", [184, 134, 11]),
    ("darkgray", [169, 169, 169]),
    ("darkgreen", [0, 100, 0]),
    ("darkgrey", [169, 169, 169]),
    ("darkkhaki", [189, 183, 107]),
    ("darkmagenta", [139, 0, 139]),
    ("darkolivegreen", [85, 107, 47]),
    ("darkorange", [255, 140, 0]),
    ("darkorchid", [153, 50, 204]),
    ("darkred", [139, 0, 0]),
    ("darksalmon", [233, 150, 122]),
    ("darkseagreen", [143, 188, 143]),
    ("darkslateblue", [72, 61, 139]),
    ("darkslategray", [47, 79, 79]),
    ("darkslategrey", [47, 79, 79]),
    ("darkturquoise", [0, 206, 209]),
    ("darkviolet", [148, 0, 211]),
    ("deeppink", [255, 20, 147]),
    ("deepskyblue", [0, 191, 255]),
    ("dimgray", [105, 105, 105]),
    ("dimgrey", [105, 105, 105]),
    ("dodgerblue", [30, 144, 255]),
    ("firebrick", [178, 34, 34]),
    ("floralwhite", [255, 250, 240]),
    ("forestgreen", [34, 139, 34]),
    ("fuchsia", [255, 0, 255]),
    ("gainsboro", [220, 220, 220]),
    ("ghostwhite", [248, 248, 255]),
    ("gold", [255, 215, 0]),
    ("goldenrod", [218, 165, 32]),
    ("gray", [128, 128, 128]),
    ("green", [0, 128, 0]),
    ("greenyellow", [173, 255, 47]),
    ("grey", [128, 128, 128]),
    ("honeydew", [240, 255, 240]),
    ("hotpink", [255, 105, 180]),
    ("indianred", [205, 92, 92]),
    ("indigo", [75, 0, 130]),
    ("ivory", [255, 255, 240]),
    ("khaki", [240, 230, 140]),
    ("lavender", [230, 230, 250]),
    ("lavenderblush", [255, 240, 245]),
    ("lawngreen", [124, 252, 0]),
    ("lemonchiffon", [255, 250, 205]),
    ("lightblue", [173, 216, 230]),
    ("lightcoral", [240, 128, 128]),
    ("lightcyan", [224, 255, 255]),
    ("lightgoldenrodyellow", [250, 250, 210]),
    ("lightgray", [211, 211, 211]),
    ("lightgreen", [144, 238, 144]),
    ("lightgrey", [211, 211, 211]),
    ("lightpink", [255, 182, 193]),
    ("lightsalmon", [255, 160, 122]),
    ("lightseagreen", [32, 178, 170]),
    ("lightskyblue", [135, 206, 250]),
    ("lightslategray", [119, 136, 153]),
    ("lightslategrey", [119, 136, 153]),
    ("lightsteelblue", [176, 196, 222]),
    ("lightyellow", [255, 255, 224]),
    ("lime", [0, 255, 0]),
    ("limegreen", [50, 205, 50]),
    ("linen", [250, 240, 230]),
    ("magenta", [255, 0, 255]),
    ("maroon", [128, 0, 0]),
    ("mediumaquamarine", [102, 205, 170]),
    ("mediumblue", [0, 0, 205]),
    ("mediumorchid", [186, 85, 211]),
    ("mediumpurple", [147, 112, 219]),
    ("mediumseagreen", [60, 179, 113]),
    ("mediumslateblue", [123, 104, 238]),
    ("mediumspringgreen", [0, 250, 154]),
    ("mediumturquoise", [72, 209, 204]),
    ("mediumvioletred", [199, 21, 133]),
    ("midnightblue", [25, 25, 112]),
    ("mintcream", [245, 255, 250]),
    ("mistyrose", [255, 228, 225]),
    ("moccasin", [255, 228, 181]),
    ("navajowhite", [255, 222, 173]),
    ("navy", [0, 0, 128]),
    ("oldlace", [253, 245, 230]),
    ("olive", [128, 128, 0]),
    ("olivedrab", [107, 142, 35]),
    ("orange", [255, 165, 0]),
    ("orangered", [255, 69, 0]),
    ("orchid", [218, 112, 214]),
    ("palegoldenrod", [238, 232, 170]),
    ("palegreen", [152, 251, 152]),
    ("paleturquoise", [175, 238, 238]),
    ("palevioletred", [219, 112, 147]),
    ("papayawhip", [255, 239, 213]),
    ("peachpuff", [255, 218, 185]),
    ("peru", [205, 133, 63]),
    ("pink", [255, 192, 203]),
    ("plum", [221, 160, 221]),
    ("powderblue", [176, 224, 230]),
    ("purple", [128, 0, 128]),
    ("rebeccapurple", [102, 51, 153]),
    ("red", [255, 0, 0]),
    ("rosybrown", [188, 143, 143]),
    ("royalblue", [65, 105, 225]),
    ("saddlebrown", [139, 69, 19]),
    ("salmon", [250, 128, 114]),
    ("sandybrown", [244, 164, 96]),
    ("seagreen", [46, 139, 87]),
    ("seashell", [255, 245, 238]),
    ("sienna", [160, 82, 45]),
    ("silver", [192, 192, 192]),
    ("skyblue", [135, 206, 235]),
    ("slateblue", [106, 90, 205]),
    ("slategray", [112, 128, 144]),
    ("slategrey", [112, 128, 144]),
    ("snow", [255, 250, 250]),
    ("springgreen", [0, 255, 127]),
    ("steelblue", [70, 130, 180]),
    ("tan", [210, 180, 140]),
    ("teal", [0, 128, 128]),
    ("thistle", [216, 191, 216]),
    ("tomato", [255, 99, 71]),
    ("turquoise", [64, 224, 208]),
    ("violet", [238, 130, 238]),
    ("wheat", [245, 222, 179]),
    ("white", [255, 255, 255]),
    ("whitesmoke", [245, 245, 245]),
    ("yellow", [255, 255, 0]),
    ("yellowgreen", [154, 205, 50]),
];

/// The value of a hex digit.
fn hex(c: u32) -> Option<u8> {
    let d = match lower(c) {
        c @ 0x30..=0x39 => c.checked_sub(0x30),
        c @ 0x61..=0x66 => c.checked_sub(0x57),
        _ => None,
    }?;
    u8::try_from(d).ok()
}

/// §5.2 hex notation: 3, 4, 6 or 8 hex digits.
pub fn from_hex(s: &[u32]) -> Option<Color> {
    let mut d = [0u8; 8];
    for (slot, &c) in d.iter_mut().zip(s.iter()) {
        *slot = hex(c)?;
    }
    if s.len() > 8 {
        return None;
    }
    let [a, b, c, e, f, g, h, i] = d;
    let one = |x: u8| x.saturating_mul(17);
    let two = |x: u8, y: u8| x.saturating_mul(16).saturating_add(y);
    match s.len() {
        3 => Some(Color::Rgba([one(a), one(b), one(c), 255])),
        4 => Some(Color::Rgba([one(a), one(b), one(c), one(e)])),
        6 => Some(Color::Rgba([two(a, b), two(c, e), two(f, g), 255])),
        8 => Some(Color::Rgba([two(a, b), two(c, e), two(f, g), two(h, i)])),
        _ => None,
    }
}

/// A fraction in millionths, clamped to [0, 1], as a channel: `round(f × 255)`.
fn channel_of_fraction(f: i64) -> u8 {
    let f = i128::from(f.clamp(0, SCALE));
    let v = f
        .saturating_mul(255)
        .saturating_add(i128::from(SCALE / 2))
        .checked_div(i128::from(SCALE))
        .unwrap_or(0);
    u8::try_from(v.clamp(0, 255)).unwrap_or(0)
}

/// A number, clamped to [0, 255] and rounded (§5.1).
fn channel_of_number(n: Num) -> u8 {
    u8::try_from(n.round().clamp(0, 255)).unwrap_or(0)
}

/// A percentage of 255.
fn channel_of_percentage(p: Num) -> u8 {
    channel_of_fraction(p.millionths.checked_div(100).unwrap_or(0))
}

/// One argument of `rgb()`, `hsl()` or their modern forms.
#[derive(Clone, Copy)]
enum Arg {
    Number(Num),
    Percentage(Num),
    Angle(Angle),
    None,
}

fn arg(src: Src<'_>, item: Item) -> Option<Arg> {
    match item {
        Item::Number { value, .. } => Some(Arg::Number(value)),
        Item::Percentage(p) => Some(Arg::Percentage(p)),
        Item::Dimension { value, unit, .. } => {
            lookup(ANGLE_UNITS, src.str(unit)).map(|unit| Arg::Angle(Angle { value, unit }))
        }
        Item::Ident(s) if eq_ignore_case(src.str(s), "none") => Some(Arg::None),
        _ => None,
    }
}

/// The arguments of a colour function: up to four values, and whether they were separated
/// by commas (the legacy syntax) or by spaces with an optional `/` before alpha (modern).
fn read_args(mut c: Cursor<'_>) -> Option<([Arg; 4], usize, bool)> {
    let mut out = [Arg::None; 4];
    let mut n = 0usize;
    let first = c.bump()?;
    out[0] = arg(c.src, first)?;
    n = n.saturating_add(1);
    let legacy = c.peek() == Some(Item::Comma);
    while !c.at_end() {
        if legacy {
            if !c.comma() {
                return None;
            }
        } else if n == 3 && !c.delim(0x2F) {
            return None;
        }
        let item = c.bump()?;
        let slot = out.get_mut(n)?;
        *slot = arg(c.src, item)?;
        n = n.saturating_add(1);
    }
    // The legacy syntax has no `none`; the modern one needs three or four.
    if legacy && out.iter().take(n).any(|a| matches!(a, Arg::None)) {
        return None;
    }
    if n < 3 {
        return None;
    }
    Some((out, n, legacy))
}

fn alpha_arg(a: Arg) -> Option<u8> {
    match a {
        Arg::Number(v) => Some(channel_of_fraction(v.millionths)),
        Arg::Percentage(p) => Some(channel_of_percentage(p)),
        Arg::None => Some(0),
        Arg::Angle(_) => None,
    }
}

/// §5.1 `rgb()` and `rgba()`, which are the same function.
fn rgb(c: Cursor<'_>) -> Option<Color> {
    let (args, n, legacy) = read_args(c)?;
    let [r, g, b, a] = args;
    let channels = [r, g, b];
    if legacy {
        // "<percentage>#{3} , <alpha-value>? ) | <number>#{3} , <alpha-value>?"
        let all_numbers = channels.iter().all(|a| matches!(a, Arg::Number(_)));
        let all_percentages = channels.iter().all(|a| matches!(a, Arg::Percentage(_)));
        if !all_numbers && !all_percentages {
            return None;
        }
    }
    let mut out = [0u8; 4];
    for (slot, ch) in out.iter_mut().zip(channels) {
        *slot = match ch {
            Arg::Number(v) => channel_of_number(v),
            Arg::Percentage(p) => channel_of_percentage(p),
            Arg::None => 0,
            Arg::Angle(_) => return None,
        };
    }
    out[3] = if n == 4 { alpha_arg(a)? } else { 255 };
    Some(Color::Rgba(out))
}

/// §7.1 "converting HSL colors to sRGB colors", with every quantity in millionths: `h6`
/// the hue in sixths of a turn in [0, 6), `s` and `l` in [0, 1].
fn hsl_to_rgb(h6: i64, s: i64, l: i64) -> [u8; 3] {
    // The text's `f(n) = l - a·max(-1, min(k - 3, 9 - k, 1))`, `k = (n + h/30) mod 12`,
    // `a = s·min(l, 1 - l)`.
    let a = s
        .saturating_mul(l.min(SCALE.saturating_sub(l)))
        .checked_div(SCALE)
        .unwrap_or(0);
    let twelve = SCALE.saturating_mul(12);
    let f = |n: i64| {
        // h/30 = h6 × 2 (h6 is in sixths of a turn, so h in degrees is 60·h6).
        let k = n
            .saturating_mul(SCALE)
            .saturating_add(h6.saturating_mul(2))
            .rem_euclid(twelve);
        let three = SCALE.saturating_mul(3);
        let nine = SCALE.saturating_mul(9);
        let m = k
            .saturating_sub(three)
            .min(nine.saturating_sub(k))
            .min(SCALE)
            .max(SCALE.saturating_neg());
        let v = l.saturating_sub(a.saturating_mul(m).checked_div(SCALE).unwrap_or(0));
        channel_of_fraction(v)
    };
    [f(0), f(8), f(4)]
}

/// §7 `hsl()` and `hsla()`.
fn hsl(c: Cursor<'_>) -> Option<Color> {
    let (args, n, legacy) = read_args(c)?;
    let [h, s, l, a] = args;
    // The hue: a number of degrees, or an angle.
    let deg = match h {
        Arg::Number(v) => v.millionths,
        Arg::Angle(angle) => degrees(angle),
        Arg::None => 0,
        Arg::Percentage(_) => return None,
    };
    let h6 = deg
        .rem_euclid(SCALE.saturating_mul(360))
        .checked_div(60)
        .unwrap_or(0);
    // Saturation and lightness: percentages; numbers too in the modern syntax.
    let fraction = |x: Arg| -> Option<i64> {
        match x {
            Arg::Percentage(p) => Some(p.millionths.checked_div(100).unwrap_or(0)),
            Arg::Number(v) if !legacy => Some(v.millionths.checked_div(100).unwrap_or(0)),
            Arg::None => Some(0),
            _ => None,
        }
    };
    let s = fraction(s)?.clamp(0, SCALE);
    let l = fraction(l)?.clamp(0, SCALE);
    let [r, g, b] = hsl_to_rgb(h6, s, l);
    let alpha = if n == 4 { alpha_arg(a)? } else { 255 };
    Some(Color::Rgba([r, g, b, alpha]))
}

/// `<color>` (§4.1), from the next item of `c`; with `quirky`, also the Quirks Mode
/// Standard's `<quirky-color>`.
pub fn parse_color(c: &mut Cursor<'_>, quirky: bool) -> Option<Color> {
    let save = c.pos;
    let item = c.peek()?;
    let color = match item {
        Item::Hash(s) => {
            c.bump();
            from_hex(c.src.str(s))
        }
        Item::Ident(s) => {
            c.bump();
            let name = c.src.str(s);
            if eq_ignore_case(name, "currentcolor") {
                Some(Color::CurrentColor)
            } else if eq_ignore_case(name, "transparent") {
                Some(Color::Transparent)
            } else if let Some(i) = NAMED.iter().position(|(n, _)| eq_ignore_case(name, n)) {
                u8::try_from(i).ok().map(Color::Named)
            } else if quirky {
                quirky_ident(name)
            } else {
                None
            }
        }
        Item::Function { .. } => {
            let (name, args) = c.function()?;
            if eq_ignore_case(name, "rgb") || eq_ignore_case(name, "rgba") {
                rgb(args)
            } else if eq_ignore_case(name, "hsl") || eq_ignore_case(name, "hsla") {
                hsl(args)
            } else {
                None
            }
        }
        Item::Number {
            value,
            repr,
            signed,
        } if quirky => {
            c.bump();
            quirky_number(c.src.str(repr), value, signed, &[])
        }
        Item::Dimension {
            value,
            unit,
            repr,
            signed,
        } if quirky => {
            c.bump();
            quirky_number(c.src.str(repr), value, signed, c.src.str(unit))
        }
        _ => None,
    };
    if color.is_none() {
        c.pos = save;
    }
    color
}

/// Quirks Mode §3.6†: an ident of 3 or 6 hex digits is that hex colour.
fn quirky_ident(s: &[u32]) -> Option<Color> {
    if s.len() == 3 || s.len() == 6 {
        from_hex(s)
    } else {
        None
    }
}

/// Quirks Mode §3.6†: a number or dimension token with the integer type flag and not
/// negative (a `+` sign is allowed and is not part of the digits); its digits (and the
/// unit's code points) padded on the left with zeros to six, which must then be six hex
/// digits. The text reads the token's representation; this reads the
/// number part and the unit after escapes are resolved (a modelling choice: a unit written
/// with an escape is read as the code point it means).
fn quirky_number(digits: &[u32], value: Num, signed: bool, unit: &[u32]) -> Option<Color> {
    let digits = if signed {
        // The sign is "+": a "-" makes a negative number, or "-0", refused below.
        if digits.first() != Some(&0x2B) {
            return None;
        }
        digits.get(1..).unwrap_or_default()
    } else {
        digits
    };
    if !value.is_integer || value.is_negative() {
        return None;
    }
    let total = digits.len().saturating_add(unit.len());
    if total > 6 {
        return None;
    }
    let mut six = [0x30u32; 6];
    let pad = 6usize.saturating_sub(total);
    for (slot, &c) in six
        .iter_mut()
        .skip(pad)
        .zip(digits.iter().chain(unit.iter()))
    {
        *slot = c;
    }
    from_hex(&six)
}

/// The shortest decimal of at most three places that rounds back to `a / 255`: CSS Color 4
/// §15.2† serializes alpha "rounded to 2 decimal places if that round-trips, else 3", which
/// is what engines do for 8-bit alpha.
fn write_alpha(out: &mut String, a: u8) {
    let a = u32::from(a);
    // Hundredths, rounded half up.
    let hundredths = a
        .saturating_mul(100)
        .saturating_add(127)
        .checked_div(255)
        .unwrap_or(0);
    let back = hundredths
        .saturating_mul(255)
        .saturating_add(50)
        .checked_div(100)
        .unwrap_or(0);
    let (value, places) = if back == a {
        (hundredths, 2u32)
    } else {
        (
            a.saturating_mul(1000)
                .saturating_add(127)
                .checked_div(255)
                .unwrap_or(0),
            3u32,
        )
    };
    let unit = 10u32.saturating_pow(places);
    let whole = value.checked_div(unit).unwrap_or(0);
    let mut frac = value.checked_rem(unit).unwrap_or(0);
    out.push_str(&whole.to_string());
    if frac != 0 {
        let mut digits = places;
        while frac.checked_rem(10) == Some(0) {
            frac = frac.checked_div(10).unwrap_or(0);
            digits = digits.saturating_sub(1);
        }
        out.push('.');
        let text = frac.to_string();
        for _ in (text.len() as u32)..digits {
            out.push('0');
        }
        out.push_str(&text);
    }
}

/// CSSOM's serialization of a specified colour: a named colour or keyword as its name,
/// anything else as `rgb(r, g, b)` or `rgba(r, g, b, a)` (CSS Color 4 §15.2†).
pub fn write_color(out: &mut String, c: Color) {
    match c {
        Color::CurrentColor => out.push_str("currentcolor"),
        Color::Transparent => out.push_str("transparent"),
        Color::Named(i) => out.push_str(NAMED.get(usize::from(i)).map_or("black", |(n, _)| n)),
        Color::Rgba([r, g, b, a]) => {
            if a == 255 {
                out.push_str(&format!("rgb({r}, {g}, {b})"));
            } else {
                out.push_str(&format!("rgba({r}, {g}, {b}, "));
                write_alpha(out, a);
                out.push(')');
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::items::{Cursor, Values};
    use super::*;

    fn color(s: &str, quirky: bool) -> Option<String> {
        let input: Vec<u32> = s.chars().map(u32::from).collect();
        let v = Values::parse(&input)?;
        let mut c = Cursor::new(v.src());
        let parsed = parse_color(&mut c, quirky)?;
        if !c.at_end() {
            return None;
        }
        let mut out = String::new();
        write_color(&mut out, parsed);
        Some(out)
    }

    #[test]
    fn parses_and_serializes() {
        let cases = [
            ("red", "red"),
            ("ReD", "red"),
            ("#234", "rgb(34, 51, 68)"),
            ("#FEDCBA", "rgb(254, 220, 186)"),
            ("#fff8", "rgba(255, 255, 255, 0.533)"),
            ("rgb(100%, 0%, 0%)", "rgb(255, 0, 0)"),
            ("rgba(2, 3, 4, 50%)", "rgba(2, 3, 4, 0.5)"),
            ("rgb(2 3 4 / 0.5)", "rgba(2, 3, 4, 0.5)"),
            ("rgb(-2, 3, 4)", "rgb(0, 3, 4)"),
            ("rgb(100, 200, 300)", "rgb(100, 200, 255)"),
            ("rgb(20, 10, 0, -10)", "rgba(20, 10, 0, 0)"),
            ("hsl(120, 100%, 50%)", "rgb(0, 255, 0)"),
            ("hsla(120, 100%, 50%, 0.25)", "rgba(0, 255, 0, 0.25)"),
            ("hsl(0.5turn 100% 25%)", "rgb(0, 128, 128)"),
            ("transparent", "transparent"),
            ("currentColor", "currentcolor"),
        ];
        for (input, want) in cases {
            assert_eq!(color(input, false).as_deref(), Some(want), "{input}");
        }
        for bad in [
            "#ff",
            "#fffff",
            "rgb(1, 2)",
            "rgb(1, 2%, 3)",
            "rgb(1 2 3 4)",
            "nope",
        ] {
            assert_eq!(color(bad, false), None, "{bad}");
        }
    }

    #[test]
    fn the_hashless_quirk() {
        assert_eq!(color("123", true).as_deref(), Some("rgb(0, 1, 35)"));
        assert_eq!(color("abc", true).as_deref(), Some("rgb(170, 187, 204)"));
        assert_eq!(color("1ab", true).as_deref(), Some("rgb(0, 1, 171)"));
        assert_eq!(color("123", false), None);
        assert_eq!(color("+123", true).as_deref(), Some("rgb(0, 1, 35)"));
        assert_eq!(color("-123", true), None);
        assert_eq!(color("-0", true), None);
        assert_eq!(color("1.5", true), None);
        assert_eq!(color("abcd", true), None);
        assert_eq!(color("1234567", true), None);
    }
}
