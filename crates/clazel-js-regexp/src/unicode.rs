//! The Unicode data the matcher reads: case canonicalization (ECMA-262
//! §22.2.2.7.3† `Canonicalize`), the equivalence classes it induces, and the
//! property sets of `\p{..}` (§22.2.2.9†, UnicodePropertyValueExpression).
//!
//! The tables are in [`crate::tables`], generated from the vendored UCD. Every
//! lookup is a bisection written here, with a loop that provably ends
//! (`lo` grows or `hi` shrinks on every pass), so that Kani can check it.

use crate::tables;

/// Finds `key` in a table of pairs sorted by their first element.
fn find_pair(table: &[(u32, u32)], key: u32) -> Option<u32> {
    let mut lo = 0usize;
    let mut hi = table.len();
    while lo < hi {
        let mid = lo.saturating_add(hi.saturating_sub(lo) / 2);
        let &(k, v) = table.get(mid)?;
        if k == key {
            return Some(v);
        }
        if k < key {
            lo = mid.saturating_add(1);
        } else {
            hi = mid;
        }
    }
    None
}

/// The index of the first element of `table` (sorted by first element) whose
/// first element is at least `key`.
fn lower_bound(table: &[(u32, u32)], key: u32) -> usize {
    let mut lo = 0usize;
    let mut hi = table.len();
    while lo < hi {
        let mid = lo.saturating_add(hi.saturating_sub(lo) / 2);
        match table.get(mid) {
            Some(&(k, _)) if k < key => lo = mid.saturating_add(1),
            _ => hi = mid,
        }
    }
    lo
}

/// The range of `ranges` (sorted, disjoint) that holds `c`, as its index.
fn range_index<T: Copy>(ranges: &[T], first: impl Fn(T) -> u32, c: u32) -> Option<usize> {
    // The last range whose first element is at most `c`.
    let mut lo = 0usize;
    let mut hi = ranges.len();
    while lo < hi {
        let mid = lo.saturating_add(hi.saturating_sub(lo) / 2);
        match ranges.get(mid) {
            Some(&r) if first(r) <= c => lo = mid.saturating_add(1),
            _ => hi = mid,
        }
    }
    lo.checked_sub(1)
}

/// Whether `c` is in one of `ranges` (first, last), sorted and disjoint.
#[must_use]
pub fn in_ranges(ranges: &[(u32, u32)], c: u32) -> bool {
    range_index(ranges, |r| r.0, c)
        .and_then(|i| ranges.get(i))
        .is_some_and(|&(_, last)| c <= last)
}

/// Simple Case Folding of `c` (`CaseFolding.txt`, statuses `C` and `S`): what
/// `Canonicalize` returns with `u` or `v` (§22.2.2.7.3† step 2.a).
#[must_use]
pub fn simple_fold(c: u32) -> u32 {
    find_pair(tables::SIMPLE_FOLD, c).unwrap_or(c)
}

/// `Canonicalize` without `u` or `v` of the code unit `c`
/// (§22.2.2.7.3† steps 3 to 7): `toUppercase` of it if that is one code unit,
/// unless that would turn a non-ASCII code unit into an ASCII one.
#[must_use]
pub fn canonicalize_unit(c: u32) -> u32 {
    find_pair(tables::UPPER, c).unwrap_or(c)
}

/// `Canonicalize(rer, c)` (§22.2.2.7.3†) for an expression with `i`:
/// [`simple_fold`] with `unicode` (`u` or `v`), else [`canonicalize_unit`].
#[must_use]
pub fn canonicalize(c: u32, unicode: bool) -> u32 {
    if unicode {
        simple_fold(c)
    } else {
        canonicalize_unit(c)
    }
}

/// Puts into `out` every `a` with `canonicalize(a, unicode) == cc`: the
/// characters CharacterSetMatcher (§22.2.2.7.1† step 3) and the
/// backreference matcher treat as equal to one another.
pub fn equivalents(cc: u32, unicode: bool, out: &mut Vec<u32>) {
    out.clear();
    if canonicalize(cc, unicode) == cc {
        out.push(cc);
    }
    let inverse = if unicode {
        tables::SIMPLE_FOLD_INVERSE
    } else {
        tables::UPPER_INVERSE
    };
    let mut i = lower_bound(inverse, cc);
    while let Some(&(k, v)) = inverse.get(i) {
        if k != cc {
            break;
        }
        out.push(v);
        i = i.saturating_add(1);
    }
}

/// The index into [`tables::CATEGORY_NAMES`] of the general category of `c`.
#[must_use]
pub fn general_category(c: u32) -> u8 {
    range_index(tables::GENERAL_CATEGORY, |r| r.0, c)
        .and_then(|i| tables::GENERAL_CATEGORY.get(i))
        .map_or(CN, |&(_, last, cat)| if c <= last { cat } else { CN })
}

/// The index of `Cn` in [`tables::CATEGORY_NAMES`].
const CN: u8 = 29;

/// The bit of a category for a mask of categories.
fn bit(abbr: &str) -> u32 {
    tables::CATEGORY_NAMES
        .iter()
        .position(|n| *n == abbr)
        .and_then(|i| u32::try_from(i).ok())
        .and_then(|i| 1u32.checked_shl(i))
        .unwrap_or(0)
}

fn mask(abbrs: &[&str]) -> u32 {
    abbrs.iter().fold(0, |m, a| m | bit(a))
}

/// A set of code points named by `\p{..}`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Prop {
    /// The code points whose general category is in the mask (a bit per index
    /// of [`tables::CATEGORY_NAMES`]).
    Category(u32),
    /// A binary property's ranges.
    Ranges(&'static [(u32, u32)]),
    /// `Any`.
    Any,
    /// `ASCII`.
    Ascii,
    /// `Assigned`: every category but `Cn`.
    Assigned,
}

impl Prop {
    /// Whether `c` has the property.
    #[must_use]
    pub fn contains(&self, c: u32) -> bool {
        match *self {
            Prop::Category(m) => 1u32
                .checked_shl(u32::from(general_category(c)))
                .is_some_and(|b| m & b != 0),
            Prop::Ranges(r) => in_ranges(r, c),
            Prop::Any => c <= 0x10FFFF,
            Prop::Ascii => c < 0x80,
            Prop::Assigned => general_category(c) != CN,
        }
    }
}

/// The mask of the general categories a `General_Category` value (a long name,
/// a short name or an alias, as in `PropertyValueAliases.txt`) stands for:
/// a group such as `L` is the union of its members.
#[must_use]
pub fn category_mask(value: &str) -> Option<u32> {
    Some(match value {
        "Lu" | "Uppercase_Letter" => mask(&["Lu"]),
        "Ll" | "Lowercase_Letter" => mask(&["Ll"]),
        "Lt" | "Titlecase_Letter" => mask(&["Lt"]),
        "LC" | "Cased_Letter" => mask(&["Lu", "Ll", "Lt"]),
        "Lm" | "Modifier_Letter" => mask(&["Lm"]),
        "Lo" | "Other_Letter" => mask(&["Lo"]),
        "L" | "Letter" => mask(&["Lu", "Ll", "Lt", "Lm", "Lo"]),
        "Mn" | "Nonspacing_Mark" => mask(&["Mn"]),
        "Mc" | "Spacing_Mark" => mask(&["Mc"]),
        "Me" | "Enclosing_Mark" => mask(&["Me"]),
        "M" | "Mark" | "Combining_Mark" => mask(&["Mn", "Mc", "Me"]),
        "Nd" | "Decimal_Number" | "digit" => mask(&["Nd"]),
        "Nl" | "Letter_Number" => mask(&["Nl"]),
        "No" | "Other_Number" => mask(&["No"]),
        "N" | "Number" => mask(&["Nd", "Nl", "No"]),
        "Pc" | "Connector_Punctuation" => mask(&["Pc"]),
        "Pd" | "Dash_Punctuation" => mask(&["Pd"]),
        "Ps" | "Open_Punctuation" => mask(&["Ps"]),
        "Pe" | "Close_Punctuation" => mask(&["Pe"]),
        "Pi" | "Initial_Punctuation" => mask(&["Pi"]),
        "Pf" | "Final_Punctuation" => mask(&["Pf"]),
        "Po" | "Other_Punctuation" => mask(&["Po"]),
        "P" | "Punctuation" | "punct" => mask(&["Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po"]),
        "Sm" | "Math_Symbol" => mask(&["Sm"]),
        "Sc" | "Currency_Symbol" => mask(&["Sc"]),
        "Sk" | "Modifier_Symbol" => mask(&["Sk"]),
        "So" | "Other_Symbol" => mask(&["So"]),
        "S" | "Symbol" => mask(&["Sm", "Sc", "Sk", "So"]),
        "Zs" | "Space_Separator" => mask(&["Zs"]),
        "Zl" | "Line_Separator" => mask(&["Zl"]),
        "Zp" | "Paragraph_Separator" => mask(&["Zp"]),
        "Z" | "Separator" => mask(&["Zs", "Zl", "Zp"]),
        "Cc" | "Control" | "cntrl" => mask(&["Cc"]),
        "Cf" | "Format" => mask(&["Cf"]),
        "Cs" | "Surrogate" => mask(&["Cs"]),
        "Co" | "Private_Use" => mask(&["Co"]),
        "Cn" | "Unassigned" => mask(&["Cn"]),
        "C" | "Other" => mask(&["Cc", "Cf", "Cs", "Co", "Cn"]),
        _ => return None,
    })
}

/// The set a binary property name (canonical or alias, exactly as written)
/// stands for: `Any`, `ASCII` and `Assigned` are the standard's; the others
/// come from [`tables::BINARY`].
#[must_use]
pub fn binary_property(name: &str) -> Option<Prop> {
    match name {
        "Any" => return Some(Prop::Any),
        "ASCII" => return Some(Prop::Ascii),
        "Assigned" => return Some(Prop::Assigned),
        _ => {}
    }
    let canonical = crate::props::BINARY_PROPERTIES
        .iter()
        .find(|(full, alias)| *full == name.as_bytes() || *alias == name.as_bytes())
        .map(|(full, _)| *full)?;
    tables::BINARY
        .iter()
        .find(|(n, _)| n.as_bytes() == canonical)
        .map(|&(_, r)| Prop::Ranges(r))
}

/// The set a `Script` (or, with `extensions`, `Script_Extensions`) value
/// stands for: a long name, a short name or another alias, exactly as in
/// `PropertyValueAliases.txt`, from [`tables::SCRIPTS`].
#[must_use]
pub fn script_property(value: &str, extensions: bool) -> Option<Prop> {
    tables::SCRIPTS
        .iter()
        .find(|s| s.names.contains(&value))
        .map(|s| Prop::Ranges(if extensions { s.scx } else { s.sc }))
}

/// A property of strings (`v`): its one-character members as a set, and its
/// strings of other lengths as code points.
#[derive(Debug, Clone)]
pub struct StringSet {
    /// The members of one code point.
    pub chars: Prop,
    /// The members of two or more, in the order of the Unicode files.
    pub strings: Vec<Vec<u32>>,
}

/// The property of strings named `name` (UTS #51; `RGI_Emoji` is the union of
/// the others), from [`tables::STRING_PROPERTIES`].
#[must_use]
pub fn string_property(name: &str) -> Option<StringSet> {
    let p = tables::STRING_PROPERTIES.iter().find(|p| p.name == name)?;
    Some(StringSet {
        chars: Prop::Ranges(p.chars),
        strings: p
            .strings
            .iter()
            .flat_map(|list| list.iter())
            .map(|s| s.chars().map(u32::from).collect())
            .collect(),
    })
}
