//! CSS Fonts 3 §5.2 "Matching font styles" and §5.4 "Character handling"
//! (<https://www.w3.org/TR/2018/REC-css-fonts-3-20180920/#font-style-matching>,
//! <https://www.w3.org/TR/2018/REC-css-fonts-3-20180920/#char-handling-issues>).
//!
//! Step numbers are §5.2's; its step 4 has four numbered sub-steps, cited
//! as 4.1 to 4.4. The modelling choices are listed in [`super`].

use super::generic::{Generic, Generics};
use super::table::{FaceId, FaceInfo, FontStyle, FontTable, STRETCH_NORMAL, same_family};

/// One entry of the computed `font-family` list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Family {
    /// A family name.
    Named(String),
    /// A generic family keyword.
    Generic(Generic),
}

/// The computed font properties matching reads (§5.2 step 1: "Using the
/// computed font property values for a given element").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FontQuery<'a> {
    /// `font-family`, in order.
    pub families: &'a [Family],
    /// `font-weight`, as a number (`normal` is 400, `bold` 700).
    pub weight: u16,
    /// `font-stretch`, 1 (`ultra-condensed`) to 9 (`ultra-expanded`).
    pub stretch: u8,
    /// `font-style`.
    pub style: FontStyle,
}

/// Whether a face maps a character: its `cmap` gives a glyph other than 0.
pub trait CharMap {
    /// Whether face `face` has a glyph for `c`.
    fn maps(&self, face: FaceId, c: char) -> bool;
}

/// Faces read with `clazel-font`, indexed like the [`FontTable`] built from
/// them.
impl CharMap for [clazel_font::Face<'_>] {
    fn maps(&self, face: FaceId, c: char) -> bool {
        self.get(face.0)
            .is_some_and(|f| matches!(f.glyph_index(c), Ok(Some(g)) if g != 0))
    }
}

/// What draws a character.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Choice {
    /// This face maps it.
    Face(FaceId),
    /// No face maps it: draw this face's glyph 0, `.notdef` (step 8).
    NotDef(FaceId),
    /// The font table has no face to draw even `.notdef` with.
    Nothing,
}

/// §5.2 step 4.1, `font-stretch`: "If the matching set contains faces with
/// width values matching the font-stretch value, faces with other width
/// values are removed from the matching set. If there is no face that
/// exactly matches the width value the nearest width is used instead. If the value
/// of font-stretch is normal or one of the condensed values, narrower width
/// values are checked first, then wider values. If the value of
/// font-stretch is one of the expanded values, wider values are checked
/// first, followed by narrower values."
fn nearest_stretch(desired: u8, widths: impl Iterator<Item = u8> + Clone) -> Option<u8> {
    let narrower = widths.clone().filter(|&w| w < desired).max();
    let wider = widths.clone().filter(|&w| w > desired).min();
    if widths.clone().any(|w| w == desired) {
        Some(desired)
    } else if desired <= STRETCH_NORMAL {
        narrower.or(wider)
    } else {
        wider.or(narrower)
    }
}

/// §5.2 step 4.2, `font-style`: "If the value of font-style is italic,
/// italic faces are checked first, then oblique, then normal faces. If the
/// value is oblique, oblique faces are checked first, then italic faces and
/// then normal faces. If the value is normal, normal faces are checked
/// first, then oblique faces, then italic faces."
fn style_order(desired: FontStyle) -> [FontStyle; 3] {
    use FontStyle::{Italic, Normal, Oblique};
    match desired {
        Italic => [Italic, Oblique, Normal],
        Oblique => [Oblique, Italic, Normal],
        Normal => [Normal, Oblique, Italic],
    }
}

/// §5.2 step 4.3, `font-weight`: "if the desired weight is available that
/// face matches. Otherwise, a weight is chosen using the rules below":
///
/// - "If the desired weight is less than 400, weights below the desired
///   weight are checked in descending order followed by weights above the
///   desired weight in ascending order until a match is found."
/// - "If the desired weight is greater than 500, weights above the desired
///   weight are checked in ascending order followed by weights below the
///   desired weight in descending order until a match is found."
/// - "If the desired weight is 400, 500 is checked first and then the rule
///   for desired weights less than 400 is used."
/// - "If the desired weight is 500, 400 is checked first and then the rule
///   for desired weights less than 400 is used."
fn nearest_weight(desired: u16, weights: impl Iterator<Item = u16> + Clone) -> Option<u16> {
    let has = |w: u16| weights.clone().any(|x| x == w);
    let below = weights.clone().filter(|&w| w < desired).max();
    let above = weights.clone().filter(|&w| w > desired).min();
    if has(desired) {
        Some(desired)
    } else if desired == 400 && has(500) {
        Some(500)
    } else if desired == 500 && has(400) {
        Some(400)
    } else if desired > 500 {
        above.or(below)
    } else {
        // Below 400, and 400 or 500 after their first check.
        below.or(above)
    }
}

/// §5.2 step 4: narrow one family's faces to one. Sub-steps 4.1 to 4.3 in
/// order, each keeping only the faces with the value it chose; 4.4
/// (`font-size`) keeps every face, since all are scalable. A tie left
/// after them goes to the first face in table order.
pub fn select_face(faces: &[(FaceId, &FaceInfo)], query: &FontQuery<'_>) -> Option<FaceId> {
    // 4.1. font-stretch.
    let width = nearest_stretch(query.stretch, faces.iter().map(|(_, f)| f.stretch))?;
    let set: Vec<&(FaceId, &FaceInfo)> = faces.iter().filter(|(_, f)| f.stretch == width).collect();
    // 4.2. font-style.
    let style = style_order(query.style)
        .into_iter()
        .find(|s| set.iter().any(|(_, f)| f.style == *s))?;
    let set: Vec<&(FaceId, &FaceInfo)> =
        set.into_iter().filter(|(_, f)| f.style == style).collect();
    // 4.3. font-weight.
    let weight = nearest_weight(query.weight, set.iter().map(|(_, f)| f.weight))?;
    // 4.4. font-size: every face is scalable; nothing is removed.
    set.into_iter()
        .find(|(_, f)| f.weight == weight)
        .map(|(id, _)| *id)
}

/// Steps 2 to 4 for one `font-family` entry: the family it names (step 2
/// for a generic, step 3 for a name), then the face step 4 selects.
fn family_face(
    table: &FontTable,
    generics: &Generics,
    family: &Family,
    query: &FontQuery<'_>,
) -> Option<FaceId> {
    let name = match family {
        // 2. "If the family name is a generic family keyword, the user agent
        //    looks up the appropriate font family name to be used."
        Family::Generic(g) => generics.resolve(*g, table)?,
        // 3. "For other family names, the user agent attempts to find the
        //    family name among … available system fonts, matching names with
        //    a case-insensitive comparison" (§5.1).
        // 4. "If a font family match occurs, the user agent assembles the
        //    set of font faces in that family and then narrows the set to a
        //    single face".
        Family::Named(n) => n.as_str(),
    };
    select_face(&table.family(name), query)
}

/// The families step 7 tries, in order: the OS's fallback list, then every
/// other family of the table (a modelling choice in [`super`]).
fn fallback_families<'a>(table: &'a FontTable, generics: &'a Generics) -> Vec<&'a str> {
    let mut out: Vec<&str> = Vec::new();
    let listed = generics.fallback.iter().map(String::as_str);
    for name in listed.chain(table.families()) {
        if table.has_family(name) && !out.iter().any(|o| same_family(o, name)) {
            out.push(name);
        }
    }
    out
}

/// §5.4: "Private-Use Area code points"; U+E000 to U+F8FF and the
/// supplementary Private Use Areas A (plane 15) and B (plane 16).
fn is_private_use(c: char) -> bool {
    matches!(
        u32::from(c),
        0xE000..=0xF8FF | 0xF_0000..=0xF_FFFD | 0x10_0000..=0x10_FFFD
    )
}

/// Steps 1 to 7 for `c`: the face that draws it, if any face does.
fn search(
    table: &FontTable,
    generics: &Generics,
    query: &FontQuery<'_>,
    c: char,
    cmap: &(impl CharMap + ?Sized),
) -> Option<FaceId> {
    // §5.4: for a private-use code point, "user agents must only match font
    // families named in the 'font-family' list that are not generic
    // families", and display a missing glyph "rather than attempting system
    // font fallback".
    let private = is_private_use(c);
    // 1. "the user agent starts with the first family name specified by
    //    the 'font-family' property."
    // 6. "If no matching face exists or the matched face does not contain a
    //    glyph for the character to be rendered, the next family name is
    //    selected and the previous three steps repeated. Glyphs from other
    //    faces in the family are not considered."
    for family in query.families {
        if private && matches!(family, Family::Generic(_)) {
            continue;
        }
        // 2. to 4.; 5. applies only to @font-face faces, which there are not.
        if let Some(id) = family_face(table, generics, family, query)
            && cmap.maps(id, c)
        {
            return Some(id);
        }
    }
    if private {
        return None;
    }
    // 7. "If there are no more font families to be evaluated and no matching
    //    face has been found, then the user agent performs a system font
    //    fallback procedure to find the best match for the character to be
    //    rendered."
    fallback_families(table, generics)
        .into_iter()
        .filter_map(|name| select_face(&table.family(name), query))
        .find(|&id| cmap.maps(id, c))
}

/// §5.2's *first available font*: "the first available font that would
/// match the U+0020 (space) character given font families in the
/// font-family list (or a user agent's default font if none are
/// available)". If no face maps U+0020, the face step 4 selects in the first
/// family of the list present in the table, else in the first fallback
/// family (a modelling choice in [`super`]).
pub fn first_available_font(
    table: &FontTable,
    generics: &Generics,
    query: &FontQuery<'_>,
    cmap: &(impl CharMap + ?Sized),
) -> Option<FaceId> {
    search(table, generics, query, ' ', cmap)
        .or_else(|| {
            query
                .families
                .iter()
                .find_map(|f| family_face(table, generics, f, query))
        })
        .or_else(|| {
            fallback_families(table, generics)
                .into_iter()
                .find_map(|name| select_face(&table.family(name), query))
        })
}

/// The face that draws `c`: §5.2 steps 1 to 7 with §5.4's private-use rule,
/// then step 8: "If a particular character cannot be displayed using any
/// font, the user agent should indicate by some means that a character is
/// not being displayed", here by `.notdef` of the first available font.
pub fn face_for_char(
    table: &FontTable,
    generics: &Generics,
    query: &FontQuery<'_>,
    c: char,
    cmap: &(impl CharMap + ?Sized),
) -> Choice {
    match search(table, generics, query, c, cmap) {
        Some(id) => Choice::Face(id),
        // 8.
        None => match first_available_font(table, generics, query, cmap) {
            Some(id) => Choice::NotDef(id),
            None => Choice::Nothing,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fonts::generic::Os;

    /// A face with the given description.
    fn face(family: &str, weight: u16, stretch: u8, style: FontStyle) -> FaceInfo {
        FaceInfo {
            family: family.to_owned(),
            weight,
            stretch,
            style,
        }
    }

    fn query(families: &[Family]) -> FontQuery<'_> {
        FontQuery {
            families,
            weight: 400,
            stretch: STRETCH_NORMAL,
            style: FontStyle::Normal,
        }
    }

    /// Faces' character maps for tests: face i maps the characters of
    /// string i.
    struct Maps(Vec<&'static str>);

    impl CharMap for Maps {
        fn maps(&self, face: FaceId, c: char) -> bool {
            self.0.get(face.0).is_some_and(|s| s.contains(c))
        }
    }

    fn named(n: &str) -> Family {
        Family::Named(n.to_owned())
    }

    /// Step 4.3 on a family with the given weights: the weight chosen.
    fn weight_of(weights: &[u16], desired: u16) -> Option<u16> {
        let mut t = FontTable::new();
        for &w in weights {
            t.push(face("F", w, STRETCH_NORMAL, FontStyle::Normal));
        }
        let families = [named("F")];
        let q = FontQuery {
            weight: desired,
            ..query(&families)
        };
        let id = select_face(&t.family("F"), &q)?;
        t.get(id).map(|f| f.weight)
    }

    #[test]
    fn step_4_3_weight() {
        let w = [100, 300, 500, 700, 900];
        // Exact.
        assert_eq!(weight_of(&w, 700), Some(700));
        // Below 400: lighter descending, then heavier ascending.
        assert_eq!(weight_of(&w, 200), Some(100));
        assert_eq!(weight_of(&[300, 500], 200), Some(300));
        // Above 500: heavier ascending, then lighter descending.
        assert_eq!(weight_of(&w, 600), Some(700));
        assert_eq!(weight_of(&[100, 300], 800), Some(300));
        // 400: 500 first, then the below-400 rule.
        assert_eq!(weight_of(&w, 400), Some(500));
        assert_eq!(weight_of(&[300, 600], 400), Some(300));
        assert_eq!(weight_of(&[600, 700], 400), Some(600));
        // 500: 400 first, then the below-400 rule.
        assert_eq!(weight_of(&[400, 600], 500), Some(400));
        assert_eq!(weight_of(&[300, 600], 500), Some(300));
        assert_eq!(weight_of(&[600, 700], 500), Some(600));
        assert_eq!(weight_of(&[], 400), None);
    }

    #[test]
    fn step_4_1_stretch() {
        assert_eq!(nearest_stretch(5, [3, 5, 7].into_iter()), Some(5));
        // Normal and condensed: narrower first.
        assert_eq!(nearest_stretch(5, [3, 7].into_iter()), Some(3));
        assert_eq!(nearest_stretch(2, [1, 4].into_iter()), Some(1));
        assert_eq!(nearest_stretch(2, [4, 6].into_iter()), Some(4));
        // Expanded: wider first.
        assert_eq!(nearest_stretch(6, [4, 8].into_iter()), Some(8));
        assert_eq!(nearest_stretch(8, [4, 7].into_iter()), Some(7));
        assert_eq!(nearest_stretch(5, core::iter::empty()), None);
    }

    #[test]
    fn step_4_2_style() {
        use FontStyle::{Italic, Normal, Oblique};
        let pick = |styles: &[FontStyle], desired| {
            let mut t = FontTable::new();
            for &s in styles {
                t.push(face("F", 400, STRETCH_NORMAL, s));
            }
            let families = [named("F")];
            let q = FontQuery {
                style: desired,
                ..query(&families)
            };
            select_face(&t.family("F"), &q).and_then(|id| t.get(id).map(|f| f.style))
        };
        assert_eq!(pick(&[Normal, Oblique, Italic], Italic), Some(Italic));
        assert_eq!(pick(&[Normal, Oblique], Italic), Some(Oblique));
        assert_eq!(pick(&[Normal], Italic), Some(Normal));
        assert_eq!(pick(&[Normal, Italic], Oblique), Some(Italic));
        assert_eq!(pick(&[Normal, Oblique, Italic], Oblique), Some(Oblique));
        assert_eq!(pick(&[Italic, Oblique], Normal), Some(Oblique));
        assert_eq!(pick(&[Italic], Normal), Some(Italic));
    }

    #[test]
    fn step_4_narrows_in_order_stretch_style_weight() {
        let mut t = FontTable::new();
        // A bold normal-width italic, and a condensed regular upright: for
        // a normal-width, normal-style, 400 query, width is decided first,
        // so the italic wins although its style and weight are worse.
        let bold_italic = t.push(face("F", 700, 5, FontStyle::Italic));
        t.push(face("F", 400, 3, FontStyle::Normal));
        let families = [named("F")];
        assert_eq!(
            select_face(&t.family("F"), &query(&families)),
            Some(bold_italic)
        );
        // Then style before weight.
        let mut t = FontTable::new();
        t.push(face("F", 400, 5, FontStyle::Italic));
        let upright_bold = t.push(face("F", 900, 5, FontStyle::Normal));
        assert_eq!(
            select_face(&t.family("F"), &query(&families)),
            Some(upright_bold)
        );
        // A tie goes to the first face added.
        let mut t = FontTable::new();
        let first = t.push(face("F", 400, 5, FontStyle::Normal));
        t.push(face("F", 400, 5, FontStyle::Normal));
        assert_eq!(select_face(&t.family("F"), &query(&families)), Some(first));
    }

    #[test]
    fn steps_2_3_6_first_family_that_maps_the_character() {
        let mut t = FontTable::new();
        let a = t.push(face("A", 400, 5, FontStyle::Normal));
        let a_bold = t.push(face("A", 700, 5, FontStyle::Normal));
        let b = t.push(face("B", 400, 5, FontStyle::Normal));
        let dejavu = t.push(face("DejaVu Serif", 400, 5, FontStyle::Normal));
        let maps = Maps(vec!["x ", "xy", "xyz", "xyzw"]);
        let g = Generics::for_os(Os::Linux);
        let families = [
            named("missing"),
            named("a"),
            named("B"),
            Family::Generic(Generic::Serif),
        ];
        let q = query(&families);
        // Step 3: an absent family is skipped; names are caseless.
        assert_eq!(face_for_char(&t, &g, &q, 'x', &maps), Choice::Face(a));
        // Step 6: A's matched face (the 400) lacks 'y'; A's bold has it but
        // "glyphs from other faces in the family are not considered".
        assert_eq!(face_for_char(&t, &g, &q, 'y', &maps), Choice::Face(b));
        assert_ne!(face_for_char(&t, &g, &q, 'y', &maps), Choice::Face(a_bold));
        // Step 2: serif is DejaVu Serif on Linux.
        assert_eq!(face_for_char(&t, &g, &q, 'w', &maps), Choice::Face(dejavu));
    }

    #[test]
    fn step_7_fallback_then_step_8_notdef() {
        let mut t = FontTable::new();
        let a = t.push(face("A", 400, 5, FontStyle::Normal));
        let other = t.push(face("Other", 400, 5, FontStyle::Normal));
        let sans = t.push(face("DejaVu Sans", 400, 5, FontStyle::Normal));
        let maps = Maps(vec!["a ", "ko", "kq"]);
        let g = Generics::for_os(Os::Linux);
        let families = [named("A")];
        let q = query(&families);
        // 7: the OS's fallback list (DejaVu Sans) before the rest of the
        // table (Other), whatever the table's order.
        assert_eq!(face_for_char(&t, &g, &q, 'k', &maps), Choice::Face(sans));
        // 7: then any other family.
        assert_eq!(face_for_char(&t, &g, &q, 'o', &maps), Choice::Face(other));
        // 8: nobody maps it: .notdef of the first available font, the face
        // that matches U+0020.
        assert_eq!(face_for_char(&t, &g, &q, '¤', &maps), Choice::NotDef(a));
        assert_eq!(first_available_font(&t, &g, &q, &maps), Some(a));
        // An empty table has nothing to draw with.
        assert_eq!(
            face_for_char(&FontTable::new(), &g, &q, 'k', &maps),
            Choice::Nothing
        );
    }

    #[test]
    fn first_available_font_without_a_space() {
        let mut t = FontTable::new();
        t.push(face("Z", 400, 5, FontStyle::Normal));
        let b = t.push(face("B", 400, 5, FontStyle::Normal));
        let maps = Maps(vec!["", ""]);
        let g = Generics::for_os(Os::MacOs);
        // Nobody maps U+0020: the first family of the list present.
        let families = [named("nope"), named("B")];
        assert_eq!(
            first_available_font(&t, &g, &query(&families), &maps),
            Some(b)
        );
        // No family of the list is present: the first fallback family,
        // here the table's first since no OS family is installed.
        let families = [named("nope")];
        assert_eq!(
            first_available_font(&t, &g, &query(&families), &maps),
            Some(FaceId(0))
        );
    }

    #[test]
    fn section_5_4_private_use_only_in_named_families() {
        let mut t = FontTable::new();
        let a = t.push(face("A", 400, 5, FontStyle::Normal));
        t.push(face("DejaVu Sans", 400, 5, FontStyle::Normal));
        let icons = t.push(face("Icons", 400, 5, FontStyle::Normal));
        let pua = '\u{E000}';
        let maps = Maps(vec![" ", "\u{E000}", "\u{E000}"]);
        let g = Generics::for_os(Os::Linux);
        // A generic family (sans-serif is DejaVu Sans) and the fallback are
        // not searched for a private-use code point.
        let families = [named("A"), Family::Generic(Generic::SansSerif)];
        assert_eq!(
            face_for_char(&t, &g, &query(&families), pua, &maps),
            Choice::NotDef(a)
        );
        // A named family is.
        let families = [named("A"), named("Icons")];
        assert_eq!(
            face_for_char(&t, &g, &query(&families), pua, &maps),
            Choice::Face(icons)
        );
        assert!(is_private_use('\u{F8FF}') && is_private_use('\u{10FFFD}'));
        assert!(!is_private_use('\u{F900}') && !is_private_use('\u{FFFD}'));
    }
}
