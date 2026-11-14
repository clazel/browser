//! HTML §15's presentational hints that its prose gives (the ones written as CSS blocks
//! are `data/hints.css`, read as a style sheet): each attribute mapping, for one element,
//! as the longhands it sets. HTML at commit 4c54fae1 (`data/html-4c54fae1/`).
//!
//! §15.2's definitions, which the mappings use:
//!
//! - "maps to the pixel length property": "if element has an attribute attribute set, and
//!   parsing that attribute's value using the rules for parsing non-negative integers
//!   doesn't generate an error, then the user agent is expected to use the parsed value as
//!   a pixel length for a presentational hint for properties" ([`pixel_length`]);
//! - "maps to the dimension property": likewise with "the rules for parsing dimension
//!   values", "with the value given as a pixel length if the dimension was a length, and
//!   with the value given as a percentage if the dimension was a percentage"
//!   ([`dimension`]); "(ignoring zero)": with "the rules for parsing nonzero dimension
//!   values".
//!
//! Not mapped, and listed in the README: `background` attributes (`background-image` is
//! "parsed, no effect"); `body`'s `vlink` and `alink` (`:visited` and `:active` never
//! match); the container frame's `marginheight` and `marginwidth` (no nested browsing
//! contexts, 5.0(i)); `li`'s `value` and `ol`'s `start` and `reversed` (counters are not in
//! the subset); the `align` values `center` and `middle` on replaced elements, which "no CSS
//! value" gives; and the `aspect-ratio` mappings (not in the subset).

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_selectors::exec_element::hyperlink;

use super::computed::{AlignDescendants, Rgba};
use super::legacy::{
    self, Dimension, legacy_color, legacy_font_size, non_negative_integer, nonzero_dimension,
};
use crate::values::color::Color;
use crate::values::component::Component;
use crate::values::items::Values;
use crate::values::items::eq_ignore_case;
use crate::values::longhand::Longhand;
use crate::values::number::{Length, LengthUnit, Num, SCALE};
use crate::values::{Declared, Property, Specified};

/// What one element's presentational hints set.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Hints {
    /// The longhands, in the order the mappings are applied.
    pub set: Vec<Declared>,
    /// HTML's "align descendants", if the element does.
    pub align: Option<AlignDescendants>,
}

/// What the hints of one element read from the rest of the document.
#[derive(Debug, Clone, Copy, Default)]
pub struct Context {
    /// The document is in quirks mode.
    pub quirks: bool,
    /// The colour of the `body` element's `link` attribute, if it parses.
    pub link_color: Option<Rgba>,
}

fn is(s: &[u32], target: &str) -> bool {
    s.iter().copied().eq(target.chars().map(u32::from))
}

/// The value of the attribute `name` (no namespace), the first if repeated.
pub fn attribute<'a>(attributes: &'a [ExecAttr], name: &str) -> Option<&'a [u32]> {
    attributes
        .iter()
        .find(|a| a.namespace.is_none() && is(&a.local_name, name))
        .map(|a| a.value.as_slice())
}

/// The local name and attributes of `x` if it is an HTML element.
pub fn html_element(arena: &Arena, x: usize) -> Option<(&[u32], &[ExecAttr])> {
    if x >= arena.len() {
        return None;
    }
    match arena.kind(x) {
        ExecKind::Element {
            namespace: Some(Namespace::Html),
            local_name,
            attributes,
            ..
        } => Some((local_name.as_slice(), attributes.as_slice())),
        _ => None,
    }
}

/// True if `x` is the HTML element named `name`.
pub fn is_html(arena: &Arena, x: usize, name: &str) -> bool {
    html_element(arena, x).is_some_and(|(n, _)| is(n, name))
}

fn set(out: &mut Vec<Declared>, property: Longhand, value: Component) {
    out.push(Declared {
        property,
        value: Specified::Value(vec![value]),
    });
}

fn px(n: Num) -> Component {
    Component::Length(Length {
        value: n,
        unit: LengthUnit::Px,
    })
}

fn color(c: Rgba) -> Component {
    Component::Color(Color::Rgba(c))
}

/// "Maps to the pixel length property": the attribute's value as a pixel length, if it is a
/// non-negative integer.
fn pixel_length(attributes: &[ExecAttr], name: &str) -> Option<Component> {
    let v = non_negative_integer(attribute(attributes, name)?)?;
    Some(px(Num::from_int(v)))
}

/// "Maps to the dimension property" (or, with `nonzero`, "(ignoring zero)").
fn dimension(attributes: &[ExecAttr], name: &str, nonzero: bool) -> Option<Component> {
    let v = attribute(attributes, name)?;
    let d = if nonzero {
        nonzero_dimension(v)?
    } else {
        legacy::dimension(v)?
    };
    Some(match d {
        Dimension::Length(n) => px(n),
        Dimension::Percentage(n) => Component::Percentage(n),
    })
}

fn sides(out: &mut Vec<Declared>, longhands: [Longhand; 4], value: &Component) {
    for l in longhands {
        set(out, l, value.clone());
    }
}

const BORDER_WIDTHS: [Longhand; 4] = [
    Longhand::BorderTopWidth,
    Longhand::BorderRightWidth,
    Longhand::BorderBottomWidth,
    Longhand::BorderLeftWidth,
];
const BORDER_STYLES: [Longhand; 4] = [
    Longhand::BorderTopStyle,
    Longhand::BorderRightStyle,
    Longhand::BorderBottomStyle,
    Longhand::BorderLeftStyle,
];
const BORDER_COLORS: [Longhand; 4] = [
    Longhand::BorderTopColor,
    Longhand::BorderRightColor,
    Longhand::BorderBottomColor,
    Longhand::BorderLeftColor,
];
const PADDINGS: [Longhand; 4] = [
    Longhand::PaddingTop,
    Longhand::PaddingRight,
    Longhand::PaddingBottom,
    Longhand::PaddingLeft,
];

/// The attribute `name` parsed as a legacy colour, as a hint for `property`.
fn legacy_color_hint(out: &mut Vec<Declared>, attributes: &[ExecAttr], name: &str, l: Longhand) {
    if let Some(c) = attribute(attributes, name).and_then(legacy_color) {
        set(out, l, color(c));
    }
}

/// An `align` attribute's text alignment and alignment of descendants, for §15.3.3's `div`
/// and §15.3.8's table parts: "center" or "middle", "left", "right" and "justify" (which
/// aligns descendants to the left).
fn align(attributes: &[ExecAttr]) -> Option<(&'static str, AlignDescendants)> {
    let v = attribute(attributes, "align")?;
    if eq_ignore_case(v, "center") || eq_ignore_case(v, "middle") {
        Some(("center", AlignDescendants::Center))
    } else if eq_ignore_case(v, "left") {
        Some(("left", AlignDescendants::Left))
    } else if eq_ignore_case(v, "right") {
        Some(("right", AlignDescendants::Right))
    } else if eq_ignore_case(v, "justify") {
        Some(("justify", AlignDescendants::Left))
    } else {
        None
    }
}

/// The `table` a `td` or `th` belongs to in HTML's table model ("the table corresponding to
/// the table element" of §15.3.8's `cellpadding`): its parent `tr`'s parent if that is a
/// `table`, or the parent of that if it is a `thead`, `tbody` or `tfoot` (HTML §4.9.1's
/// "forming a table"† reads rows from exactly those).
pub fn table_of_cell(arena: &Arena, cell: usize) -> Option<usize> {
    let tr = arena.parent(cell).filter(|&p| is_html(arena, p, "tr"))?;
    let up = arena.parent(tr)?;
    if is_html(arena, up, "table") {
        return Some(up);
    }
    let group = ["thead", "tbody", "tfoot"]
        .iter()
        .any(|g| is_html(arena, up, g));
    let table = arena.parent(up).filter(|_| group)?;
    is_html(arena, table, "table").then_some(table)
}

/// The presentational hints of element `x` of `arena`.
pub fn hints(arena: &Arena, x: usize, cx: Context) -> Hints {
    let mut h = Hints::default();
    let Some((name, attributes)) = html_element(arena, x) else {
        return h;
    };
    let out = &mut h.set;
    let n = |s: &str| is(name, s);
    // §15.3.2: `body`'s margins, colours.
    if n("body") {
        // "the first attribute that exists maps to the pixel length property on the body
        // element. If none of the attributes for a property are found, or if the value of
        // the attribute that was found cannot be parsed successfully, then a default value
        // of 8px is expected to be used" (the default is the user agent's, `ua.rs`).
        for (names, longhands) in [
            (
                ["marginheight", "topmargin"],
                [Longhand::MarginTop, Longhand::MarginBottom],
            ),
            (
                ["marginwidth", "leftmargin"],
                [Longhand::MarginLeft, Longhand::MarginRight],
            ),
        ] {
            let found = names.iter().find(|a| attribute(attributes, a).is_some());
            if let Some(v) = found.and_then(|a| pixel_length(attributes, a)) {
                for l in longhands {
                    set(out, l, v.clone());
                }
            }
        }
        legacy_color_hint(out, attributes, "bgcolor", Longhand::BackgroundColor);
        legacy_color_hint(out, attributes, "text", Longhand::Color);
    }
    // §15.3.2: "the 'color' property of any element in the Document matching the :link
    // pseudo-class" (`:visited` never matches, so `:link` is every hyperlink).
    if let Some(c) = cx.link_color
        && hyperlink(arena, x)
    {
        set(out, Longhand::Color, color(c));
    }
    // §15.3.3: `center`, and `div` with `align`: "as if they had their 'text-align' property
    // set to ... in a presentational hint, and to align descendants".
    if n("center") {
        set(out, Longhand::TextAlign, Component::Keyword("center"));
        h.align = Some(AlignDescendants::Center);
    }
    if n("div")
        && let Some((k, a)) = align(attributes)
    {
        set(out, Longhand::TextAlign, Component::Keyword(k));
        h.align = Some(a);
    }
    // §15.3.4: `font`.
    if n("font") {
        legacy_color_hint(out, attributes, "color", Longhand::Color);
        // "treat the attribute as a presentational hint setting the element's 'font-family'
        // property to the attribute's value" (if it is a valid value of it).
        if let Some(face) = attribute(attributes, "face")
            && let Some(ds) = Values::parse(face).and_then(|v| {
                crate::values::parse_items(Property::Longhand(Longhand::FontFamily), v.src(), false)
            })
        {
            out.extend(
                ds.into_iter()
                    .filter(|d| !matches!(d.value, Specified::Wide(_))),
            );
        }
        if let Some(k) = attribute(attributes, "size").and_then(legacy_font_size) {
            set(out, Longhand::FontSize, Component::Keyword(k));
        }
    }
    // §15.3.8: tables.
    if n("table") {
        if let Some(v) = pixel_length(attributes, "cellspacing") {
            set(out, Longhand::BorderSpacing, v);
        }
        if let Some(v) = dimension(attributes, "height", false) {
            set(out, Longhand::Height, v);
        }
        if let Some(v) = dimension(attributes, "width", true) {
            set(out, Longhand::Width, v);
        }
        legacy_color_hint(out, attributes, "bgcolor", Longhand::BackgroundColor);
        if let Some(c) = attribute(attributes, "bordercolor").and_then(legacy_color) {
            sides(out, BORDER_COLORS, &color(c));
        }
        // "The table element's border attribute maps to the pixel length properties
        // 'border-top-width', ... If the attribute is present but parsing the attribute's
        // value using the rules for parsing non-negative integers generates an error, a
        // default value of 1px is expected to be used for that property instead."
        if attribute(attributes, "border").is_some() {
            let v = pixel_length(attributes, "border").unwrap_or(px(Num::from_int(1)));
            sides(out, BORDER_WIDTHS, &v);
        }
    }
    if n("col")
        && let Some(v) = dimension(attributes, "width", false)
    {
        set(out, Longhand::Width, v);
    }
    let group = n("thead") || n("tbody") || n("tfoot");
    let cell = n("td") || n("th");
    if (group || n("tr"))
        && let Some(v) = dimension(attributes, "height", false)
    {
        set(out, Longhand::Height, v);
    }
    if cell {
        if let Some(v) = dimension(attributes, "height", true) {
            set(out, Longhand::Height, v);
        }
        if let Some(v) = dimension(attributes, "width", true) {
            set(out, Longhand::Width, v);
        }
        // `cellpadding` "maps to the pixel length properties 'padding-top', ... of any td
        // and th elements that have corresponding cells in the table corresponding to the
        // table element."
        if let Some(v) = table_of_cell(arena, x)
            .and_then(|t| html_element(arena, t))
            .and_then(|(_, a)| pixel_length(a, "cellpadding"))
        {
            sides(out, PADDINGS, &v);
        }
        // "In quirks mode, a td element or a th element that has a nowrap attribute but also
        // has a width attribute whose value, when parsed using the rules for parsing nonzero
        // dimension values, is found to be a length ... is expected to have a presentational
        // hint setting the element's 'white-space' property to 'normal', overriding the rule
        // in the CSS block above that sets it to 'nowrap'." (Hints from prose follow the
        // hints from the CSS blocks, at the same specificity, so this one wins.)
        if cx.quirks
            && attribute(attributes, "nowrap").is_some()
            && matches!(
                attribute(attributes, "width").and_then(nonzero_dimension),
                Some(Dimension::Length(_))
            )
        {
            set(out, Longhand::WhiteSpace, Component::Keyword("normal"));
        }
    }
    if group || n("tr") || cell {
        legacy_color_hint(out, attributes, "bgcolor", Longhand::BackgroundColor);
        if let Some((k, a)) = align(attributes) {
            set(out, Longhand::TextAlign, Component::Keyword(k));
            h.align = Some(a);
        }
    }
    // §15.3.11: `hr`.
    if n("hr") {
        let shaded =
            attribute(attributes, "color").is_none() && attribute(attributes, "noshade").is_none();
        if let Some(size) = attribute(attributes, "size").and_then(non_negative_integer) {
            if !shaded {
                // "the parsed value divided by two as a pixel length".
                let half = Num {
                    millionths: size.saturating_mul(SCALE).checked_div(2).unwrap_or(0),
                    is_integer: false,
                };
                sides(out, BORDER_WIDTHS, &px(half));
            } else if size == 1 {
                set(out, Longhand::BorderBottomWidth, px(Num::ZERO));
            } else if size > 1 {
                set(
                    out,
                    Longhand::Height,
                    px(Num::from_int(size.saturating_sub(2))),
                );
            }
        }
        if let Some(v) = dimension(attributes, "width", false) {
            set(out, Longhand::Width, v);
        }
        legacy_color_hint(out, attributes, "color", Longhand::Color);
    }
    // §15.4.3: embedded content and images.
    let image_input =
        n("input") && attribute(attributes, "type").is_some_and(|t| eq_ignore_case(t, "image"));
    let image_like = n("img") || image_input;
    if image_like || n("embed") || n("object") {
        if let Some(v) = dimension(attributes, "hspace", false) {
            set(out, Longhand::MarginLeft, v.clone());
            set(out, Longhand::MarginRight, v);
        }
        if let Some(v) = dimension(attributes, "vspace", false) {
            set(out, Longhand::MarginTop, v.clone());
            set(out, Longhand::MarginBottom, v);
        }
    }
    // "When an iframe element has a frameborder attribute whose value, when parsed using the
    // rules for parsing integers, is zero or an error".
    if n("iframe")
        && let Some(v) = attribute(attributes, "frameborder")
        && legacy::integer(v).is_none_or(|i| i == 0)
    {
        sides(out, BORDER_WIDTHS, &px(Num::ZERO));
    }
    if (image_like || n("object"))
        && let Some(b) = attribute(attributes, "border").and_then(non_negative_integer)
        && b > 0
    {
        sides(out, BORDER_WIDTHS, &px(Num::from_int(b)));
        sides(out, BORDER_STYLES, &Component::Keyword("solid"));
    }
    if image_like || n("embed") || n("iframe") || n("object") || n("video") {
        if let Some(v) = dimension(attributes, "width", false) {
            set(out, Longhand::Width, v);
        }
        if let Some(v) = dimension(attributes, "height", false) {
            set(out, Longhand::Height, v);
        }
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::values::component::to_string;

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn element(arena: &mut Arena, parent: usize, name: &str, attrs: &[(&str, &str)]) -> usize {
        let id = arena
            .create(ExecKind::Element {
                namespace: Some(Namespace::Html),
                prefix: None,
                local_name: u(name),
                attributes: attrs
                    .iter()
                    .map(|(k, v)| ExecAttr {
                        namespace: None,
                        prefix: None,
                        local_name: u(k),
                        value: u(v),
                    })
                    .collect(),
                template_contents: None,
                form_owner: None,
            })
            .unwrap_or(0);
        arena.append(parent, id);
        id
    }

    fn show(h: &Hints) -> Vec<String> {
        h.set
            .iter()
            .map(|d| match &d.value {
                Specified::Value(v) => format!("{}: {}", d.property.name(), to_string(v)),
                Specified::Wide(w) => format!("{}: {}", d.property.name(), w.name()),
            })
            .collect()
    }

    #[test]
    fn hacker_news_attributes() {
        let mut a = Arena::new(u("about:blank"));
        let html = element(&mut a, 0, "html", &[]);
        let table = element(
            &mut a,
            html,
            "table",
            &[
                ("id", "hnmain"),
                ("border", "0"),
                ("cellpadding", "0"),
                ("cellspacing", "0"),
                ("width", "85%"),
                ("bgcolor", "#f6f6ef"),
            ],
        );
        let tbody = element(&mut a, table, "tbody", &[]);
        let tr = element(&mut a, tbody, "tr", &[]);
        let td = element(&mut a, tr, "td", &[("valign", "top"), ("align", "right")]);
        let img = element(
            &mut a,
            td,
            "img",
            &[("src", "s.gif"), ("height", "1"), ("width", "40")],
        );
        let font = element(&mut a, td, "font", &[("size", "1"), ("color", "#828282")]);
        let cx = Context::default();
        assert_eq!(
            show(&hints(&a, table, cx)),
            vec![
                "border-spacing: 0px",
                "width: 85%",
                "background-color: rgb(246, 246, 239)",
                "border-top-width: 0px",
                "border-right-width: 0px",
                "border-bottom-width: 0px",
                "border-left-width: 0px",
            ]
        );
        let h = hints(&a, td, cx);
        assert_eq!(
            show(&h),
            vec![
                "padding-top: 0px",
                "padding-right: 0px",
                "padding-bottom: 0px",
                "padding-left: 0px",
                "text-align: right",
            ]
        );
        assert_eq!(h.align, Some(AlignDescendants::Right));
        assert_eq!(
            show(&hints(&a, img, cx)),
            vec!["width: 40px", "height: 1px"]
        );
        assert_eq!(
            show(&hints(&a, font, cx)),
            vec!["color: rgb(130, 130, 130)", "font-size: x-small"]
        );
    }

    #[test]
    fn hr_center_body_and_quirks() {
        let mut a = Arena::new(u("about:blank"));
        let html = element(&mut a, 0, "html", &[]);
        let body = element(
            &mut a,
            html,
            "body",
            &[("topmargin", "x"), ("marginwidth", "4")],
        );
        let hr = element(&mut a, body, "hr", &[("size", "5"), ("noshade", "")]);
        let hr2 = element(&mut a, body, "hr", &[("size", "1")]);
        let center = element(&mut a, body, "center", &[]);
        let link = element(&mut a, body, "a", &[("href", "x")]);
        let table = element(&mut a, body, "table", &[("border", "")]);
        let tr = element(&mut a, table, "tr", &[]);
        let td = element(&mut a, tr, "td", &[("nowrap", ""), ("width", "50")]);
        let cx = Context {
            quirks: true,
            link_color: Some([1, 2, 3, 255]),
        };
        assert_eq!(
            show(&hints(&a, body, cx)),
            vec!["margin-left: 4px", "margin-right: 4px"]
        );
        assert_eq!(
            show(&hints(&a, hr, cx)).first().map(String::as_str),
            Some("border-top-width: 2.5px")
        );
        assert_eq!(show(&hints(&a, hr2, cx)), vec!["border-bottom-width: 0px"]);
        let c = hints(&a, center, cx);
        assert_eq!(show(&c), vec!["text-align: center"]);
        assert_eq!(c.align, Some(AlignDescendants::Center));
        assert_eq!(show(&hints(&a, link, cx)), vec!["color: rgb(1, 2, 3)"]);
        assert_eq!(show(&hints(&a, table, cx)).len(), 4);
        assert_eq!(
            show(&hints(&a, td, cx)),
            vec!["width: 50px", "white-space: normal"]
        );
        let no_quirks = Context::default();
        assert_eq!(show(&hints(&a, td, no_quirks)), vec!["width: 50px"]);
    }
}
