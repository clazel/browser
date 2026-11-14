//! Matching through the parser: `parse_selector` then `matches`, on a document with
//! non-HTML elements, so that what the HTML case rules and the namespace components change
//! can be told apart.
//!
//! Every expected set below was worked out by hand from the cited text, not from a run:
//! Selectors Level 4 (§N), and HTML §4.16.2 "Case-sensitivity of selectors". The arena:
//!
//! ```text
//! html > body >
//!   div#d1 [comment]          div#d2 ["  \n\t\f\r "]    div#d3 ["x"]
//!   div#d4 [U+00A0]           div#d5 [""]                div#hh type=Text viewbox data-a
//!   svg:svg#sv viewBox type=Text >
//!       svg:linearGradient lg, svg:rect r1, svg:rect r2, rect nr (no namespace),
//!       svg:a xa (attribute xlink:href)
//!   ol > li1 "t" em1 li2 <!--c--> li3 em2 li4 em3 svg:li sli
//!   ul > li uli
//! ```

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_selectors::exec_match::matches;
use clazel_selectors::exec_parse::parse_selector;

/// A document mode that can be used twice.
#[derive(Clone, Copy)]
enum Mode {
    NoQuirks,
    Quirks,
}

impl Mode {
    fn get(self) -> DocumentMode {
        match self {
            Mode::NoQuirks => DocumentMode::NoQuirks,
            Mode::Quirks => DocumentMode::Quirks,
        }
    }
}

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// `(in the XLink namespace, local name, value)`.
type Attrs<'a> = &'a [(bool, &'a str, &'a str)];

/// An element in namespace `ns`, with attributes `(namespace, local name, value)`.
fn el(arena: &mut Arena, ns: Option<Namespace>, name: &str, attrs: Attrs) -> usize {
    let id = arena
        .create(ExecKind::Element {
            namespace: ns,
            prefix: None,
            local_name: cps(name),
            attributes: Vec::new(),
            template_contents: None,
            form_owner: None,
        })
        .expect("room in the arena");
    for (ans, n, v) in attrs.iter().copied() {
        arena.append_attribute(
            id,
            ExecAttr {
                namespace: ans.then_some(Namespace::XLink),
                prefix: ans.then(|| cps("xlink")),
                local_name: cps(n),
                value: cps(v),
            },
        );
    }
    id
}

fn html(arena: &mut Arena, name: &str, attrs: Attrs) -> usize {
    el(arena, Some(Namespace::Html), name, attrs)
}

fn svg(arena: &mut Arena, name: &str, attrs: Attrs) -> usize {
    el(arena, Some(Namespace::Svg), name, attrs)
}

fn text(arena: &mut Arena, data: &str) -> usize {
    arena
        .create(ExecKind::Text { data: cps(data) })
        .expect("room")
}

fn comment(arena: &mut Arena, data: &str) -> usize {
    arena
        .create(ExecKind::Comment { data: cps(data) })
        .expect("room")
}

/// The document, and its elements by label, in document order.
fn document(mode: Mode) -> (Arena, Vec<(&'static str, usize)>) {
    let mut a = Arena::new(Vec::new());
    a.set_mode(mode.get());
    let none: Attrs = &[];
    let mut names: Vec<(&'static str, usize)> = Vec::new();
    let mut add = |a: &mut Arena, label: &'static str, parent: usize, node: usize| {
        a.append(parent, node);
        names.push((label, node));
        node
    };
    let h = html(&mut a, "html", none);
    let h = add(&mut a, "html", 0, h);
    let b = html(&mut a, "body", none);
    let body = add(&mut a, "body", h, b);

    let n = html(&mut a, "div", &[(false, "id", "d1")]);
    let d1 = add(&mut a, "d1", body, n);
    let c = comment(&mut a, " nothing ");
    a.append(d1, c);

    let n = html(&mut a, "div", &[(false, "id", "d2")]);
    let d2 = add(&mut a, "d2", body, n);
    let t = text(&mut a, "  \n\t\u{c}\r ");
    a.append(d2, t);

    let n = html(&mut a, "div", &[(false, "id", "d3")]);
    let d3 = add(&mut a, "d3", body, n);
    let t = text(&mut a, "x");
    a.append(d3, t);

    let n = html(&mut a, "div", &[(false, "id", "d4")]);
    let d4 = add(&mut a, "d4", body, n);
    let t = text(&mut a, "\u{a0}");
    a.append(d4, t);

    let n = html(&mut a, "div", &[(false, "id", "d5")]);
    let d5 = add(&mut a, "d5", body, n);
    let t = text(&mut a, "");
    a.append(d5, t);

    let n = html(
        &mut a,
        "div",
        &[
            (false, "id", "hh"),
            (false, "type", "Text"),
            (false, "viewbox", "1"),
            (false, "data-a", "x"),
        ],
    );
    add(&mut a, "hh", body, n);

    let n = svg(
        &mut a,
        "svg",
        &[
            (false, "id", "sv"),
            (false, "viewBox", "0 0 1 1"),
            (false, "type", "Text"),
        ],
    );
    let sv = add(&mut a, "sv", body, n);
    let n = svg(&mut a, "linearGradient", none);
    add(&mut a, "lg", sv, n);
    let n = svg(&mut a, "rect", none);
    add(&mut a, "r1", sv, n);
    let n = svg(&mut a, "rect", none);
    add(&mut a, "r2", sv, n);
    let n = el(&mut a, None, "rect", none);
    add(&mut a, "nr", sv, n);
    let n = svg(&mut a, "a", &[(true, "href", "u")]);
    add(&mut a, "xa", sv, n);

    let n = html(&mut a, "ol", none);
    let ol = add(&mut a, "ol", body, n);
    let n = html(&mut a, "li", none);
    add(&mut a, "li1", ol, n);
    let t = text(&mut a, "t");
    a.append(ol, t);
    let n = html(&mut a, "em", none);
    add(&mut a, "em1", ol, n);
    let n = html(&mut a, "li", none);
    add(&mut a, "li2", ol, n);
    let c = comment(&mut a, "c");
    a.append(ol, c);
    let n = html(&mut a, "li", none);
    add(&mut a, "li3", ol, n);
    let n = html(&mut a, "em", none);
    add(&mut a, "em2", ol, n);
    let n = html(&mut a, "li", none);
    add(&mut a, "li4", ol, n);
    let n = html(&mut a, "em", none);
    add(&mut a, "em3", ol, n);
    let n = svg(&mut a, "li", none);
    add(&mut a, "sli", ol, n);

    let n = html(&mut a, "ul", none);
    let ul = add(&mut a, "ul", body, n);
    let n = html(&mut a, "li", none);
    add(&mut a, "uli", ul, n);
    (a, names)
}

/// The labels of the elements `selector` matches, or `["<invalid>"]`.
fn matched(mode: Mode, selector: &str) -> Vec<&'static str> {
    let (arena, names) = document(mode);
    let Some(s) = parse_selector(&cps(selector)) else {
        return vec!["<invalid>"];
    };
    names
        .iter()
        .filter(|(_, id)| matches(&arena, &s, *id))
        .map(|(n, _)| *n)
        .collect()
}

fn run(mode: Mode, cases: &[(&str, &[&str])]) {
    let mut wrong: Vec<String> = Vec::new();
    for (selector, expected) in cases {
        let got = matched(mode, selector);
        if got != *expected {
            wrong.push(format!("{selector:?}: {got:?}, expected {expected:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

const DIVS: &[&str] = &["d1", "d2", "d3", "d4", "d5", "hh"];

#[test]
fn type_selectors_and_namespace_components_on_non_html_elements() {
    use Mode::NoQuirks;
    run(
        NoQuirks,
        &[
            // HTML §4.16.2: an HTML element's name is compared to the selector lowercased; any
            // other element's "according to its original case".
            ("DIV", DIVS),
            ("Div", DIVS),
            ("linearGradient", &["lg"]),
            ("lineargradient", &[]),
            ("LINEARGRADIENT", &[]),
            ("svg", &["sv"]),
            ("SVG", &[]),
            ("rect", &["r1", "r2", "nr"]),
            ("RECT", &[]),
            // §5.3: `E` with no default namespace is `*|E`: any namespace or none.
            ("*|rect", &["r1", "r2", "nr"]),
            // §5.3: `|E` is an element "without a namespace": only nr.
            ("|rect", &["nr"]),
            ("|div", &[]),
            ("*|div", DIVS),
            ("|*", &["nr"]),
            // A universal selector without a prefix is `*|*`.
            ("svg > *", &["lg", "r1", "r2", "nr", "xa"]),
            ("svg > |*", &["nr"]),
            ("svg > *|*", &["lg", "r1", "r2", "nr", "xa"]),
            // The same rules in compounds and combinators.
            ("svg > |rect", &["nr"]),
            ("svg|rect", &["<invalid>"]),
            // A list: the union, each item with its own namespace rule.
            ("|rect, linearGradient", &["lg", "nr"]),
            // Case differs between an HTML `li` and an SVG one only by namespace: both match `li`.
            ("li", &["li1", "li2", "li3", "li4", "sli", "uli"]),
            ("LI", &["li1", "li2", "li3", "li4", "uli"]),
            ("ol > li", &["li1", "li2", "li3", "li4", "sli"]),
        ],
    );
}

#[test]
fn attribute_name_and_value_case_in_html_and_non_html() {
    use Mode::NoQuirks;
    run(
        NoQuirks,
        &[
            // HTML §4.16.2: on an HTML element in an HTML document the selector's attribute name
            // is lowercased first; on other elements it is compared in its own case.
            ("[viewBox]", &["hh", "sv"]),
            ("[viewbox]", &["hh"]),
            ("[VIEWBOX]", &["hh"]),
            ("[DATA-A]", &["hh"]),
            ("[data-a]", &["hh"]),
            // §6.4: without a namespace component, only attributes without a namespace.
            ("[href]", &[]),
            ("[*|href]", &["xa"]),
            ("[|href]", &[]),
            ("[*|viewBox]", &["hh", "sv"]),
            ("[|viewBox]", &["hh", "sv"]),
            // §6.1: `[att]` is presence.
            ("[id]", &["d1", "d2", "d3", "d4", "d5", "hh", "sv"]),
            ("[id^=d]", &["d1", "d2", "d3", "d4", "d5"]),
            ("[id$=h]", &["hh"]),
            ("[id*=\"5\"]", &["d5"]),
            ("[id|=d1]", &["d1"]),
            ("[id~=hh]", &["hh"]),
            // HTML §4.16.2's list of attributes whose values are case-insensitive (it includes
            // `type`), for HTML elements only.
            ("[type=text]", &["hh"]),
            ("[type=Text]", &["hh", "sv"]),
            ("[type=TEXT i]", &["hh", "sv"]),
            // §6.3: the `s` flag is case-sensitive "regardless of document language rules".
            ("[type=text s]", &[]),
            ("[type=Text s]", &["hh", "sv"]),
            // An attribute that is not in the list is case-sensitive on HTML elements too.
            ("[id=D1]", &[]),
            ("[id=D1 i]", &["d1"]),
            ("[data-a=X]", &[]),
        ],
    );
}

#[test]
fn nth_child_and_nth_of_type_with_negative_and_zero_a() {
    use Mode::NoQuirks;
    // In `ol`, the elements are li1=1 em1=2 li2=3 li3=4 em2=5 li4=6 em3=7 sli=8 (text and
    // comments are not counted, §15.3). Among HTML li: li1..li4 are 1..4; sli, in the SVG
    // namespace, is a different type (§15.4: same expanded element name), the first of its
    // own. em1..em3 are 1..3.
    run(
        NoQuirks,
        &[
            // §15.3.1: elements with An+B-1 siblings before them, for n >= 0.
            ("ol > :nth-child(-n+3)", &["li1", "em1", "li2"]),
            ("ol > :nth-child(0n+4)", &["li3"]),
            ("ol > :nth-child(0)", &[]),
            ("ol > :nth-child(0n)", &[]),
            ("ol > :nth-child(-2n+7)", &["li1", "li2", "em2", "em3"]),
            ("ol > :nth-child(even)", &["em1", "li3", "li4", "sli"]),
            ("ol > :nth-child(odd)", &["li1", "li2", "em2", "em3"]),
            ("ol > :nth-child(n+7)", &["em3", "sli"]),
            ("ol > :nth-child(3n-1)", &["em1", "em2", "sli"]),
            ("ol > :nth-child(-n)", &[]),
            ("ol > :nth-child(-3)", &[]),
            // Clamped A and B give the same sets as exact arithmetic would, since only n = 0
            // reaches the child indexes.
            ("ol > :nth-child(99999999999n+1)", &["li1"]),
            ("ol > :nth-child(-99999999999n+2)", &["em1"]),
            ("ol > :nth-child(2147483648)", &[]),
            ("ol > :nth-child(-2147483649n-5)", &[]),
            // §15.3.2: from the end.
            ("ol > :nth-last-child(2)", &["em3"]),
            ("ol > :nth-last-child(-n+2)", &["em3", "sli"]),
            ("ol > :nth-last-child(0n+8)", &["li1"]),
            // From the end li4 is 3rd and li2 6th (n = 0 gives 0, which is no index).
            ("ol > :nth-last-child(3n)", &["li2", "li4"]),
            // §15.4.1: of the same type only.
            ("ol > li:nth-of-type(2)", &["li2"]),
            ("ol > li:nth-of-type(-n+2)", &["li1", "li2", "sli"]),
            ("ol > li:nth-of-type(0n+3)", &["li3"]),
            ("ol > li:nth-of-type(0)", &[]),
            ("ol > li:nth-of-type(odd)", &["li1", "li3", "sli"]),
            ("ol > em:nth-of-type(odd)", &["em1", "em3"]),
            ("ol > em:nth-of-type(n+2)", &["em2", "em3"]),
            // §15.4.2: of the same type, from the end.
            ("ol > li:nth-last-of-type(1)", &["li4", "sli"]),
            ("ol > li:nth-last-of-type(2)", &["li3"]),
            ("ol > em:nth-last-of-type(2)", &["em2"]),
            ("ol > em:nth-last-of-type(-n+2)", &["em2", "em3"]),
            ("ol > li:nth-last-of-type(0)", &[]),
            // §15.4.3 to §15.4.5.
            ("ol > li:first-of-type", &["li1", "sli"]),
            ("ol > li:last-of-type", &["li4", "sli"]),
            ("ol > li:only-of-type", &["sli"]),
            ("ol > em:only-of-type", &[]),
            // §15.3.3 to §15.3.5.
            ("ol > :first-child", &["li1"]),
            ("ol > :last-child", &["sli"]),
            ("body > :only-child", &[]),
            ("ul > :only-child", &["uli"]),
        ],
    );
}

#[test]
fn empty_with_comments_and_whitespace_text() {
    use Mode::NoQuirks;
    run(
        NoQuirks,
        &[
            // §15.2: only elements and text with non-zero length affect emptiness, and document
            // white space does not (U+0009, U+000A, U+000C, U+000D, U+0020 here): d1 has a
            // comment only, d2 white space only, d5 an empty text node, hh nothing.
            // d3 holds "x" and d4 U+00A0, which is not document white space.
            ("div:empty", &["d1", "d2", "d5", "hh"]),
            ("div:not(:empty)", &["d3", "d4"]),
            ("#d1:empty", &["d1"]),
            ("#d2:empty", &["d2"]),
            ("#d3:empty", &[]),
            ("#d4:empty", &[]),
            ("ol:empty", &[]),
        ],
    );
}

#[test]
fn not_with_complex_arguments() {
    use Mode::NoQuirks;
    run(
        NoQuirks,
        &[
            // §4.3: :not(S) matches what no complex selector of S matches, combinators included.
            ("li:not(ul > li)", &["li1", "li2", "li3", "li4", "sli"]),
            ("li:not(ol > li)", &["uli"]),
            (
                "li:not(ul > li, ol > li:first-child)",
                &["li2", "li3", "li4", "sli"],
            ),
            (
                "li:not(:is(ol, ul) > li:nth-child(odd))",
                &["li3", "li4", "sli"],
            ),
            // li3 and li4 follow an li or an em; `li + *` is an element right after an li.
            ("ol > :not(li + *)", &["li1", "li2", "li4", "sli"]),
            ("ol > :not(li ~ em)", &["li1", "li2", "li3", "li4", "sli"]),
            ("ol > :not(em ~ li)", &["li1", "em1", "em2", "em3"]),
            // `li` matches the SVG li too, so sli follows li1 and is excluded as well.
            ("ol > :not(li ~ li)", &["li1", "em1", "em2", "em3"]),
            // A descendant combinator in the argument.
            ("li:not(body li)", &[]),
            ("li:not(ul li)", &["li1", "li2", "li3", "li4", "sli"]),
        ],
    );
}

#[test]
fn quirks_mode_still_matches_names_case_sensitively_for_non_html() {
    use Mode::Quirks;
    // §7 and HTML §4.16.2: quirks mode folds only class and ID values; type names of
    // non-HTML elements and attribute names stay as they are.
    run(
        Quirks,
        &[
            ("#D1", &["d1"]),
            ("lineargradient", &[]),
            ("linearGradient", &["lg"]),
            ("[viewbox]", &["hh"]),
            ("[id=D1]", &[]),
        ],
    );
}

/// `n` levels of `open` around `x`.
fn nested(open: &str, x: &str, n: usize) -> String {
    format!("{}{}{}", open.repeat(n), x, ")".repeat(n))
}

#[test]
fn nesting_is_accepted_at_max_nesting_and_refused_one_past() {
    use Mode::NoQuirks;
    // contract.rs: MAX_NESTING = 32 levels of functions inside functions; the spec has no
    // limit, so 33 levels of an otherwise valid selector are the one place the parser may
    // answer "invalid" where the standard does not.
    assert_eq!(clazel_selectors::contract::MAX_NESTING, 32);
    for open in [":is(", ":where(", ":not("] {
        let ok = nested(open, "ul", 32);
        let over = nested(open, "ul", 33);
        // 32 levels of :not() is an even number of negations: `ul` itself (§4.3).
        assert_eq!(matched(NoQuirks, &ok), ["ul"], "{open} x32");
        assert_eq!(matched(NoQuirks, &over), ["<invalid>"], "{open} x33");
        // One fewer is accepted too.
        // 31 levels of :not() is odd: every element but `ul`.
        let every_element = document(NoQuirks).1.len();
        let expected = if open == ":not(" {
            every_element - 1
        } else {
            1
        };
        assert_eq!(
            matched(NoQuirks, &nested(open, "ul", 31)).len(),
            expected,
            "{open} x31"
        );
    }
    // Mixed functions count together.
    let mixed32 = format!(
        "{}ul{}",
        ":is(:not(:where(".repeat(10) + ":is(:not(",
        ")".repeat(32)
    );
    let mixed33 = format!("{}ul{}", ":is(:not(:where(".repeat(11), ")".repeat(33));
    assert!(parse_selector(&cps(&mixed32)).is_some());
    assert!(parse_selector(&cps(&mixed33)).is_none());
    // The limit is on nesting, not on length: 33 siblings at one level are fine.
    let wide = format!(":is({})", vec!["ul"; 200].join(","));
    assert_eq!(matched(NoQuirks, &wide), ["ul"]);
}
