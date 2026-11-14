//! The rule index (`clazel_style::cascade::index`) against the cascade without it, on
//! random rule sets over random documents: the computed tables must be equal.
//!
//! Each round builds a document of up to 24 elements (`div`, `span`, `p`, `a`, `ul`, `li`,
//! `table`, `td`, `svg` with a `foreignObject`, in random nesting; random `id`s and
//! `class`es in mixed case, with tabs and form feeds between words, and the attributes
//! `lang`, `title`, `data-k`, `href` and `type` with values of mixed case, some of them
//! with a hyphen or a shared prefix) in no-quirks or quirks mode, and up to 16 rules whose
//! selectors combine type, universal, ID, class and attribute selectors (presence, `=`,
//! `~=`, `|=`, `^=`, `$=`, `*=`, with and without the `i` flag), `:is()`, `:where()`,
//! `:not()`, `:first-child`, and all four combinators, each setting `color` and
//! `margin-left` to values that tell the rules apart. A deterministic generator (xorshift),
//! seeded by [`SEEDS`], makes every run the same.
//!
//! The comparison would hold vacuously if no rule ever matched, so every run counts the
//! elements whose `margin-left` a rule set (no user agent rule gives these elements one) and
//! asserts a minimum, [`MIN_STYLED`], measured when the test was written, and that rules of
//! several selector kinds matched.

use std::fmt::Write as _;

use clazel_dom::exec::Arena;
use clazel_style::cascade::computed::{Lp, Size};
use clazel_style::cascade::{cascade, cascade_unindexed};
use clazel_style::sources::{Device, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

struct NoEncodings;

impl EncFnsExec for NoEncodings {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

fn parse(html: &str) -> Arena {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    let url: Vec<u32> = "http://example.com/".chars().map(u32::from).collect();
    parse_real(&NoEncodings, &input, url, false, false).0.arena
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        usize::try_from(
            self.next()
                .checked_rem(u64::try_from(n).unwrap_or(1))
                .unwrap_or(0),
        )
        .unwrap_or(0)
    }

    fn pick<'a>(&mut self, items: &[&'a str]) -> &'a str {
        let i = self.below(items.len());
        items.get(i).copied().unwrap_or("")
    }
}

const TYPES: &[&str] = &[
    "div",
    "span",
    "p",
    "a",
    "ul",
    "li",
    "td",
    "DIV",
    "Span",
    "foreignObject",
    "foreignobject",
];
const CLASSES: &[&str] = &["a", "b", "c", "A", "Bb", "bb"];
const IDS: &[&str] = &["x", "y", "X"];
const ATTRS: &[&str] = &["lang", "title", "data-k", "href", "type", "LANG"];
const VALUES: &[&str] = &[
    "en", "EN", "en-US", "en-us", "abc", "ABC", "abcabc", "x-y", "",
];
const OPS: &[&str] = &["=", "~=", "|=", "^=", "$=", "*="];
const COMBINATORS: &[&str] = &[" ", " > ", " + ", " ~ "];

fn compound(r: &mut Rng, depth: u32) -> String {
    let mut out = String::new();
    match r.below(3) {
        0 => out.push_str(r.pick(TYPES)),
        1 => out.push('*'),
        _ => {}
    }
    for _ in 0..r.below(3) {
        match r.below(8) {
            0 => {
                let _ = write!(out, "#{}", r.pick(IDS));
            }
            1 | 2 => {
                let _ = write!(out, ".{}", r.pick(CLASSES));
            }
            3 => {
                let _ = write!(out, "[class~={}]", r.pick(CLASSES));
            }
            5 => {
                let name = r.pick(ATTRS);
                match r.below(3) {
                    0 => {
                        let _ = write!(out, "[{name}]");
                    }
                    k => {
                        let (op, value) = (r.pick(OPS), r.pick(VALUES));
                        let flag = if k == 1 { "" } else { " i" };
                        let _ = write!(out, "[{name}{op}\"{value}\"{flag}]");
                    }
                }
            }
            4 => out.push_str(":first-child"),
            _ if depth > 0 => {
                let f = r.pick(&[":is", ":where", ":not"]);
                let a = complex(r, depth.saturating_sub(1));
                let b = complex(r, depth.saturating_sub(1));
                let _ = write!(out, "{f}({a}, {b})");
            }
            _ => {}
        }
    }
    if out.is_empty() {
        out.push('*');
    }
    out
}

fn complex(r: &mut Rng, depth: u32) -> String {
    let mut out = compound(r, depth);
    for _ in 0..r.below(3) {
        out.push_str(r.pick(COMBINATORS));
        out.push_str(&compound(r, depth));
    }
    out
}

fn element(r: &mut Rng, html: &mut String, budget: &mut usize, depth: u32) {
    if *budget == 0 {
        return;
    }
    *budget = budget.saturating_sub(1);
    let name = r.pick(&["div", "span", "p", "a", "ul", "li", "div", "svg"]);
    let _ = write!(html, "<{name}");
    if r.below(3) == 0 {
        let _ = write!(html, " id={}", r.pick(IDS));
    }
    for name in ["lang", "title", "data-k", "href", "type"] {
        if r.below(3) == 0 {
            let _ = write!(html, " {name}=\"{}\"", r.pick(VALUES));
        }
    }
    if r.below(2) == 0 {
        let a = r.pick(CLASSES);
        let b = r.pick(CLASSES);
        let sep = r.pick(&[" ", "\t", "\u{c}", "  "]);
        let _ = write!(html, " class=\"{a}{sep}{b}\"");
    }
    html.push('>');
    if name == "svg" {
        html.push_str("<foreignObject class=a><span class=b>s</span></foreignObject>");
    } else if depth > 0 {
        for _ in 0..r.below(4) {
            element(r, html, budget, depth.saturating_sub(1));
        }
    }
    let _ = write!(html, "</{name}>");
}

/// The generator's seeds: each gives a different run of documents and rule sets.
const SEEDS: &[u64] = &[
    0x9E37_79B9_7F4A_7C15,
    0x0123_4567_89AB_CDEF,
    0xDEAD_BEEF_CAFE_F00D,
    0x1357_9BDF_0246_8ACE,
    0xFEED_FACE_0BAD_C0DE,
];

/// The fewest styled elements (those a rule gave a `margin-left`) over all seeds and rounds,
/// measured when the test was written (13,642 of 21,286 nodes), rounded down.
const MIN_STYLED: usize = 10_000;

#[test]
#[cfg_attr(
    miri,
    ignore = "each round cascades with the whole user agent sheets twice, minutes under Miri; \
              the index runs under Miri in every other cascade test"
)]
fn index_gives_the_same_tables_as_trying_every_rule() {
    let rounds = 120;
    let mut styled = 0usize;
    let mut elements = 0usize;
    let mut rounds_with_matches = 0usize;
    for &seed in SEEDS {
        let mut r = Rng(seed);
        for round in 0..rounds {
            let mut html = String::new();
            if r.below(2) == 0 {
                html.push_str("<!DOCTYPE html>");
            }
            html.push_str("<style>");
            for k in 0..r.below(16).saturating_add(1) {
                let list: Vec<String> = (0..r.below(2).saturating_add(1))
                    .map(|_| complex(&mut r, 1))
                    .collect();
                // `k + 1` px: no user agent rule gives these elements a margin-left of
                // 1 to 16px, so a margin-left in that range is a rule's.
                let _ = write!(
                    html,
                    "{} {{ color: rgb({k}, 0, 0); margin-left: {}px }}",
                    list.join(", "),
                    k.saturating_add(1)
                );
            }
            html.push_str("</style><body>");
            let mut budget = 24usize;
            for _ in 0..4 {
                element(&mut r, &mut html, &mut budget, 3);
            }
            let arena = parse(&html);
            let sources = collect(&arena);
            let device = Device::screen(800, 600);
            let indexed = cascade(&arena, &sources, device);
            assert!(
                indexed == cascade_unindexed(&arena, &sources, device),
                "seed {seed:#x} round {round}: {html}"
            );
            let hit = indexed
                .styles
                .iter()
                .flatten()
                .filter(|s| {
                    s.margin.get(3).is_some_and(|m| {
                        (1..=16_i32).any(|k| *m == Size::Lp(Lp::Px64(k.saturating_mul(64))))
                    })
                })
                .count();
            styled = styled.saturating_add(hit);
            elements = elements.saturating_add(arena.len());
            rounds_with_matches = rounds_with_matches.saturating_add(usize::from(hit > 0));
        }
    }
    println!("styled {styled} of {elements} nodes, {rounds_with_matches} rounds with matches");
    assert!(styled >= MIN_STYLED, "styled {styled}");
    assert!(
        rounds_with_matches >= SEEDS.len().saturating_mul(rounds) / 2,
        "{rounds_with_matches} rounds with matches"
    );
}

/// The attribute selectors the generator uses do match, through the index and without it:
/// a fixed document, and for each operator the elements Selectors 4 §6.1 and §6.2 say it
/// matches, derived by hand: `=` the whole value; `~=` a whitespace-separated word; `|=`
/// the value, or the value followed by a hyphen; `^=`, `$=`, `*=` prefix, suffix, substring
/// (an empty value matches nothing); the `i` flag ignores ASCII case in the value.
#[test]
fn attribute_selectors_match_in_both_cascades() {
    let html = "<!DOCTYPE html><style>\
        [lang=en] { margin-left: 1px }\
        [lang=\"en\" i] { margin-top: 2px }\
        [title~=b] { margin-left: 3px }\
        [lang|=en] { margin-right: 4px }\
        [title^=ab] { margin-bottom: 5px }\
        [title$=bc] { margin-bottom: 6px }\
        [title*=\"b c\"] { margin-top: 7px }\
        [data-k] { margin-right: 8px }\
        [title^=\"\"] { margin-left: 9px }\
        </style><body>\
        <p id=a lang=en title=\"a b\">1</p>\
        <p id=b lang=EN title=abc>2</p>\
        <p id=c lang=en-US title=\"a b c\">3</p>\
        <p id=d lang=en-us data-k>4</p>\
        <p id=e lang=\"\" title=x>5</p>";
    let arena = parse(html);
    let sources = collect(&arena);
    let device = Device::screen(800, 600);
    let indexed = cascade(&arena, &sources, device);
    assert!(indexed == cascade_unindexed(&arena, &sources, device));
    let side = |id: &str, i: usize| {
        let node = (0..arena.len()).find(|&n| {
            clazel_style::cascade::hints::html_element(&arena, n).is_some_and(|(_, attributes)| {
                clazel_style::cascade::hints::attribute(attributes, "id")
                    .is_some_and(|v| v.iter().copied().eq(id.chars().map(u32::from)))
            })
        })?;
        indexed.get(node)?.margin.get(i).copied()
    };
    let px = |v: i32| Size::Lp(Lp::Px64(v.saturating_mul(64)));
    // HTML §4.2 "Case-sensitivity of selectors": the values of `lang` (and of `type`, `rel`,
    // ...) are ASCII case-insensitive in an HTML document; `title`'s are not.
    // margin-left (the index 3 of top, right, bottom, left): `[lang=en]` 1px (a and b; c is
    // en-US), then `[title~=b]` 3px (a and c have the word b), later and so the winner; the
    // empty `[title^=""]` matches nothing, so 9px is never set.
    assert_eq!(side("a", 3), Some(px(3)));
    assert_eq!(side("b", 3), Some(px(1)));
    assert_eq!(side("c", 3), Some(px(3)));
    assert_eq!(side("d", 3), Some(px(0)));
    assert_eq!(side("e", 3), Some(px(0)));
    // margin-right: `[lang|=en]` 4px (en, EN, en-US, en-us; not the empty lang), then
    // `[data-k]` 8px (d).
    assert_eq!(side("a", 1), Some(px(4)));
    assert_eq!(side("b", 1), Some(px(4)));
    assert_eq!(side("c", 1), Some(px(4)));
    assert_eq!(side("d", 1), Some(px(8)));
    assert_eq!(side("e", 1), Some(px(0)));
    // margin-top: `[lang="en" i]` 2px (a, b), then `[title*="b c"]` 7px (c). The others have
    // the user agent's 1em, 16px.
    assert_eq!(side("a", 0), Some(px(2)));
    assert_eq!(side("b", 0), Some(px(2)));
    assert_eq!(side("c", 0), Some(px(7)));
    assert_eq!(side("d", 0), Some(px(16)));
    // margin-bottom: `[title^=ab]` 5px (abc), then `[title$=bc]` 6px (abc; "a b c" ends
    // in " c", not "bc").
    assert_eq!(side("b", 2), Some(px(6)));
    assert_eq!(side("c", 2), Some(px(16)));
    assert_eq!(side("a", 2), Some(px(16)));
}
