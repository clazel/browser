//! The rule index (`clazel_style::cascade::index`) against the cascade without it, on
//! random rule sets over random documents: the computed tables must be equal.
//!
//! Each round builds a document of up to 24 elements (`div`, `span`, `p`, `a`, `ul`, `li`,
//! `table`, `td`, `svg` with a `foreignObject`, in random nesting; random `id`s and
//! `class`es in mixed case, with tabs and form feeds between words) in no-quirks or quirks
//! mode, and up to 16 rules whose selectors combine type, universal, ID, class and
//! attribute selectors, `:is()`, `:where()`, `:not()`, `:first-child`, and all four
//! combinators, each setting `color` and `margin-left` to values that tell the rules apart.
//! A deterministic generator (xorshift) makes every run the same.

use std::fmt::Write as _;

use clazel_dom::exec::Arena;
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
const COMBINATORS: &[&str] = &[" ", " > ", " + ", " ~ "];

fn compound(r: &mut Rng, depth: u32) -> String {
    let mut out = String::new();
    match r.below(3) {
        0 => out.push_str(r.pick(TYPES)),
        1 => out.push('*'),
        _ => {}
    }
    for _ in 0..r.below(3) {
        match r.below(7) {
            0 => {
                let _ = write!(out, "#{}", r.pick(IDS));
            }
            1 | 2 => {
                let _ = write!(out, ".{}", r.pick(CLASSES));
            }
            3 => {
                let _ = write!(out, "[class~={}]", r.pick(CLASSES));
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

#[test]
#[cfg_attr(
    miri,
    ignore = "each round cascades with the whole user agent sheets twice, minutes under Miri; \
              the index runs under Miri in every other cascade test"
)]
fn index_gives_the_same_tables_as_trying_every_rule() {
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    let rounds = 300;
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
            let _ = write!(
                html,
                "{} {{ color: rgb({k}, 0, 0); margin-left: {k}px }}",
                list.join(", ")
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
        assert!(
            cascade(&arena, &sources, device) == cascade_unindexed(&arena, &sources, device),
            "round {round}: {html}"
        );
    }
}
