//! The cascade at scale (phase-5.md item 5.26's CSS bomb "10,000 rules over 100,000
//! elements"): a page of `E` `div`s, each holding a `span`, styled by `R` rules
//! `.cN span { color: … }`, the `div`s' classes cycling through `c0` to `c(R-1)`.
//!
//! `cascade_scale` is a measurement, not a check: run by hand in release, one shape per run, as
//! `CLAZEL_SCALE=RxE cargo test --release -p clazel-style --test cascade_scale -- \
//! --ignored --nocapture`. It prints the time to parse the page, to collect its style
//! sources and to cascade it. With `CLAZEL_UNINDEXED=1` it cascades without the rule index
//! (`cascade_unindexed`, every rule tried against every element), as before the index.
//!
//! `index_candidates_do_not_grow_with_the_rule_count` is the check, and always runs: it counts
//! the rules the index offers each element (not time) and requires one per `span`, whatever
//! the number of rules.

use std::fmt::Write as _;
use std::time::Instant;

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

/// The page with `rules` rules over `divs` `div`s.
pub fn page(rules: usize, divs: usize) -> String {
    let mut html = String::from("<!DOCTYPE html><style>");
    for i in 0..rules {
        let _ = writeln!(html, ".c{i} span {{ color: rgb(0, 0, {}) }}", i & 255);
    }
    html.push_str("</style>");
    for i in 0..divs {
        let _ = write!(
            html,
            "<div class=c{}><span>x</span></div>",
            i.checked_rem(rules).unwrap_or(0)
        );
    }
    html
}

#[test]
#[ignore = "a measurement, run by hand in release (see the module's documentation)"]
fn cascade_scale() {
    let shape = std::env::var("CLAZEL_SCALE").unwrap_or_else(|_| "1000x10000".into());
    let (r, e) = shape.split_once('x').unwrap_or(("1000", "10000"));
    let rules: usize = r.parse().unwrap_or(1000);
    let divs: usize = e.parse().unwrap_or(10000);
    let html = page(rules, divs);
    let t = Instant::now();
    let arena = parse(&html);
    let parsed = t.elapsed();
    let t = Instant::now();
    let sources = collect(&arena);
    let collected = t.elapsed();
    let t = Instant::now();
    let unindexed = std::env::var_os("CLAZEL_UNINDEXED").is_some_and(|v| v == "1");
    let device = Device::screen(800, 600);
    let table = if unindexed {
        cascade_unindexed(&arena, &sources, device)
    } else {
        cascade(&arena, &sources, device)
    };
    let cascaded = t.elapsed();
    let styled = table.styles.iter().filter(|s| s.is_some()).count();
    println!(
        "unindexed={unindexed} rules={rules} divs={divs} nodes={} styled={styled} parse={parsed:?} \
         collect={collected:?} cascade={cascaded:?}",
        arena.len()
    );
}

/// A deterministic guard on the index's complexity claim (`cascade::index`'s module
/// documentation): the rules an element is matched against are found by keys, so the matches
/// tried grow with the elements, not with rules times elements. It counts candidates, not
/// time. For the page of `page(R, 2R)`, the rule `.cN span` is filed under the subject key
/// `span` and the ancestor key `.cN`; the `span` of the `i`th `div` has the ancestors
/// `div.c(i mod R)`, `body` and `html`, so its one candidate is rule `i mod R`, and a `div`
/// (subject key `div`, `.cN` and the class) has none. So the total over all elements is
/// exactly the number of `span`s, `2R`, for every `R`; without the index it would be
/// `R` per element.
#[test]
fn index_candidates_do_not_grow_with_the_rule_count() {
    use clazel_style::cascade::index::{Ancestors, Key, RuleIndex, element_keys};
    use clazel_style::cascade::rules::Selectors;

    let candidates_for = |rules: usize| -> (usize, usize, usize) {
        let divs = rules.saturating_mul(2);
        let arena = parse(&page(rules, divs));
        let entries: Vec<(usize, Option<Key>, Option<Key>)> = (0..rules)
            .flat_map(|i| {
                let text: Vec<u32> = format!(".c{i} span").chars().map(u32::from).collect();
                let selectors = Selectors::parse(&text);
                selectors
                    .map(|s| s.index_keys())
                    .unwrap_or_default()
                    .into_iter()
                    .map(move |(subject, ancestor)| (i, subject, ancestor))
            })
            .collect();
        let index = RuleIndex::new(entries);
        let mut total = 0usize;
        let mut elements = 0usize;
        let mut spans = 0usize;
        for n in 0..arena.len() {
            let clazel_dom::exec::ExecKind::Element { local_name, .. } = arena.kind(n) else {
                continue;
            };
            elements = elements.saturating_add(1);
            let mut ancestors: Ancestors<Key> = Ancestors::default();
            let mut up = arena.parent(n);
            while let Some(p) = up {
                if matches!(arena.kind(p), clazel_dom::exec::ExecKind::Element { .. }) {
                    ancestors.push(&element_keys(arena.kind(p)));
                }
                up = arena.parent(p);
            }
            let found = index.candidates(&element_keys(arena.kind(n)), &ancestors);
            let is_span = local_name.iter().copied().eq("span".chars().map(u32::from));
            if is_span {
                spans = spans.saturating_add(1);
            } else {
                assert!(
                    found.is_empty(),
                    "a non-span element has no candidate: {found:?}"
                );
            }
            total = total.saturating_add(found.len());
        }
        (total, spans, elements)
    };
    // Under Miri the largest page takes most of half an hour: small pages only.
    let sizes: &[usize] = if cfg!(miri) {
        &[12, 24]
    } else {
        &[50, 200, 800]
    };
    for &rules in sizes {
        let (total, spans, elements) = candidates_for(rules);
        assert_eq!(spans, rules.saturating_mul(2));
        assert_eq!(total, spans, "{rules} rules: one candidate per span");
        // The unindexed work would be rules x elements matches.
        assert!(total.saturating_mul(10) < elements.saturating_mul(rules));
    }
}
