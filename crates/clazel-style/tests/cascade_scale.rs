//! The cascade at scale (phase-5.md item 5.26's CSS bomb "10,000 rules over 100,000
//! elements"): a page of `E` `div`s, each holding a `span`, styled by `R` rules
//! `.cN span { color: … }`, the `div`s' classes cycling through `c0` to `c(R-1)`.
//!
//! A measurement, not a check: run by hand in release, one shape per run, as
//! `CLAZEL_SCALE=RxE cargo test --release -p clazel-style --test cascade_scale -- \
//! --ignored --nocapture`. It prints the time to parse the page, to collect its style
//! sources and to cascade it. With `CLAZEL_UNINDEXED=1` it cascades without the rule index
//! (`cascade_unindexed`, every rule tried against every element), as before the index.

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
