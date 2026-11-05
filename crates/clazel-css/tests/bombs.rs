//! Sheets a page could write to hurt the parser. Each must finish, with no stack overflow
//! and in time linear in its size: the depth is far beyond any thread's stack, and doubling
//! the size must not do much more than double the time. Item 5.26 runs these through a real
//! sandboxed renderer, at 64 MiB, with the memory bound checked.

use clazel_css::parser::exec_parse::parse_stylesheet_contents;
use std::time::{Duration, Instant};

/// `times` copies of `open`, then `times` copies of `close`.
fn nested(open: &str, close: &str, times: usize) -> Vec<u32> {
    let mut sheet = open.repeat(times);
    sheet.push_str(&close.repeat(times));
    sheet.chars().map(u32::from).collect()
}

fn time(input: &[u32]) -> Duration {
    let start = Instant::now();
    let parsed = parse_stylesheet_contents(input);
    let spent = start.elapsed();
    assert!(parsed.output.rows.len() <= input.len());
    spent
}

/// Parses at two sizes and fails if the larger is out of proportion. Times are noisy, so the
/// limit is far above 2 and far below the 16 that quadratic work would give for 4 times the
/// input, and a time too short to measure is passed.
fn linear(open: &str, close: &str) {
    let small = nested(open, close, 50_000);
    let large = nested(open, close, 200_000);
    let (a, b) = (time(&small), time(&large));
    println!("{open:?} {close:?}: {a:?} then {b:?}");
    let floor = Duration::from_millis(5);
    assert!(
        b < a.max(floor).saturating_mul(10),
        "{open:?} {close:?} took {a:?} then {b:?}"
    );
}

#[test]
#[cfg_attr(miri, ignore = "minutes under Miri, and Miri has no use for the timing")]
fn curly_brackets() {
    linear("{", "");
    linear("{", "}");
}

#[test]
#[cfg_attr(miri, ignore = "minutes under Miri, and Miri has no use for the timing")]
fn other_brackets() {
    linear("(", "");
    linear("[", "]");
    linear("a(", ")");
}

#[test]
#[cfg_attr(miri, ignore = "minutes under Miri, and Miri has no use for the timing")]
fn rules_inside_rules() {
    linear("a{", "}");
    linear("a b{", "}");
    linear("@a{", "}");
}

#[test]
#[cfg_attr(miri, ignore = "minutes under Miri, and Miri has no use for the timing")]
fn declarations_that_are_rules() {
    linear("a:b{", "}");
    linear("--a:b{", "}");
}

#[test]
#[cfg_attr(miri, ignore = "minutes under Miri, and Miri has no use for the timing")]
fn a_block_as_a_value() {
    linear("a:{", "}");
}

/// A sheet of `{`, 64 MiB of code points unless `CLAZEL_BOMB_MIB` says otherwise, for
/// measuring: run it alone in a release build and read the process's peak memory.
#[test]
#[ignore = "takes a few seconds and gigabytes; run by hand to measure against 5.26's bound"]
fn sixty_four_mib_of_curly_brackets() {
    let mib = std::env::var("CLAZEL_BOMB_MIB")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(64);
    let sheet = vec![0x7Bu32; mib.saturating_mul(1024 * 1024)];
    let start = Instant::now();
    let parsed = parse_stylesheet_contents(&sheet);
    println!(
        "{:?}: {} rows, {} items, {} declarations",
        start.elapsed(),
        parsed.output.rows.len(),
        parsed.output.items.len(),
        parsed.output.declarations.len()
    );
}
