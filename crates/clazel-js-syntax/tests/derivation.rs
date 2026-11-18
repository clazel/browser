//! The proven check of the whole arena against the tokens
//! ([`clazel_js_syntax::arena_d`]): which programs it covers, that it never
//! finds a covered node the parser built wrongly, and what it costs.

use clazel_js_syntax::arena_d::Derivation;
use clazel_js_syntax::exec::parse_checked;
use clazel_js_syntax::spec::SourceGoal;
use std::time::Instant;

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn derivation(s: &str, goal: SourceGoal) -> Option<Derivation> {
    parse_checked(&cps(s), goal).ok().map(|(_, d)| d)
}

#[test]
fn covered_programs_are_verified() {
    for s in [
        "",
        ";",
        ";;",
        "1;",
        "1\n2\n3",
        "1 + 2 * 3;",
        "(1 + 2) * 3\n4 < 5 > 6",
        "'a'; ; /re/;",
        "((1));",
        "1 - 2 - 3 / 4 % 5;",
        "2 ** 3 ** 2;",
        "1 << 2 >> 3 >>> 4;",
        "1 == 2 != 3 === 4 !== 5;",
        "1 & 2 ^ 3 | 4;",
        "1 && 2 || 3 && 4;",
        "1 ?? 2 ?? 3;",
        "1 <= 2 >= 3 < 4;",
        "1 in 2 instanceof 3;",
        "-1; !2; ~3; +4; typeof 5; void 6; delete (7).a;",
        "- -1 + +2;",
        "1 ? 2 : 3 ? 4 : 5;",
        "(1).a;",
        "(1).a.b.c;",
        "(1).a = 2;",
        "(1).a += 2 ** 3;",
        "(1).a &&= (1).b ||= 3;",
        "a;",
        "a + b * c;",
        "a.b.c = d ? e : f;",
        "typeof a === 'x';",
        "a in b;",
        "// c\n 1 /* d */ + 2 ;;",
    ] {
        assert!(
            derivation(s, SourceGoal::Script) == Some(Derivation::Verified),
            "{s}"
        );
        assert!(
            derivation(s, SourceGoal::Module) == Some(Derivation::Verified),
            "{s}"
        );
    }
}

#[test]
fn other_programs_are_unsupported_not_failed() {
    for s in ["f(1);", "if (1) ;", "var a = 1;"] {
        assert!(
            derivation(s, SourceGoal::Script) == Some(Derivation::Unsupported),
            "{s}"
        );
    }
}

#[test]
fn errors_are_still_errors() {
    for s in ["1 +", "(", "1 2", ")"] {
        assert!(derivation(s, SourceGoal::Script).is_none(), "{s}");
    }
}

/// The cost of the check: the same program of covered nodes, parsed with the
/// check running to the end and with an uncovered node first, which stops it at
/// once (the parse and the other checks of `parse` are the same).
#[test]
fn what_the_check_costs() {
    let body = "(1 + 2 * 3) < 4 - 5 / 6 % 7;\n".repeat(60_000);
    let covered = cps(&body);
    let stopped = cps(&format!("this;\n{body}"));
    let time = |src: &[u32]| {
        let t = Instant::now();
        let r = parse_checked(src, SourceGoal::Script);
        (t.elapsed(), r.map(|(_, d)| d).ok())
    };
    let (_, d0) = time(&covered);
    assert!(d0 == Some(Derivation::Verified));
    let (_, d1) = time(&stopped);
    assert!(d1 == Some(Derivation::Unsupported));
    let best = |src: &[u32]| (0..3).map(|_| time(src).0).min().unwrap_or_default();
    let with = best(&covered);
    let without = best(&stopped);
    println!(
        "covered, checked to the end: {with:?}; same size, check stopped at once: {without:?}"
    );
}
