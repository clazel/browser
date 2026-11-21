//! The matcher on hand-written patterns and inputs (ECMA-262 §22.2.2†): each
//! feature of the semantics, with the result a conforming engine gives. Every
//! expected value is what the standard's algorithm yields (several are the
//! worked examples of the standard's own text). The differential against a
//! reference matcher is in `differential.rs`; limits and catastrophic patterns
//! are in `limits.rs`.

use clazel_js_regexp::{CompileError, Flags, Limits, Match, Program, compile, parse};

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn build(pattern: &str, flags: &str) -> Result<Program, String> {
    let f = Flags::parse(&units(flags)).map_err(|e| format!("flags {flags:?}: {e:?}"))?;
    let p = parse(&units(pattern), f).map_err(|e| format!("/{pattern}/{flags}: {e}"))?;
    compile(&p, f).map_err(|e| format!("/{pattern}/{flags}: {e}"))
}

/// The captures of the first match as text (`None` for a group that did not
/// take part), with `lastIndex` 0 and `y` taken from the flags.
fn exec_at(
    pattern: &str,
    flags: &str,
    input: &str,
    start: usize,
) -> Result<Option<Vec<Option<String>>>, String> {
    let prog = build(pattern, flags)?;
    let sticky = flags.contains('y');
    let text = units(input);
    let m = prog
        .exec(&text, start, sticky, &Limits::default(), None)
        .map_err(|e| format!("/{pattern}/{flags} on {input:?}: {e}"))?;
    Ok(m.map(|m| texts(&m, &text)))
}

fn texts(m: &Match, text: &[u16]) -> Vec<Option<String>> {
    m.captures
        .iter()
        .map(|c| c.and_then(|(a, b)| text.get(a..b).map(String::from_utf16_lossy)))
        .collect()
}

fn exec(pattern: &str, flags: &str, input: &str) -> Result<Option<Vec<Option<String>>>, String> {
    exec_at(pattern, flags, input, 0)
}

const N: Option<&str> = None;

/// `(pattern, flags, input, expected)`; `expected` is the whole match and
/// then each group, or `None` for no match.
type Case = (
    &'static str,
    &'static str,
    &'static str,
    Option<&'static [Option<&'static str>]>,
);

fn run(suite: &str, cases: &[Case]) -> Result<(), String> {
    let mut bad = Vec::new();
    for &(pattern, flags, input, want) in cases {
        let got = exec(pattern, flags, input)?;
        let want: Option<Vec<Option<String>>> =
            want.map(|w| w.iter().map(|x| x.map(str::to_string)).collect());
        if got != want {
            bad.push(format!(
                "/{pattern}/{flags}.exec({input:?}): got {got:?}, want {want:?}"
            ));
        }
    }
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={} xfail=0 fail={} total={}",
        cases.len().saturating_sub(bad.len()),
        bad.len(),
        cases.len()
    );
    if bad.is_empty() {
        Ok(())
    } else {
        Err(bad.join("\n"))
    }
}

#[test]
fn literals_alternation_and_quantifiers() -> Result<(), String> {
    run(
        "matcher: literals, alternation, quantifiers",
        &[
            ("abc", "", "xxabcxx", Some(&[Some("abc")])),
            ("abc", "", "ab", None),
            ("", "", "abc", Some(&[Some("")])),
            ("a|ab", "", "abc", Some(&[Some("a")])),
            ("(a)|b", "", "b", Some(&[Some("b"), N])),
            ("(a)|(b)", "", "b", Some(&[Some("b"), N, Some("b")])),
            ("a*", "", "aaa", Some(&[Some("aaa")])),
            ("a*?", "", "aaa", Some(&[Some("")])),
            ("a+?", "", "aaa", Some(&[Some("a")])),
            ("a?", "", "b", Some(&[Some("")])),
            ("a{2,3}", "", "aaaa", Some(&[Some("aaa")])),
            ("a{2,3}?", "", "aaaa", Some(&[Some("aa")])),
            ("a{2}", "", "a", None),
            ("a{2,}", "", "aaaa", Some(&[Some("aaaa")])),
            ("a{0}b", "", "ab", Some(&[Some("b")])),
            ("(?:ab){2}", "", "ababab", Some(&[Some("abab")])),
            ("(?:ab){2,}?", "", "ababab", Some(&[Some("abab")])),
            (
                "(a|ab)(c|bcd)(d*)",
                "",
                "abcd",
                Some(&[Some("abcd"), Some("a"), Some("bcd"), Some("")]),
            ),
            ("a+b", "", "aaab", Some(&[Some("aaab")])),
            ("a+?b", "", "aaab", Some(&[Some("aaab")])),
            ("a*b", "", "aaac", None),
            ("x*y+$", "", "xxyy", Some(&[Some("xxyy")])),
            ("(?:)*", "", "x", Some(&[Some("")])),
            // A brace that is no quantifier (Annex B).
            ("a{", "", "a{", Some(&[Some("a{")])),
            ("a{,5}", "", "a{,5}", Some(&[Some("a{,5}")])),
            ("x{1}", "", "x", Some(&[Some("x")])),
        ],
    )
}

#[test]
fn captures_and_the_empty_check() -> Result<(), String> {
    run(
        "matcher: captures, the empty check",
        &[
            // §22.2.2.3.1† RepeatMatcher's notes: an iteration beyond the
            // least number that matches the empty string fails.
            ("(a*)*", "", "b", Some(&[Some(""), N])),
            ("(a*)+", "", "b", Some(&[Some(""), Some("")])),
            ("(a*)*", "", "aa", Some(&[Some("aa"), Some("aa")])),
            ("(a?)*", "", "aa", Some(&[Some("aa"), Some("a")])),
            ("(?:a?)*?b", "", "aab", Some(&[Some("aab")])),
            // The standard's example: the captures are reset on each iteration.
            (
                "(z)((a+)?(b+)?(c))*",
                "",
                "zaacbbbcac",
                Some(&[
                    Some("zaacbbbcac"),
                    Some("z"),
                    Some("ac"),
                    Some("a"),
                    N,
                    Some("c"),
                ]),
            ),
            ("(?:(a)|b)*", "", "ab", Some(&[Some("ab"), N])),
            ("(?:(a)|(b))+", "", "ab", Some(&[Some("ab"), N, Some("b")])),
            (
                "((a)|(b))*?c",
                "",
                "abc",
                Some(&[Some("abc"), Some("b"), N, Some("b")]),
            ),
            (
                "(a)(?:(b)|c)\\2",
                "",
                "acb",
                Some(&[Some("ac"), Some("a"), N]),
            ),
            // Backreferences.
            ("(a)\\1", "", "aa", Some(&[Some("aa"), Some("a")])),
            ("(a)\\1", "", "ab", None),
            ("\\1(a)", "", "aa", Some(&[Some("a"), Some("a")])),
            ("(a\\1)", "", "a", Some(&[Some("a"), Some("a")])),
            ("(a)|\\1b", "", "b", Some(&[Some("b"), N])),
            ("(?<x>a)\\k<x>", "", "aa", Some(&[Some("aa"), Some("a")])),
            ("(a)\\2", "", "a\u{2}", Some(&[Some("a\u{2}"), Some("a")])),
            ("\\1", "", "\u{1}", Some(&[Some("\u{1}")])),
            // Duplicate names: the group that took part.
            (
                "(?:(?<x>a)|(?<x>b))\\k<x>",
                "",
                "bb",
                Some(&[Some("bb"), N, Some("b")]),
            ),
            (
                "(?:(?<x>a)|(?<x>b))\\k<x>",
                "",
                "aa",
                Some(&[Some("aa"), Some("a"), N]),
            ),
            ("(?:(?<x>a)|(?<x>b))\\k<x>", "", "ab", None),
        ],
    )
}

#[test]
fn assertions_and_dot() -> Result<(), String> {
    run(
        "matcher: assertions, dot",
        &[
            ("^b", "", "a\nb", None),
            ("^b", "m", "a\nb", Some(&[Some("b")])),
            ("a$", "", "a\nb", None),
            ("a$", "m", "a\nb", Some(&[Some("a")])),
            ("^$", "", "", Some(&[Some("")])),
            ("^$", "m", "a\n\nb", Some(&[Some("")])),
            ("^b", "m", "a\u{2028}b", Some(&[Some("b")])),
            ("^b", "m", "a\u{b}b", None),
            ("\\bfoo\\b", "", "a foo b", Some(&[Some("foo")])),
            ("\\bfoo\\b", "", "afoo b", None),
            ("\\Boo", "", "foo", Some(&[Some("oo")])),
            ("\\b", "", "", None),
            ("\\B", "", "", Some(&[Some("")])),
            ("\\b", "", "-a", Some(&[Some("")])),
            (".", "", "\n", None),
            (".", "s", "\n", Some(&[Some("\n")])),
            (".", "", "\u{2028}", None),
            (".", "", "\r", None),
            (".+", "", "ab\ncd", Some(&[Some("ab")])),
            (".+", "s", "ab\ncd", Some(&[Some("ab\ncd")])),
            ("(?s:.)", "", "\n", Some(&[Some("\n")])),
            ("(?-s:.)", "s", "\n", None),
            ("(?m:^b)", "", "a\nb", Some(&[Some("b")])),
            ("(?-m:^b)", "m", "a\nb", None),
            ("(?m:^b)^", "", "a\nb", None),
        ],
    )
}

#[test]
fn lookaround() -> Result<(), String> {
    run(
        "matcher: lookahead, lookbehind",
        &[
            ("a(?=b)", "", "ab", Some(&[Some("a")])),
            ("a(?!b)", "", "ab", None),
            ("a(?!b)", "", "ac", Some(&[Some("a")])),
            ("(?=(a))\\1", "", "aa", Some(&[Some("a"), Some("a")])),
            ("(?!(a))\\1", "", "b", Some(&[Some(""), N])),
            // The standard's example: no backtracking into a lookahead.
            (
                "(?=(a+))a*b\\1",
                "",
                "baaabac",
                Some(&[Some("aba"), Some("a")]),
            ),
            (
                "(.*?)a(?!(a+)b\\2c)\\2(.*)",
                "",
                "baaabaac",
                Some(&[Some("baaabaac"), Some("ba"), N, Some("abaac")]),
            ),
            ("(?=a)*b", "", "b", Some(&[Some("b")])),
            ("(?<=a)b", "", "ab", Some(&[Some("b")])),
            ("(?<=a)b", "", "cb", None),
            ("(?<!a)b", "", "ab", None),
            ("(?<!a)b", "", "cb", Some(&[Some("b")])),
            ("(?<!a)b", "", "b", Some(&[Some("b")])),
            ("(?<=ab|c)d", "", "abd", Some(&[Some("d")])),
            (
                "(?<=\\$)\\d+(\\.\\d*)?",
                "",
                "cost $10.50",
                Some(&[Some("10.50"), Some(".50")]),
            ),
            // Lookbehind matches backwards: the groups capture right to left.
            (
                "(?<=(\\d+)(\\d+))$",
                "",
                "1053",
                Some(&[Some(""), Some("1"), Some("053")]),
            ),
            (
                "(?<=(\\w){3})f",
                "",
                "abcdef",
                Some(&[Some("f"), Some("c")]),
            ),
            ("(?<=\\1(a))b", "", "aab", Some(&[Some("b"), Some("a")])),
            ("(?<=(a)\\1)b", "", "aab", Some(&[Some("b"), Some("a")])),
            ("(?<=\\b)a", "", "a", Some(&[Some("a")])),
            ("(?<=^a)b", "", "ab", Some(&[Some("b")])),
            ("(?<=(?<=a)b)c", "", "abc", Some(&[Some("c")])),
            ("(?<=a(?=b))b", "", "ab", Some(&[Some("b")])),
            ("(?<!(a))b", "", "cb", Some(&[Some("b"), N])),
            ("(?<=a+)b", "", "aaab", Some(&[Some("b")])),
            ("(?<=a{3})b", "", "aab", None),
            ("(?<=\\p{L})\\d", "u", "é1", Some(&[Some("1")])),
            ("(?<=.)b", "u", "\u{1F600}b", Some(&[Some("b")])),
        ],
    )
}

#[test]
fn classes_and_escapes() -> Result<(), String> {
    run(
        "matcher: classes, escapes",
        &[
            ("[^a]", "", "a", None),
            ("[^a]", "", "ab", Some(&[Some("b")])),
            ("[]", "", "a", None),
            ("[^]", "", "\n", Some(&[Some("\n")])),
            ("[\\d-x]", "", "-", Some(&[Some("-")])),
            ("[a-c]+", "", "abcd", Some(&[Some("abc")])),
            ("[\\w-]+", "", "a-b c", Some(&[Some("a-b")])),
            ("[\\b]", "", "\u{8}", Some(&[Some("\u{8}")])),
            ("\\s", "", "\u{a0}", Some(&[Some("\u{a0}")])),
            ("\\s", "", "\u{feff}", Some(&[Some("\u{feff}")])),
            ("\\s", "", "\u{200b}", None),
            (
                "\\s+",
                "",
                "a \t\n\u{2003}b",
                Some(&[Some(" \t\n\u{2003}")]),
            ),
            ("\\S+", "", "  ab ", Some(&[Some("ab")])),
            ("\\d+", "", "a12b", Some(&[Some("12")])),
            ("\\D+", "", "12ab3", Some(&[Some("ab")])),
            ("\\w+", "", "-ab_1-", Some(&[Some("ab_1")])),
            ("\\W", "", "ab-", Some(&[Some("-")])),
            (
                "\\x41\\u0042\\cJ\\0",
                "",
                "AB\n\u{0}",
                Some(&[Some("AB\n\u{0}")]),
            ),
            ("\\101", "", "A", Some(&[Some("A")])),
            ("[\\x41-\\x43]+", "", "ABCD", Some(&[Some("ABC")])),
            ("[a-z&&[aeiou]]", "", "&]", Some(&[Some("&]")])),
        ],
    )
}

#[test]
fn ignore_case() -> Result<(), String> {
    run(
        "matcher: ignore case",
        &[
            ("abc", "i", "ABC", Some(&[Some("ABC")])),
            ("ABC", "i", "abc", Some(&[Some("abc")])),
            ("[a-z]+", "i", "ABC", Some(&[Some("ABC")])),
            ("[^a-z]", "i", "ABC1", Some(&[Some("1")])),
            ("(a)\\1", "i", "aA", Some(&[Some("aA"), Some("a")])),
            ("(?<=(a))\\1", "i", "aA", Some(&[Some("A"), Some("a")])),
            // Without u: toUpperCase of the code unit, never into or out of ASCII.
            ("\u{e9}", "i", "\u{c9}", Some(&[Some("\u{c9}")])),
            ("\u{3c3}", "i", "\u{3c2}", Some(&[Some("\u{3c2}")])),
            ("\u{212a}", "i", "k", None),
            ("k", "i", "\u{212a}", None),
            ("\u{17f}", "i", "s", None),
            ("s", "i", "\u{17f}", None),
            ("\u{df}", "i", "SS", None),
            ("\\w", "i", "\u{17f}", None),
            ("\\w", "i", "\u{212a}", None),
            ("[\u{17f}]", "i", "S", None),
            // With u: simple case folding.
            ("\u{212a}", "iu", "k", Some(&[Some("k")])),
            ("k", "iu", "\u{212a}", Some(&[Some("\u{212a}")])),
            ("[k]", "iu", "\u{212a}", Some(&[Some("\u{212a}")])),
            ("\u{17f}", "iu", "S", Some(&[Some("S")])),
            ("\u{df}", "iu", "SS", None),
            ("\u{df}", "iu", "\u{1e9e}", Some(&[Some("\u{1e9e}")])),
            ("\\w", "iu", "\u{17f}", Some(&[Some("\u{17f}")])),
            ("\\w", "iu", "\u{212a}", Some(&[Some("\u{212a}")])),
            ("\\W", "iu", "S", None),
            ("\\W", "iu", "\u{17f}", None),
            ("\\bk", "iu", "\u{212a}", Some(&[Some("\u{212a}")])),
            ("\u{10400}", "iu", "\u{10428}", Some(&[Some("\u{10428}")])),
            (
                "[\u{10400}-\u{10410}]",
                "iu",
                "\u{10428}",
                Some(&[Some("\u{10428}")]),
            ),
            ("\u{1c5}", "i", "\u{1c4}", Some(&[Some("\u{1c4}")])),
            ("\u{1c5}", "i", "\u{1c6}", Some(&[Some("\u{1c6}")])),
            ("\\p{Lu}", "iu", "a", Some(&[Some("a")])),
            ("\\p{Lu}", "u", "a", None),
            ("\\p{Ll}", "iu", "A", Some(&[Some("A")])),
            // Without v, a negated escape is complemented before folding: the
            // standard's behaviour, which v fixes.
            ("\\P{Lu}", "iu", "A", Some(&[Some("A")])),
            ("\\P{Lu}", "iv", "A", None),
            ("[^\\P{Lu}]", "iv", "a", Some(&[Some("a")])),
            ("[^\\p{Lu}]", "iv", "a", None),
            ("[^\\p{Lu}]", "iu", "a", None),
            ("\\D", "iu", "5", None),
            ("(?i:a)b", "", "Ab", Some(&[Some("Ab")])),
            ("(?i:a)b", "", "AB", None),
            ("(?-i:a)b", "i", "aB", Some(&[Some("aB")])),
            ("(?-i:a)b", "i", "AB", None),
            ("(?i:[a-b]+)", "", "aBcD", Some(&[Some("aB")])),
        ],
    )
}

#[test]
fn unicode_mode() -> Result<(), String> {
    run(
        "matcher: code points",
        &[
            ("^.$", "u", "\u{1F600}", Some(&[Some("\u{1F600}")])),
            ("^.$", "", "\u{1F600}", None),
            ("^..$", "", "\u{1F600}", Some(&[Some("\u{1F600}")])),
            ("^.$", "v", "\u{1F600}", Some(&[Some("\u{1F600}")])),
            ("\\u{1F600}", "u", "\u{1F600}", Some(&[Some("\u{1F600}")])),
            (
                "\\ud83d\\ude00",
                "u",
                "\u{1F600}",
                Some(&[Some("\u{1F600}")]),
            ),
            ("[\u{1F600}]", "u", "\u{1F600}", Some(&[Some("\u{1F600}")])),
            (
                "[\u{1F600}-\u{1F64F}]+",
                "u",
                "x\u{1F601}\u{1F602}",
                Some(&[Some("\u{1F601}\u{1F602}")]),
            ),
            ("^[^x]$", "u", "\u{1F600}", Some(&[Some("\u{1F600}")])),
            ("^[^x]$", "", "\u{1F600}", None),
            (
                "\u{1F600}+",
                "u",
                "\u{1F600}\u{1F600}",
                Some(&[Some("\u{1F600}\u{1F600}")]),
            ),
            // Without u the quantifier is on the low surrogate alone.
            (
                "\u{1F600}+",
                "",
                "\u{1F600}\u{1F600}",
                Some(&[Some("\u{1F600}")]),
            ),
            // A lone surrogate is not half of a pair with u.
            ("\\ud83d", "u", "\u{1F600}", None),
            ("\\ud83d", "u", "\u{FFFD}", None),
            ("\\ude00", "u", "\u{1F600}", None),
            (
                "(?<=\\ud83d)\\ude00",
                "",
                "\u{1F600}",
                Some(&[Some("\u{FFFD}")]),
            ),
            (
                "(.)\\1",
                "u",
                "\u{1F600}\u{1F600}",
                Some(&[Some("\u{1F600}\u{1F600}"), Some("\u{1F600}")]),
            ),
            (
                "(?<=(.))x",
                "u",
                "\u{1F600}x",
                Some(&[Some("x"), Some("\u{1F600}")]),
            ),
            ("\\b", "u", "\u{1F600}", None),
            (".+?", "u", "\u{1F600}", Some(&[Some("\u{1F600}")])),
            (
                ".{2}",
                "u",
                "\u{1F600}\u{1F601}",
                Some(&[Some("\u{1F600}\u{1F601}")]),
            ),
            (
                "^.{3}$",
                "u",
                "\u{1F600}a\u{1F601}",
                Some(&[Some("\u{1F600}a\u{1F601}")]),
            ),
        ],
    )
}

#[test]
fn property_escapes() -> Result<(), String> {
    run(
        "matcher: property escapes",
        &[
            ("\\p{Lu}", "u", "aBc", Some(&[Some("B")])),
            (
                "\\p{L}+",
                "u",
                "h\u{e9}llo w\u{f6}rld",
                Some(&[Some("h\u{e9}llo")]),
            ),
            ("\\p{Letter}+", "u", "ab1", Some(&[Some("ab")])),
            ("\\p{gc=Nd}", "u", "x\u{663}", Some(&[Some("\u{663}")])),
            (
                "\\p{General_Category=Decimal_Number}",
                "u",
                "x\u{663}",
                Some(&[Some("\u{663}")]),
            ),
            ("\\P{L}", "u", "ab1", Some(&[Some("1")])),
            ("\\p{ASCII}", "u", "\u{e9}a", Some(&[Some("a")])),
            ("\\p{Any}", "u", "\u{1F600}", Some(&[Some("\u{1F600}")])),
            ("\\p{Cn}", "u", "a\u{378}", Some(&[Some("\u{378}")])),
            ("\\p{Assigned}", "u", "\u{378}a", Some(&[Some("a")])),
            ("\\p{Alphabetic}+", "u", "ab1", Some(&[Some("ab")])),
            ("\\p{Alpha}+", "u", "ab1", Some(&[Some("ab")])),
            ("\\p{Emoji}", "u", "a\u{1F600}", Some(&[Some("\u{1F600}")])),
            (
                "\\p{White_Space}",
                "u",
                "a\u{2003}",
                Some(&[Some("\u{2003}")]),
            ),
            ("\\p{Uppercase}", "u", "aB", Some(&[Some("B")])),
            ("\\p{ID_Start}+", "u", "$ab1", Some(&[Some("ab")])),
            ("\\p{Hex_Digit}+", "u", "xfF9g", Some(&[Some("fF9")])),
            ("\\p{Cs}", "u", "a", None),
            ("[\\p{L}\\p{N}]+", "u", "-a1-", Some(&[Some("a1")])),
            ("[^\\p{L}]", "u", "a1", Some(&[Some("1")])),
            ("\\p{Lu}", "v", "aB", Some(&[Some("B")])),
            ("\\p{Sc}", "u", "a$", Some(&[Some("$")])),
            ("\\p{Pd}", "u", "a-", Some(&[Some("-")])),
            ("\\p{Zs}", "u", "a ", Some(&[Some(" ")])),
            ("\\p{Cc}", "u", "a\n", Some(&[Some("\n")])),
            ("\\p{Cased_Letter}+", "u", "aB1", Some(&[Some("aB")])),
        ],
    )
}

#[test]
fn unicode_sets() -> Result<(), String> {
    run(
        "matcher: v-mode class sets",
        &[
            ("[\\p{L}--[a-z]]", "v", "aB", Some(&[Some("B")])),
            ("[[a-z]&&[aeiou]]+", "v", "hello", Some(&[Some("e")])),
            ("[[a-z]--[aeiou]]+", "v", "hello", Some(&[Some("h")])),
            ("[^[a-z]]", "v", "aB", Some(&[Some("B")])),
            ("[\\w--\\d]+", "v", "12ab3", Some(&[Some("ab")])),
            ("[\\q{abc|d}]", "v", "xabc", Some(&[Some("abc")])),
            ("[\\q{abc|ab}]", "v", "abx", Some(&[Some("ab")])),
            ("[\\q{ab|abc}]", "v", "abcx", Some(&[Some("abc")])),
            ("^[\\q{ab|}]$", "v", "", Some(&[Some("")])),
            ("^[\\q{ab|}]$", "v", "ab", Some(&[Some("ab")])),
            ("[\\q{ab}x]+", "v", "xabx", Some(&[Some("xabx")])),
            ("[\\q{a}b]+", "v", "ab", Some(&[Some("ab")])),
            ("[\\q{abc}--\\q{abc}]", "v", "abc", None),
            ("[\\q{ab|cd}&&\\q{cd|ef}]", "v", "abcd", Some(&[Some("cd")])),
            ("[\\q{ab|cd}--\\q{cd}]", "v", "cdab", Some(&[Some("ab")])),
            ("[\\q{ab}]", "iv", "AB", Some(&[Some("AB")])),
            ("(?<=[\\q{ab|c}])d", "v", "abd", Some(&[Some("d")])),
            ("[\\q{ab|c}]d", "v", "abd", Some(&[Some("abd")])),
            ("[[a-c]&&[b-d]]", "v", "abcd", Some(&[Some("b")])),
            ("[[a-c][x-z]]+", "v", "abxy-", Some(&[Some("abxy")])),
        ],
    )
}

#[test]
fn start_index_and_sticky() -> Result<(), String> {
    let some = |p: &str, f: &str, s: &str, at: usize, want: Option<(usize, usize)>| {
        let prog = build(p, f)?;
        let m = prog
            .exec(&units(s), at, f.contains('y'), &Limits::default(), None)
            .map_err(|e| e.to_string())?;
        let got = m.and_then(|m| m.get(0));
        if got == want {
            Ok(())
        } else {
            Err(format!(
                "/{p}/{f} at {at} on {s:?}: got {got:?}, want {want:?}"
            ))
        }
    };
    some("a", "", "aaa", 1, Some((1, 2)))?;
    some("a", "y", "aaa", 1, Some((1, 2)))?;
    some("b", "y", "ab", 0, None)?;
    some("b", "", "ab", 0, Some((1, 2)))?;
    some("b", "y", "ab", 1, Some((1, 2)))?;
    some("^a", "", "aa", 1, None)?;
    some("^a", "m", "a\na", 1, Some((2, 3)))?;
    some("", "", "abc", 3, Some((3, 3)))?;
    some("", "", "abc", 4, None)?;
    some("a", "", "abc", 4, None)?;
    some("(?<=a)b", "y", "ab", 1, Some((1, 2)))?;
    some("\\b", "", "ab cd", 2, Some((2, 2)))?;
    // A start inside a surrogate pair is the pair's start, with u or v; and an
    // unanchored search steps by code points.
    some(".", "uy", "\u{1F600}", 1, Some((0, 2)))?;
    some(".", "y", "\u{1F600}", 1, Some((1, 2)))?;
    some("\\udc00|x", "u", "\u{10000}x", 0, Some((2, 3)))?;
    some("^", "", "\u{1F600}", 1, None)?;
    Ok(())
}

#[test]
fn many_repetitions_in_a_long_input() -> Result<(), String> {
    // A run of one character takes one stack entry, however long. (Under Miri
    // the input is shorter, to keep the test under its time limit.)
    let n: usize = if cfg!(miri) { 300 } else { 100_000 };
    let a = "a".repeat(n);
    let input = format!("{a}b");
    let r = exec("a*b", "", &input)?;
    assert_eq!(r.map(|v| v.len()), Some(1));
    let r = exec("a*a*a*b", "", &input)?;
    assert!(r.is_some());
    let r = exec("[a-z]+?b", "", &input)?;
    assert!(r.is_some());
    let r = exec("(?:a|b)*b", "", &input)?;
    assert!(r.is_some());
    // A large count is a counter, not a copy of the body.
    let r = exec(&format!("a{{{n}}}b"), "", &input)?;
    assert!(r.is_some());
    let r = exec(&format!("(?:a){{{}}}ab", n - 1), "", &input)?;
    assert!(r.is_some());
    // A count beyond the input fails, after trying every start.
    let short = "a".repeat(if cfg!(miri) { 50 } else { 2000 });
    let r = exec("a{4000000000}", "", &short)?;
    assert!(r.is_none());
    Ok(())
}

#[test]
fn named_groups_through_the_api() -> Result<(), String> {
    let prog = build("(?:(?<x>a)|(?<x>b))(?<y>c)?", "")?;
    let text = units("bc");
    let m = prog
        .exec(&text, 0, false, &Limits::default(), None)
        .map_err(|e| e.to_string())?
        .ok_or("no match")?;
    let name = |s: &str| s.chars().map(u32::from).collect::<Vec<_>>();
    assert_eq!(prog.named_capture(&m, &name("x")), Some((0, 1)));
    assert_eq!(prog.named_capture(&m, &name("y")), Some((1, 2)));
    assert_eq!(prog.named_capture(&m, &name("z")), None);
    assert_eq!(prog.capture_count(), 3);
    assert_eq!(prog.group_names().len(), 3);
    assert!(!prog.unicode());
    Ok(())
}

#[test]
fn properties_without_a_table_are_not_compiled() -> Result<(), String> {
    for (p, flags) in [
        ("\\p{Script=Latin}", "u"),
        ("\\p{sc=Latn}", "u"),
        ("\\p{scx=Grek}", "v"),
        ("[\\p{RGI_Emoji}]", "v"),
        ("\\p{Basic_Emoji}", "v"),
    ] {
        let f = Flags::parse(&units(flags)).map_err(|e| format!("{e:?}"))?;
        let pat = parse(&units(p), f).map_err(|e| e.to_string())?;
        match compile(&pat, f) {
            Err(CompileError::UnsupportedProperty(_)) => {}
            other => return Err(format!("/{p}/{flags}: {other:?}")),
        }
    }
    Ok(())
}
