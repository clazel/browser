//! Basic URL parser conformance (docs/phases/phase-1.md item 1.10).
//!
//! The proofs show the implementation equals `url/spec.rs`, and
//! `url/independent.rs` shows where the spec equals RFC 3986. This file
//! checks both against the outside world:
//!
//! 1. Every row of WPT `url/resources/urltestdata.json`, converted by
//!    `cargo xtask testdata` (`tests/data/wpt-urltestdata/SOURCE.md`). A
//!    row is `new URL(input, base)`: the base is parsed first (a base that
//!    fails makes the row a failure), then the input against it, and the
//!    ten getters `href` to `hash` are compared with the row. The unit is a
//!    row: it passes only if all ten match (or both fail).
//! 2. A differential test against rust-url 2.5.8 (the `url` crate, used
//!    by Servo), on 200,000 random URL-like strings with and without a
//!    base, comparing the href or failure. Two rules newer than rust-url
//!    (U+005E in the path percent-encode set, "%20" before "?" or "#" in
//!    an opaque path) are adjusted for in `ours`. Every other mismatch must
//!    fall in one of the [`Divergence`] classes, each a place where
//!    rust-url contradicts a named step of the standard (several also
//!    contradict a WPT row we pass); the test prints how many fell in each,
//!    and fails on any other.
//!
//! The parser under test is `basic_url_parser`, whose host and file host
//! states run `host_parser_full`, so `clazel-idna`'s domain parser (UTS #46
//! ToASCII) handles every non-ASCII domain.

use clazel_url::host::record::ParsedHost;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::{ParsedPath, ParsedUrl};
use clazel_url::url::serialize::url_path_serializer;

/// The ten getters a row compares.
struct Expected {
    href: &'static str,
    protocol: &'static str,
    username: &'static str,
    password: &'static str,
    host: &'static str,
    hostname: &'static str,
    port: &'static str,
    pathname: &'static str,
    search: &'static str,
    hash: &'static str,
}

/// One converted WPT row.
struct Case {
    name: &'static str,
    input: &'static str,
    base: Option<&'static str>,
    /// `None` for failure.
    expected: Option<Expected>,
}

// `const URLTESTDATA: &[Case]`, generated from the vendored WPT file.
include!("generated/wpt_urltestdata.rs");

/// Rows that fail for a reason outside the parser, by name. None today.
const EXPECTED_FAILURES: &[&str] = &[];

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn string(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

/// The URL API's getters (URL §6.1), from the URL record.
struct Getters {
    href: String,
    protocol: String,
    username: String,
    password: String,
    host: String,
    hostname: String,
    port: String,
    pathname: String,
    search: String,
    hash: String,
}

fn getters(url: &ParsedUrl) -> Getters {
    let hostname = url
        .host
        .as_ref()
        .map(|h: &ParsedHost| string(&h.serialize()))
        .unwrap_or_default();
    let port = url.port.map(|p| p.to_string()).unwrap_or_default();
    let host = match (&url.host, url.port) {
        (None, _) => String::new(),
        (Some(_), None) => hostname.clone(),
        (Some(_), Some(p)) => format!("{hostname}:{p}"),
    };
    let prefixed = |prefix: char, v: &Option<Vec<u32>>| match v {
        Some(v) if !v.is_empty() => format!("{prefix}{}", string(v)),
        _ => String::new(),
    };
    Getters {
        href: string(&url.serialize(false)),
        protocol: format!("{}:", string(&url.scheme)),
        username: string(&url.username),
        password: string(&url.password),
        host,
        hostname,
        port,
        pathname: string(&url_path_serializer(&url.path)),
        search: prefixed('?', &url.query),
        hash: prefixed('#', &url.fragment),
    }
}

/// `new URL(input, base)`: `None` if it throws.
fn new_url(input: &str, base: Option<&str>) -> Option<ParsedUrl> {
    let base = match base {
        Some(b) => Some(basic_url_parser(&scalars(b), None)?),
        None => None,
    };
    basic_url_parser(&scalars(input), base.as_ref())
}

/// The differences between `got` and `expected`, field by field.
fn differences(got: &Getters, e: &Expected) -> Vec<String> {
    let pairs = [
        ("href", &got.href, e.href),
        ("protocol", &got.protocol, e.protocol),
        ("username", &got.username, e.username),
        ("password", &got.password, e.password),
        ("host", &got.host, e.host),
        ("hostname", &got.hostname, e.hostname),
        ("port", &got.port, e.port),
        ("pathname", &got.pathname, e.pathname),
        ("search", &got.search, e.search),
        ("hash", &got.hash, e.hash),
    ];
    pairs
        .iter()
        .filter(|(_, g, w)| g.as_str() != *w)
        .map(|(f, g, w)| format!("{f}: got {g:?}, expected {w:?}"))
        .collect()
}

/// The WPT rows a run checks: every row, or under Miri every 4th (parsing
/// each URL there is slow, and the native run checks them all).
fn rows() -> impl Iterator<Item = &'static Case> {
    URLTESTDATA.iter().step_by(if cfg!(miri) { 4 } else { 1 })
}

#[test]
fn wpt_urltestdata() {
    let mut failures = Vec::new();
    let mut passed = 0usize;
    let mut expected_failures = 0usize;
    let checked = rows().count();
    for case in rows() {
        let got = new_url(case.input, case.base);
        let problem = match (&got, &case.expected) {
            (None, None) => None,
            (Some(u), None) => Some(format!("expected failure, got {:?}", getters(u).href)),
            (None, Some(e)) => Some(format!("failed, expected {:?}", e.href)),
            (Some(u), Some(e)) => {
                let d = differences(&getters(u), e);
                if d.is_empty() {
                    None
                } else {
                    Some(d.join("; "))
                }
            }
        };
        match problem {
            None => passed = passed.saturating_add(1),
            Some(_) if EXPECTED_FAILURES.contains(&case.name) => {
                expected_failures = expected_failures.saturating_add(1);
            }
            Some(p) => failures.push(format!("{}: {p}", case.name)),
        }
    }
    for name in EXPECTED_FAILURES {
        if !URLTESTDATA.iter().any(|c| c.name == *name) {
            failures.push(format!(
                "EXPECTED_FAILURES lists {name:?}, which is no such row"
            ));
        }
    }
    // Summary line for the README table (unit: a row); format in
    // xtask/src/conformance.rs.
    println!(
        "clazel-conformance: suite=\"WPT url/ urltestdata.json\" pass={passed} xfail={expected_failures} fail={} total={checked}",
        checked
            .saturating_sub(passed)
            .saturating_sub(expected_failures),
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// URL §4.5 / Goals: "a non-failure result of a parse-then-serialize
/// operation will not change with any further parse-then-serialize
/// operations applied to it". Checked on every WPT row that parses and on
/// the differential test's random inputs: parsing the href again (without
/// a base) gives the same href. (`url/lemmas.rs` proves this for a class
/// of URLs; this is the evidence for the rest.)
fn reparses_to_itself(input: &str, base: Option<&str>) -> Result<(), String> {
    let Some(u) = new_url(input, base) else {
        return Ok(());
    };
    let href = string(&u.serialize(false));
    match new_url(&href, None) {
        Some(again) if string(&again.serialize(false)) == href => Ok(()),
        Some(again) => Err(format!(
            "{input:?} against {base:?}: {href:?} reparses as {:?}",
            string(&again.serialize(false))
        )),
        None => Err(format!(
            "{input:?} against {base:?}: {href:?} does not reparse"
        )),
    }
}

#[test]
fn idempotence() {
    let mut failures = Vec::new();
    for case in rows() {
        if let Err(e) = reparses_to_itself(case.input, case.base) {
            failures.push(e);
        }
    }
    let mut rng = Lcg(11);
    for _ in 0..samples(200_000, 75) {
        let input = random_input(&mut rng);
        let n = u64::try_from(BASES.len()).unwrap_or(1);
        let base = BASES.get(rng.below(n)).copied().flatten();
        if let Err(e) = reparses_to_itself(&input, base) {
            failures.push(e);
        }
    }
    let shown: Vec<&String> = failures.iter().take(40).collect();
    assert!(
        failures.is_empty(),
        "{} failures:\n{:#?}",
        failures.len(),
        shown
    );
}

/// The path of a parsed URL is opaque exactly when rust-url says it
/// "cannot be a base".
fn opaque(url: &ParsedUrl) -> bool {
    matches!(url.path, ParsedPath::Opaque(_))
}

#[test]
fn opaque_paths() {
    let u = new_url("mailto:x@example.com", None);
    assert!(u.as_ref().is_some_and(opaque));
    let u = new_url("http://example.com/", None);
    assert!(u.as_ref().is_some_and(|u| !opaque(u)));
}

// ---------------------------------------------------------------------
// Differential test against rust-url.
// ---------------------------------------------------------------------

/// A small deterministic generator (64-bit LCG, Knuth's constants).
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 16
    }

    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }

    fn pick<'a>(&mut self, from: &[&'a str]) -> &'a str {
        let n = u64::try_from(from.len()).unwrap_or(1);
        from.get(self.below(n)).copied().unwrap_or("")
    }
}

fn samples(full: u64, miri: u64) -> u64 {
    if cfg!(miri) { miri } else { full }
}

/// Pieces that random inputs are made of: every delimiter the parser
/// switches on, dot segments (plain and percent-encoded), Windows drive
/// letters, IP addresses, ports at the 16-bit edge, credentials, C0
/// controls, spaces, tabs, and a few non-ASCII code points (one that
/// IDNA maps, one it rejects in a host, and one outside the BMP).
const SCHEMES: &[&str] = &[
    "http:",
    "https:",
    "HTTP:",
    "ws:",
    "wss:",
    "ftp:",
    "file:",
    "FILE:",
    "sc:",
    "web+demo:",
    "a1-.+:",
    "",
    "1a:",
    "mailto:",
    "javascript:",
];
const PIECES: &[&str] = &[
    "/",
    "//",
    "\\",
    "?",
    "#",
    "@",
    ":",
    "[",
    "]",
    "%",
    "%2e",
    "%2E",
    ".",
    "..",
    "%2e.",
    ".%2E",
    " ",
    "\t",
    "\n",
    "\u{0}",
    "\u{1f}",
    "a",
    "B",
    "z9",
    "example.com",
    "EXAMPLE.org",
    "localhost",
    "C|",
    "c:",
    "1.2.3.4",
    "0x7f.1",
    "256.0.0.1",
    "[::1]",
    "[1:2::3:4]",
    "80",
    "443",
    "65535",
    "65536",
    "user",
    "pa:ss",
    "%40",
    "^",
    "|",
    "~",
    "'",
    "\"",
    "<",
    ">",
    "`",
    "{",
    "}",
    "ß",
    "ñ",
    "\u{fffd}",
    "\u{1f600}",
    "-",
    "_",
];
const BASES: &[Option<&str>] = &[
    None,
    Some("http://example.org/foo/bar?q#f"),
    Some("https://u:p@h.example:8080/a/b/c"),
    Some("file:///C:/dir/file"),
    Some("file://host/share/x"),
    Some("sc://h/a/b"),
    Some("sc:/a/b"),
    Some("sc:opaque?q"),
    Some("mailto:x@example.com"),
];

/// A random URL-like string.
fn random_input(rng: &mut Lcg) -> String {
    let mut s = String::new();
    if rng.below(4) != 0 {
        s.push_str(rng.pick(SCHEMES));
    }
    let n = rng.below(10).saturating_add(1);
    for _ in 0..n {
        s.push_str(rng.pick(PIECES));
    }
    s
}

/// rust-url's result: the href, or `None` for failure.
fn theirs(input: &str, base: Option<&str>) -> Option<String> {
    let base = match base {
        Some(b) => Some(url::Url::parse(b).ok()?),
        None => None,
    };
    url::Url::options()
        .base_url(base.as_ref())
        .parse(input)
        .ok()
        .map(|u| u.as_str().to_owned())
}

/// `s` with every `from` replaced by `to`.
fn replace(s: &[u32], from: &[u32], to: &[u32]) -> Vec<u32> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < s.len() {
        if s.get(i..).is_some_and(|t| t.starts_with(from)) {
            out.extend_from_slice(to);
            i = i.saturating_add(from.len());
        } else {
            out.extend(s.get(i).copied());
            i = i.saturating_add(1);
        }
    }
    out
}

/// Ours: the href, or `None` for failure, adjusted for the two places
/// where rust-url 2.5.8 is older than the standard (both asserted below):
/// - the path percent-encode set gained U+005E (^) in whatwg/url
///   `9bc33c39` (March 2025), so a path segment's "%5E" (which only an
///   encoded "^" produces from the generator's pieces) is written "^";
/// - opaque path state step 3.2 (a U+0020 SPACE before "?" or "#" is
///   "%20") is newer than rust-url, so a trailing "%20" of an opaque path
///   is written " ".
fn ours(input: &str, base: Option<&str>) -> Option<String> {
    let mut u = new_url(input, base)?;
    match &mut u.path {
        ParsedPath::List(l) => {
            for seg in l.iter_mut() {
                *seg = replace(seg, &[0x25, 0x35, 0x45], &[0x5E]);
            }
        }
        ParsedPath::Opaque(o) => {
            if o.ends_with(&[0x25, 0x32, 0x30]) {
                o.truncate(o.len().saturating_sub(3));
                o.push(0x20);
            }
        }
    }
    Some(string(&u.serialize(false)))
}

/// The input after basic URL parser steps 1 to 3.
fn prepared(input: &str) -> String {
    input
        .trim_matches(|c: char| c <= ' ')
        .chars()
        .filter(|c| !matches!(c, '\t' | '\n' | '\r'))
        .collect()
}

/// The scheme the parser ends up with: the input's, if it starts with one,
/// otherwise base's.
fn effective_scheme(p: &str, base: Option<&str>) -> String {
    let scheme: String = p
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || matches!(c, '+' | '-' | '.'))
        .collect();
    let starts_alpha = scheme
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic());
    if starts_alpha && p.get(scheme.len()..).is_some_and(|r| r.starts_with(':')) {
        scheme.to_ascii_lowercase()
    } else {
        base.and_then(|b| b.split(':').next())
            .unwrap_or("")
            .to_owned()
    }
}

fn is_special_scheme(s: &str) -> bool {
    matches!(s, "ftp" | "file" | "http" | "https" | "ws" | "wss")
}

/// `s` with runs of U+002F (/) after "scheme://" collapsed to one.
fn collapse_slashes(s: &str) -> String {
    let (head, rest) = match s.find("://") {
        Some(k) => s.split_at(k.saturating_add(3)),
        None => return s.to_owned(),
    };
    let mut out = head.to_owned();
    let mut last_slash = false;
    for c in rest.chars() {
        if !(c == '/' && last_slash) {
            out.push(c);
        }
        last_slash = c == '/';
    }
    out
}

/// The places where rust-url 2.5.8 does something the standard's text does
/// not say, each named with the step it contradicts (and a WPT
/// `urltestdata.json` row that agrees with us, where there is one). A
/// mismatch outside them fails the test.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Divergence {
    /// The input starts with a run of U+002F (/) and U+005C (\\) that holds
    /// a U+005C, against a non-special base: rust-url treats those U+005C
    /// as U+002F, which the relative and relative slash states do only if
    /// url is special. These inputs are counted, not compared.
    BackslashNonSpecial,
    /// Port state step 3: in a non-special URL, U+005C (\\) after the ":"
    /// and digits of a port is port-invalid, failure; rust-url starts the
    /// path there.
    BackslashAfterNonSpecialPort,
    /// Authority state step 2.1: "@" followed by an empty host is
    /// host-missing, failure; rust-url accepts it in non-special URLs.
    AtSignWithoutHost,
    /// Special authority ignore slashes state: any number of slashes may
    /// precede a special relative URL's authority (WPT "///test" against
    /// "http://example.org/" is "http://test/"); rust-url fails with
    /// EmptyHost.
    IgnoredSlashes,
    /// Path state keeps empty segments in a file URL's path (WPT
    /// "////one/two" against "file:///" is "file:////one/two"); rust-url
    /// drops them. Checked by collapsing runs of slashes in both.
    FileEmptySegments,
    /// Path state step 1.4.1 only rewrites a segment that is exactly a
    /// Windows drive letter; rust-url also splits "c:" off a longer first
    /// segment of a file URL.
    FileDriveLetterPrefix,
    /// Path state step 1.4.1 replaces the "|" of a file URL's first
    /// segment that is a Windows drive letter with ":"; rust-url keeps
    /// "|" in some positions.
    FileDriveLetterPipe,
    /// File state step 4.1 copies base's host before step 4.4.3 resets the
    /// path for a Windows drive letter (WPT "C|" against
    /// "file://host/dir/file" is "file://host/C:"); rust-url empties it.
    FileDriveLetterKeepsBaseHost,
}

/// Which divergence explains `ours` != `theirs`, if any.
fn divergence(
    input: &str,
    base: Option<&str>,
    ours_href: Option<&str>,
    theirs_href: Option<&str>,
) -> Option<Divergence> {
    let p = prepared(input);
    let scheme = effective_scheme(&p, base);
    let special = is_special_scheme(&scheme);
    let leading: String = p.chars().take_while(|c| matches!(c, '/' | '\\')).collect();
    if !special && leading.contains('\\') {
        return Some(Divergence::BackslashNonSpecial);
    }
    let (Some(o), Some(t)) = (ours_href, theirs_href) else {
        if ours_href.is_none() && !special {
            let after_port = p.char_indices().any(|(k, c)| {
                c == ':' && {
                    let digits: String = p
                        .get(k.saturating_add(1)..)
                        .unwrap_or("")
                        .chars()
                        .take_while(char::is_ascii_digit)
                        .collect();
                    p.get(k.saturating_add(1).saturating_add(digits.len())..)
                        .is_some_and(|r| r.starts_with('\\'))
                }
            });
            if after_port {
                return Some(Divergence::BackslashAfterNonSpecialPort);
            }
            if p.contains("//@") || p.contains(":@") {
                return Some(Divergence::AtSignWithoutHost);
            }
        }
        let slashes = p.chars().take_while(|c| matches!(c, '/' | '\\')).count();
        if theirs_href.is_none() && special && slashes >= 3 {
            return Some(Divergence::IgnoredSlashes);
        }
        return None;
    };
    if !o.starts_with("file:") {
        return None;
    }
    if collapse_slashes(o) == collapse_slashes(t) {
        return Some(Divergence::FileEmptySegments);
    }
    if let Some(rest) = o.strip_prefix("file:///")
        && rest.len() > 2
        && rest.as_bytes().get(1) == Some(&b':')
        && t == format!(
            "file:///{}/{}",
            rest.get(..2).unwrap_or(""),
            rest.get(2..).unwrap_or("")
        )
    {
        return Some(Divergence::FileDriveLetterPrefix);
    }
    if o.replacen(':', "|", 2).replacen("file|", "file:", 1) == t {
        return Some(Divergence::FileDriveLetterPipe);
    }
    if base.is_some_and(|b| b.starts_with("file://host/"))
        && o.strip_prefix("file://host/")
            .map(|r| format!("file:///{r}"))
            .as_deref()
            == Some(t)
    {
        return Some(Divergence::FileDriveLetterKeepsBaseHost);
    }
    None
}

#[test]
fn differential_rust_url() {
    let mut rng = Lcg(7);
    let mut unexplained = Vec::new();
    let mut explained: std::collections::BTreeMap<Divergence, usize> =
        std::collections::BTreeMap::new();
    let mut agree = 0usize;
    for _ in 0..samples(200_000, 75) {
        let input = random_input(&mut rng);
        let n = u64::try_from(BASES.len()).unwrap_or(1);
        let base = BASES.get(rng.below(n)).copied().flatten();
        let (a, b) = (ours(&input, base), theirs(&input, base));
        if a == b {
            agree = agree.saturating_add(1);
        } else if let Some(d) = divergence(&input, base, a.as_deref(), b.as_deref()) {
            let count = explained.entry(d).or_insert(0);
            *count = count.saturating_add(1);
        } else {
            unexplained.push(format!(
                "{input:?} against {base:?}: ours {a:?}, rust-url {b:?}"
            ));
        }
    }
    println!("rust-url agrees on {agree} inputs; known divergences: {explained:?}");
    let shown: Vec<&String> = unexplained.iter().take(40).collect();
    assert!(
        unexplained.is_empty(),
        "{} unexplained mismatches:\n{:#?}",
        unexplained.len(),
        shown
    );
}
