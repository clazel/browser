//! Navigation with the real URL parser (docs/phases/phase-2.md item 2.13).
//!
//! The proofs show the exec kernel with `exec::real_urls::RealUrls` equals
//! the spec over `urls::real_urls()`; this file checks that spec against
//! WPT `url/resources/urltestdata.json` (vendored with `clazel-url`,
//! `tests/data/wpt-urltestdata/`), through the proven code:
//!
//! 1. **Navigation, rows with a base.** For each row with a base, the
//!    kernel opens a tab on the base (an `OpenTab`, so the kernel parses
//!    it), and the renderer sends `Navigate` with the row's input, as UTF-8.
//!    The kernel must commit exactly the row's `href` (a `Commit` carrying
//!    its UTF-8 bytes, to the same renderer or to a spawned one), or, for a
//!    row that expects failure, answer `Error { code: 3 }` (bad URL) and
//!    commit nothing. A base the kernel refuses to open can only be one that
//!    does not parse, and the row must then expect failure. One unit is
//!    one row.
//! 2. **`origin_of` and `path_of`, rows without a base.** `origin_of` of the
//!    input has the serialization of the row's `origin` (`"null"` for an
//!    opaque one) and `path_of` is the row's `pathname` as octets; a row that
//!    expects failure has no origin and the empty path. One unit is one row;
//!    a row without an `origin` field checks `path_of` (and `origin_of`
//!    being `Some`) only.
//! 3. **The guards never fire.** `RealUrls::resolve` is `None` only when the
//!    parser fails (the scalar-value guard on its result is never what
//!    refuses), and `path_of` is ASCII, on every input and base of the WPT
//!    file and on random inputs of the kind the parser finds hard (non-
//!    ASCII, controls, percent signs, brackets). The spec guards these
//!    properties of the parser instead of proving them (`src/urls.rs`);
//!    this is the evidence they are vacuous. One unit is one input.
//!
//! Prints one `clazel-conformance:` line per suite (format in
//! `xtask/src/conformance.rs`). Under Miri, every 29th row and 50 random
//! inputs are run.

mod support;

use clazel_fetch::transducer::types::InputBuf;
use clazel_kernel::exec::records::EventRecord;

use clazel_ipc::message::codec::Msg;
use clazel_kernel::exec::real_urls::RealUrls;
use clazel_kernel::exec::urls::UrlFnsExec;
use clazel_origin::exec::serialization_of_origin_exec;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::serialize::url_path_serializer;
use support::{Kernel, Out, code_points};

/// Answer the network outputs among `out` as a server with an empty page
/// would: `Connected` for a `Connect`, a whole response for a `Send`, nothing
/// for a `Close`. The outputs for renderers, in order, with those that
/// answering gave after them (the document's script is the empty body).
fn settled(kernel: &mut Kernel, out: Vec<Out>) -> Vec<Out> {
    let response = b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\nConnection: close\r\n\r\n".to_vec();
    let mut all = Vec::new();
    let mut queue: std::collections::VecDeque<Out> = out.into();
    while let Some(o) = queue.pop_front() {
        let answer = match o {
            Out::Connect(conn, ..) => Some((conn, InputBuf::Connected)),
            Out::Send(conn, _) => Some((conn, InputBuf::Bytes(response.clone()))),
            Out::Close(_) => None,
            other => {
                all.push(other);
                None
            }
        };
        if let Some((conn, input)) = answer {
            queue.extend(kernel.event(&EventRecord::Net { conn, input }));
        }
    }
    all
}

const URLTESTDATA: &str =
    include_str!("../../clazel-url/tests/data/wpt-urltestdata/urltestdata.json");

// ---------------------------------------------------------------------
// A small JSON reader (the file is ours to parse; no dependency).
// ---------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Json {
    Null,
    Bool(bool),
    Number,
    Str(String),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

struct Reader<'a> {
    chars: Vec<char>,
    at: usize,
    _text: &'a str,
}

impl<'a> Reader<'a> {
    fn new(text: &'a str) -> Self {
        Reader {
            chars: text.chars().collect(),
            at: 0,
            _text: text,
        }
    }
    fn peek(&self) -> Option<char> {
        self.chars.get(self.at).copied()
    }
    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        self.at = self.at.saturating_add(1);
        c
    }
    fn skip_space(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.at = self.at.saturating_add(1);
        }
    }
    fn hex4(&mut self) -> Option<u32> {
        let mut v = 0u32;
        for _ in 0..4 {
            v = v.checked_mul(16)?.checked_add(self.bump()?.to_digit(16)?)?;
        }
        Some(v)
    }
    fn string(&mut self) -> Option<String> {
        if self.bump()? != '"' {
            return None;
        }
        let mut out = String::new();
        loop {
            match self.bump()? {
                '"' => return Some(out),
                '\\' => match self.bump()? {
                    'n' => out.push('\n'),
                    't' => out.push('\t'),
                    'r' => out.push('\r'),
                    'b' => out.push('\u{8}'),
                    'f' => out.push('\u{c}'),
                    'u' => {
                        let hi = self.hex4()?;
                        if (0xD800..0xDC00).contains(&hi)
                            && self.peek() == Some('\\')
                            && self.chars.get(self.at.saturating_add(1)) == Some(&'u')
                        {
                            let save = self.at;
                            self.at = self.at.saturating_add(2);
                            let lo = self.hex4()?;
                            if (0xDC00..0xE000).contains(&lo) {
                                let cp = 0x10000u32
                                    .checked_add(hi.checked_sub(0xD800)?.checked_mul(0x400)?)?
                                    .checked_add(lo.checked_sub(0xDC00)?)?;
                                out.push(char::from_u32(cp)?);
                                continue;
                            }
                            self.at = save;
                        }
                        // A lone surrogate is U+FFFD, as the URL API's USVString conversion makes it.
                        out.push(char::from_u32(hi).unwrap_or(char::REPLACEMENT_CHARACTER));
                    }
                    other => out.push(other),
                },
                c => out.push(c),
            }
        }
    }
    fn value(&mut self) -> Option<Json> {
        self.skip_space();
        match self.peek()? {
            '"' => Some(Json::Str(self.string()?)),
            '[' => {
                self.bump();
                let mut items = Vec::new();
                loop {
                    self.skip_space();
                    if self.peek()? == ']' {
                        self.bump();
                        return Some(Json::Array(items));
                    }
                    items.push(self.value()?);
                    self.skip_space();
                    if self.peek()? == ',' {
                        self.bump();
                    }
                }
            }
            '{' => {
                self.bump();
                let mut items = Vec::new();
                loop {
                    self.skip_space();
                    if self.peek()? == '}' {
                        self.bump();
                        return Some(Json::Object(items));
                    }
                    let key = self.string()?;
                    self.skip_space();
                    if self.bump()? != ':' {
                        return None;
                    }
                    items.push((key, self.value()?));
                    self.skip_space();
                    if self.peek()? == ',' {
                        self.bump();
                    }
                }
            }
            't' => {
                self.at = self.at.saturating_add(4);
                Some(Json::Bool(true))
            }
            'f' => {
                self.at = self.at.saturating_add(5);
                Some(Json::Bool(false))
            }
            'n' => {
                self.at = self.at.saturating_add(4);
                Some(Json::Null)
            }
            _ => {
                while self.peek().is_some_and(|c| {
                    c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E' || c.is_ascii_digit()
                }) {
                    self.at = self.at.saturating_add(1);
                }
                Some(Json::Number)
            }
        }
    }
}

fn field<'a>(obj: &'a [(String, Json)], key: &str) -> Option<&'a Json> {
    obj.iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

fn str_field(obj: &[(String, Json)], key: &str) -> Option<String> {
    match field(obj, key)? {
        Json::Str(s) => Some(s.clone()),
        _ => None,
    }
}

/// One row of the file.
#[derive(Clone)]
struct Row {
    input: String,
    base: Option<String>,
    failure: bool,
    href: Option<String>,
    origin: Option<String>,
    pathname: Option<String>,
}

/// Every row (an object with an `input`), thinned under Miri. The file is
/// parsed once per test binary: under Miri the parse costs more than the
/// rows it yields.
fn rows() -> Vec<Row> {
    static ROWS: std::sync::OnceLock<Vec<Row>> = std::sync::OnceLock::new();
    ROWS.get_or_init(parse_rows).clone()
}

fn parse_rows() -> Vec<Row> {
    let mut reader = Reader::new(URLTESTDATA);
    let Some(Json::Array(items)) = reader.value() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for item in &items {
        if let Json::Object(obj) = item
            && let Some(input) = str_field(obj, "input")
        {
            out.push(Row {
                input,
                base: str_field(obj, "base"),
                failure: matches!(field(obj, "failure"), Some(Json::Bool(true))),
                href: str_field(obj, "href"),
                origin: str_field(obj, "origin"),
                pathname: str_field(obj, "pathname"),
            });
        }
    }
    let step = if cfg!(miri) { 29 } else { 1 };
    out.into_iter().step_by(step).collect()
}

fn string(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

/// The `Commit` url a set of outputs carries, if there is exactly one.
fn committed(out: &[Out]) -> Option<&[u8]> {
    let mut found = None;
    for o in out {
        if let Out::Commit(_, support::Doc { url, .. }) = o {
            if found.is_some() {
                return None;
            }
            found = Some(url.as_slice());
        }
    }
    found
}

/// Whether the fetch takes `href`: an `http:` URL without userinfo
/// (`clazel-fetch`; TLS is not carried out).
fn fetched(href: &str) -> bool {
    let Some(rest) = href.strip_prefix("http://") else {
        return false;
    };
    let authority = rest.split(['/', '?', '#']).next().unwrap_or("");
    !authority.contains('@')
}

/// What navigating from `base` to `input` did, or why the row cannot run.
enum Navigation {
    /// The kernel refused to open a tab on the base.
    BaseRefused,
    /// `Error { code: 3 }` and nothing else.
    BadUrl,
    /// `Error { code: 5 }` and nothing else: the fetch does not take the URL
    /// (only `http:` URLs without userinfo are fetched).
    NotFetched,
    /// A commit of these bytes.
    Committed(Vec<u8>),
    /// Anything else.
    Other(String),
}

fn navigate(base: &str, input: &str) -> Navigation {
    let mut kernel = Kernel::new();
    let (Some(id), _) = kernel.open_tab(base, "") else {
        return Navigation::BaseRefused;
    };
    let out = kernel.send(
        id,
        &Msg::Navigate {
            url: input.as_bytes().to_vec(),
        },
    );
    if out == vec![Out::To(id, Msg::Error { code: 3 })] {
        return Navigation::BadUrl;
    }
    if out == vec![Out::To(id, Msg::Error { code: 5 })] {
        return Navigation::NotFetched;
    }
    let out = settled(&mut kernel, out);
    match committed(&out) {
        Some(url) => Navigation::Committed(url.to_vec()),
        None => Navigation::Other(format!("{out:?}")),
    }
}

#[test]
fn wpt_navigation_with_a_base() {
    let rows: Vec<Row> = rows().into_iter().filter(|r| r.base.is_some()).collect();
    let total = rows.len();
    let mut pass = 0usize;
    let mut commits = 0usize;
    let mut failures = Vec::new();
    for r in &rows {
        let base = r.base.as_deref().unwrap_or("");
        let got = navigate(base, &r.input);
        let ok = match (&got, r.failure, &r.href) {
            (Navigation::BaseRefused | Navigation::BadUrl, true, _) => true,
            (Navigation::Committed(url), false, Some(href)) => {
                fetched(href) && url.as_slice() == href.as_bytes()
            }
            (Navigation::NotFetched, false, Some(href)) => !fetched(href),
            _ => false,
        };
        if ok && matches!(got, Navigation::Committed(_)) {
            commits = commits.saturating_add(1);
        }
        if ok {
            pass = pass.saturating_add(1);
        } else {
            let shown = match got {
                Navigation::BaseRefused => "base refused".to_string(),
                Navigation::BadUrl => "bad url".to_string(),
                Navigation::NotFetched => "not fetched".to_string(),
                Navigation::Committed(u) => format!("committed {:?}", String::from_utf8_lossy(&u)),
                Navigation::Other(s) => s,
            };
            failures.push(format!(
                "{:?} against {base:?}: {shown}; want failure={} href={:?}",
                r.input, r.failure, r.href
            ));
        }
    }
    println!(
        "clazel-conformance: suite=\"WPT url/ urltestdata.json navigation (rows with a base)\" pass={pass} xfail=0 fail={} total={total}",
        failures.len()
    );
    println!("{commits} of the {total} rows commit a URL; the rest are refused or not fetched");
    assert!(total > 0, "no rows with a base were read");
    assert!(commits > total / 10, "too few navigations committed");
    assert!(failures.is_empty(), "{failures:#?}");
}

#[test]
fn wpt_origin_of_and_path_of() {
    let rows: Vec<Row> = rows().into_iter().filter(|r| r.base.is_none()).collect();
    let total = rows.len();
    let urls = RealUrls;
    let mut pass = 0usize;
    let mut failures = Vec::new();
    for r in &rows {
        let input = code_points(&r.input);
        let origin = urls.origin_of(&input);
        let path = urls.path_of(&input);
        let ok = if r.failure {
            origin.is_none() && path.is_empty()
        } else {
            let origin_ok = match (&origin, &r.origin) {
                (Some(o), Some(want)) => string(&serialization_of_origin_exec(o)) == *want,
                (Some(_), None) => true,
                (None, _) => false,
            };
            let path_ok = r
                .pathname
                .as_ref()
                .is_some_and(|p| p.as_bytes() == path.as_slice());
            origin_ok && path_ok
        };
        if ok {
            pass = pass.saturating_add(1);
        } else {
            failures.push(format!(
                "{:?}: origin {:?}, path {:?}; want failure={} origin={:?} pathname={:?}",
                r.input,
                origin.map(|o| string(&serialization_of_origin_exec(&o))),
                String::from_utf8_lossy(&path),
                r.failure,
                r.origin,
                r.pathname
            ));
        }
    }
    println!(
        "clazel-conformance: suite=\"WPT url/ urltestdata.json origin_of and path_of (rows without a base)\" pass={pass} xfail=0 fail={} total={total}",
        failures.len()
    );
    assert!(total > 0, "no rows without a base were read");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// A deterministic generator of hard inputs.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next())
            .unwrap_or(0)
            .checked_rem(n)
            .unwrap_or(0)
    }
}

/// A random string of URL-ish pieces and hard characters.
fn fuzz(rng: &mut Rng) -> String {
    const PIECES: &[&str] = &[
        "http://",
        "https://",
        "file:///",
        "ws://",
        "data:",
        "blob:",
        "javascript:",
        "//",
        "/",
        "\\",
        "./",
        "../",
        "?",
        "#",
        "@",
        ":",
        "[",
        "]",
        "%",
        "%41",
        "%zz",
        "a",
        "b.c",
        "example.com",
        "xn--",
        "\u{e9}",
        "\u{3b1}",
        "\u{4e2d}\u{6587}",
        "\u{1f600}",
        "\u{fffd}",
        "\u{0}",
        "\u{1}",
        " ",
        "\t",
        "\n",
        "\u{a0}",
        "\u{ff0e}",
        "1.2.3.4",
        "0x7f",
        "::1",
        "[::1]",
        "8080",
        ";",
        "=",
        "&",
        "\u{202e}",
        "\u{200d}",
        "\u{80}",
        "\u{7f}",
    ];
    let mut s = String::new();
    for _ in 0..rng.below(8).saturating_add(1) {
        s.push_str(PIECES.get(rng.below(PIECES.len())).copied().unwrap_or("a"));
    }
    s
}

#[test]
fn the_guards_never_fire() {
    let mut cases: Vec<(String, Option<String>)> =
        rows().into_iter().map(|r| (r.input, r.base)).collect();
    let mut rng = Rng(0x2013);
    let n: usize = if cfg!(miri) { 50 } else { 2000 };
    for i in 0..n {
        let input = fuzz(&mut rng);
        let base = if i % 3 == 0 {
            None
        } else {
            Some(fuzz(&mut rng))
        };
        let base = base.map(|b| {
            if i % 2 == 0 {
                format!("http://h/{b}")
            } else {
                b
            }
        });
        cases.push((input, base));
    }
    let total = cases.len();
    let urls = RealUrls;
    let mut pass = 0usize;
    let mut failures = Vec::new();
    for (input, base) in &cases {
        let i = code_points(input);
        let absolute = basic_url_parser(&i, None);
        // `resolve` against the base, or against a base of its own when there
        // is none in the case: compare with the parser alone.
        let base_text = base.clone().unwrap_or_else(|| "http://h/p/q".to_string());
        let parsed_base = basic_url_parser(&code_points(&base_text), None);
        let direct = parsed_base
            .as_ref()
            .and_then(|b| basic_url_parser(&i, Some(b)))
            .map(|u| u.serialize(false));
        let through = urls.resolve(&code_points(&base_text), &i);
        let path = urls.path_of(&i);
        let want_path_len = absolute
            .as_ref()
            .map_or(0, |u| url_path_serializer(&u.path).len());
        let path_ascii = absolute
            .as_ref()
            .is_none_or(|u| url_path_serializer(&u.path).iter().all(|c| *c < 0x80));
        if direct == through && path_ascii && path.len() == want_path_len {
            pass = pass.saturating_add(1);
        } else {
            failures.push(format!(
                "{input:?} against {base_text:?}: parser {direct:?}, resolve {through:?}"
            ));
        }
    }
    println!(
        "clazel-conformance: suite=\"scalar and ASCII guards never fire (WPT urltestdata.json and fuzz)\" pass={pass} xfail=0 fail={} total={total}",
        failures.len()
    );
    assert!(failures.is_empty(), "{failures:#?}");
}
