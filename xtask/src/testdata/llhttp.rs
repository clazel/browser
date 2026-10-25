//! `nodejs/llhttp`'s `test/response/*.md`, and the `Content-Length` and
//! `Transfer-Encoding` files of `test/request/*.md`: Node's HTTP parser
//! keeps its tests as markdown, and this reads that fixed shape.
//!
//! Each test is, in this order, with anything else (prose, blank lines)
//! allowed between the parts:
//!
//! ```text
//! ## Name                                  (a heading, `##` or `###`)
//!
//! <!-- meta={"type": "response"} -->       (one line of JSON)
//! ```http                                  (only blank lines between)
//! HTTP/1.1 200 OK
//! ...
//! ```
//!
//! ```log
//! off=0 message begin
//! ...
//! ```
//! ```
//!
//! The `http` block is the input, written the way `test/md-test.ts` reads it:
//! a backslash and a newline join two lines; every newline is then CRLF;
//! then `\r`, `\n`, `\t` and `\f` are the octets they name, replaced one
//! escape after the other in that order, as `md-test.ts` does. The octal,
//! `\x` and `${...}` escapes of that file are not used by the vendored
//! files, and the converter fails if one appears.
//!
//! The `log` block is what llhttp's test parser printed: one event per
//! line, each starting with `off=N ` (the offset in the input). The events
//! are read into a list of messages (their status, version, header fields,
//! and body octets) and how the log ends: with an `error`, or just ends.
//! Every event shape in the files is listed below; a line of any other
//! shape fails the converter, so a change of shape upstream is noticed.
//!
//! The generated table is `const LLHTTP: &[Case]`, whose types the test
//! defines. The converter does no interpretation beyond reading the log;
//! what each outcome means for a client is the test's.

use std::fmt::Write as _;
use std::path::Path;

use serde_json::Value;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "request-content-length.md",
    "request-transfer-encoding.md",
    "response-connection.md",
    "response-content-length.md",
    "response-finish.md",
    "response-invalid.md",
    "response-lenient-version.md",
    "response-pausing.md",
    "response-pipelining.md",
    "response-sample.md",
    "response-transfer-encoding.md",
];

/// What the `log` of one test says about one message.
#[derive(Default)]
struct Msg {
    version: Option<(u8, u8)>,
    /// The status code, 0 for a request (which has a method instead).
    status: u16,
    fields: Vec<(Vec<u8>, Vec<u8>)>,
    body: Vec<u8>,
    headers_done: bool,
    complete: bool,
}

enum End {
    Eof,
    Error { code: u32, reason: String },
}

struct Test {
    id: String,
    name: String,
    ty: String,
    skip_body: bool,
    input: Vec<u8>,
    msgs: Vec<Msg>,
    end: End,
}

/// Rust source for `bytes` as a byte string literal.
fn lit(bytes: &[u8]) -> String {
    format!("b\"{}\"", bytes.escape_ascii())
}

/// The octets of an `http` block, as `md-test.ts` makes them.
fn input_octets(block: &[String], at: &str) -> Result<Vec<u8>, String> {
    let mut text = block.join("\n");
    // `input.replace(/\\(\r\n|\r|\n)/g, '')`: a backslash and a newline.
    text = text.replace("\\\n", "");
    // Every newline is CRLF.
    text = text.replace('\n', "\r\n");
    for (escape, octet) in [("\\r", "\r"), ("\\n", "\n"), ("\\t", "\t"), ("\\f", "\x0c")] {
        text = text.replace(escape, octet);
    }
    if text.contains("${") {
        return Err(format!(
            "{at}: a `${{...}}` escape; the converter does not read it"
        ));
    }
    let b = text.as_bytes();
    for (i, w) in b.windows(2).enumerate() {
        if let [b'\\', next] = w
            && (*next == b'x' || (b'0'..=b'7').contains(next))
        {
            return Err(format!(
                "{at}: a `\\x` or octal escape at octet {i}; the converter does not read it"
            ));
        }
    }
    Ok(b.to_vec())
}

fn number(s: &str, what: &str, at: &str) -> Result<u64, String> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("{at}: {what}: not a number: {s:?}"));
    }
    s.parse().map_err(|e| format!("{at}: {what}: {s:?}: {e}"))
}

/// The payload of `len=N span[KIND]=PAYLOAD`: `lf`, `cr`, or the octets
/// between the quotes (which may hold quotes themselves).
fn span_payload(rest: &str, len: u64, at: &str) -> Result<Vec<u8>, String> {
    let bytes = match rest {
        "lf" => b"\n".to_vec(),
        "cr" => b"\r".to_vec(),
        _ => {
            let inner = rest
                .strip_prefix('"')
                .and_then(|r| r.strip_suffix('"'))
                .ok_or_else(|| format!("{at}: a span payload that is neither lf, cr nor quoted"))?;
            inner.as_bytes().to_vec()
        }
    };
    if bytes.len() as u64 != len {
        return Err(format!(
            "{at}: span of len={len} has a payload of {} octets",
            bytes.len()
        ));
    }
    Ok(bytes)
}

/// `v=A/B`.
fn version(s: &str, at: &str) -> Result<(u8, u8), String> {
    let v = s
        .strip_prefix("v=")
        .and_then(|v| v.split_once('/'))
        .ok_or_else(|| format!("{at}: expected v=A/B, found {s:?}"))?;
    let a = number(v.0, "major", at)?;
    let b = number(v.1, "minor", at)?;
    Ok((
        u8::try_from(a).map_err(|e| format!("{at}: {e}"))?,
        u8::try_from(b).map_err(|e| format!("{at}: {e}"))?,
    ))
}

const SPAN_KINDS: &[&str] = &[
    "protocol",
    "version",
    "status",
    "method",
    "url",
    "header_field",
    "header_value",
    "body",
    "chunk_extension_name",
    "chunk_extension_value",
];

const COMPLETE_KINDS: &[&str] = &[
    "protocol",
    "version",
    "status",
    "method",
    "url",
    "header_field",
    "header_value",
    "chunk_extension_name",
    "chunk_extension_value",
];

fn cur<'a>(msgs: &'a mut [Msg], at: &str, line: &str) -> Result<&'a mut Msg, String> {
    msgs.last_mut()
        .ok_or_else(|| format!("{at}: an event before `message begin`: {line:?}"))
}

/// Read the events of a `log` block.
fn read_log(block: &[String], at: &str) -> Result<(Vec<Msg>, End), String> {
    let mut msgs: Vec<Msg> = Vec::new();
    let mut name: Vec<u8> = Vec::new();
    let mut value: Vec<u8> = Vec::new();
    let mut pending_name: Option<Vec<u8>> = None;
    let mut end = End::Eof;
    for (n, line) in block.iter().enumerate() {
        let at = format!("{at}, log line {}", n.saturating_add(1));
        // As `md-test.ts` does for the expected log: `\t` and `\f` are the
        // octets they name.
        let line = &line.replace("\\t", "\t").replace("\\f", "\x0c");
        let line = line.as_str();
        if matches!(end, End::Error { .. }) {
            return Err(format!("{at}: an event after an error"));
        }
        if line == "off=NULL finish=0" || line == "off=NULL finish=1" || line == "off=NULL finish=2"
        {
            continue;
        }
        let rest = line
            .strip_prefix("off=")
            .and_then(|r| r.split_once(' '))
            .filter(|(o, _)| !o.is_empty() && o.bytes().all(|b| b.is_ascii_digit()))
            .map(|(_, r)| r)
            .ok_or_else(|| format!("{at}: does not start with `off=N `: {line:?}"))?;
        if rest == "message begin" {
            msgs.push(Msg::default());
        } else if rest == "message complete" {
            let m = cur(&mut msgs, &at, line)?;
            m.complete = true;
        } else if let Some(r) = rest.strip_prefix("len=") {
            let (len, r) = r
                .split_once(" span[")
                .ok_or_else(|| format!("{at}: expected `len=N span[...]`: {line:?}"))?;
            let len = number(len, "len", &at)?;
            let (kind, payload) = r
                .split_once("]=")
                .ok_or_else(|| format!("{at}: span without `]=`: {line:?}"))?;
            if !SPAN_KINDS.contains(&kind) {
                return Err(format!("{at}: unknown span kind {kind:?}"));
            }
            let bytes = span_payload(payload, len, &at)?;
            let m = cur(&mut msgs, &at, line)?;
            match kind {
                "header_field" => name.extend(bytes),
                "header_value" => value.extend(bytes),
                "body" => m.body.extend(bytes),
                _ => {}
            }
        } else if rest == "chunk complete"
            || rest == "reset"
            || rest == "pause"
            || rest == "skip body"
        {
            // Events with no part in what a message says.
        } else if let Some(kind) = rest.strip_suffix(" complete") {
            if kind == "headers" {
                return Err(format!("{at}: malformed `headers complete`: {line:?}"));
            }
            if !COMPLETE_KINDS.contains(&kind) {
                return Err(format!("{at}: unknown completion {kind:?}"));
            }
            let m = cur(&mut msgs, &at, line)?;
            match kind {
                "header_field" => pending_name = Some(std::mem::take(&mut name)),
                "header_value" => {
                    let n = pending_name.take().ok_or_else(|| {
                        format!("{at}: header_value complete with no header_field complete")
                    })?;
                    m.fields.push((n, std::mem::take(&mut value)));
                }
                _ => {}
            }
        } else if let Some(r) = rest.strip_prefix("headers complete ") {
            let m = cur(&mut msgs, &at, line)?;
            let parts: Vec<&str> = r.split(' ').collect();
            let [first, v, flags, cl] = parts.as_slice() else {
                return Err(format!("{at}: malformed `headers complete`: {line:?}"));
            };
            if let Some(s) = first.strip_prefix("status=") {
                m.status =
                    u16::try_from(number(s, "status", &at)?).map_err(|e| format!("{at}: {e}"))?;
            } else if let Some(m) = first.strip_prefix("method=") {
                number(m, "method", &at)?;
            } else {
                return Err(format!("{at}: expected status= or method=: {line:?}"));
            }
            m.version = Some(version(v, &at)?);
            let ok = flags
                .strip_prefix("flags=")
                .is_some_and(|f| !f.is_empty() && f.bytes().all(|b| b.is_ascii_hexdigit()));
            if !ok {
                return Err(format!("{at}: expected flags=HEX: {line:?}"));
            }
            number(
                cl.strip_prefix("content_length=")
                    .ok_or_else(|| format!("{at}: expected content_length=N: {line:?}"))?,
                "content_length",
                &at,
            )?;
            m.headers_done = true;
        } else if let Some(r) = rest.strip_prefix("chunk header len=") {
            number(r, "chunk header len", &at)?;
        } else if let Some(r) = rest.strip_prefix("error code=") {
            let (code, reason) = r
                .split_once(" reason=\"")
                .and_then(|(c, rs)| rs.strip_suffix('"').map(|rs| (c, rs)))
                .ok_or_else(|| format!("{at}: malformed `error`: {line:?}"))?;
            end = End::Error {
                code: u32::try_from(number(code, "code", &at)?)
                    .map_err(|e| format!("{at}: {e}"))?,
                reason: reason.to_owned(),
            };
        } else {
            return Err(format!("{at}: an event of an unknown shape: {line:?}"));
        }
    }
    Ok((msgs, end))
}

/// The tests of one markdown file.
fn read_file(label: &str, text: &str) -> Result<Vec<Test>, String> {
    #[derive(PartialEq)]
    enum State {
        Prose,
        MetaSeen,
        InHttp,
        AfterHttp,
        InLog,
    }
    let mut tests: Vec<Test> = Vec::new();
    let mut state = State::Prose;
    let mut heading: Option<(usize, String)> = None;
    let mut cases_under_heading = 0usize;
    let mut meta: Option<Value> = None;
    let mut block: Vec<String> = Vec::new();
    let mut input: Vec<u8> = Vec::new();
    for (index, line) in text.lines().enumerate() {
        let number = index.saturating_add(1);
        let at = format!("{label}:{number}");
        match state {
            State::InHttp | State::InLog => {
                if line == "```" {
                    if state == State::InHttp {
                        input = input_octets(&block, &at)?;
                        state = State::AfterHttp;
                    } else {
                        let (msgs, end) = read_log(&block, &at)?;
                        let (_, h) = heading
                            .clone()
                            .ok_or_else(|| format!("{at}: a test before any heading"))?;
                        let m = meta
                            .take()
                            .ok_or_else(|| format!("{at}: internal: no meta"))?;
                        let obj = m
                            .as_object()
                            .ok_or_else(|| format!("{at}: meta is not an object"))?;
                        for key in obj.keys() {
                            if !["type", "pause", "skipBody", "noScan"].contains(&key.as_str()) {
                                return Err(format!("{at}: unknown meta key {key:?}"));
                            }
                        }
                        let ty = obj
                            .get("type")
                            .and_then(Value::as_str)
                            .ok_or_else(|| format!("{at}: meta has no string \"type\""))?
                            .to_owned();
                        let skip_body = match obj.get("skipBody") {
                            None => false,
                            Some(Value::Bool(b)) => *b,
                            Some(_) => return Err(format!("{at}: skipBody is not a boolean")),
                        };
                        let hl = heading.as_ref().map_or(0, |h| h.0);
                        tests.push(Test {
                            id: format!("{label}:{hl}"),
                            name: h,
                            ty,
                            skip_body,
                            input: std::mem::take(&mut input),
                            msgs,
                            end,
                        });
                        state = State::Prose;
                    }
                    block.clear();
                } else {
                    block.push(line.to_owned());
                }
            }
            State::Prose | State::MetaSeen | State::AfterHttp => {
                if line.starts_with("```") {
                    let lang = line.trim_start_matches('`');
                    match (&state, lang) {
                        (State::MetaSeen, "http") => {
                            state = State::InHttp;
                        }
                        (State::AfterHttp, "log") => state = State::InLog,
                        _ => {
                            return Err(format!(
                                "{at}: a ```{lang} block where the shape has none (in order: heading, meta, http, log)"
                            ));
                        }
                    }
                } else if let Some(m) = line
                    .strip_prefix("<!-- meta=")
                    .and_then(|m| m.strip_suffix("-->"))
                {
                    if state != State::Prose {
                        return Err(format!("{at}: a meta comment before the test is done"));
                    }
                    meta = Some(
                        serde_json::from_str(m.trim())
                            .map_err(|e| format!("{at}: meta is not JSON: {e}"))?,
                    );
                    cases_under_heading = cases_under_heading.saturating_add(1);
                    if cases_under_heading != 1 {
                        return Err(format!(
                            "{at}: more than one test under one heading; ids are heading lines"
                        ));
                    }
                    state = State::MetaSeen;
                } else if line.starts_with('#') {
                    if state != State::Prose {
                        return Err(format!("{at}: a heading inside a test"));
                    }
                    let level = line.bytes().take_while(|&b| b == b'#').count();
                    let title = line.get(level..).unwrap_or("");
                    if !(2..=3).contains(&level) || !title.starts_with(' ') {
                        return Err(format!("{at}: a heading of an unexpected shape: {line:?}"));
                    }
                    heading = Some((number, title.trim().to_owned()));
                    cases_under_heading = 0;
                } else if state == State::MetaSeen && !line.trim().is_empty() {
                    return Err(format!(
                        "{at}: something other than the ```http block after the meta comment"
                    ));
                }
            }
        }
    }
    if state != State::Prose {
        return Err(format!("{label}: ends inside a test"));
    }
    Ok(tests)
}

pub fn convert(dir: &Path) -> Result<String, String> {
    let mut all: Vec<Test> = Vec::new();
    for file in FILES {
        let text = std::fs::read_to_string(dir.join(file)).map_err(|e| format!("{file}: {e}"))?;
        let label = file.replacen('-', "/", 1);
        let tests = read_file(&label, &text)?;
        if tests.is_empty() {
            return Err(format!("{file}: no tests found"));
        }
        all.extend(tests);
    }
    let mut ids: Vec<&str> = all.iter().map(|t| t.id.as_str()).collect();
    ids.sort_unstable();
    if let Some(w) = ids.windows(2).find(|w| w.first() == w.get(1)) {
        return Err(format!("duplicate test id {:?}", w.first()));
    }

    let mut out = String::new();
    out.push_str("// @generated by `cargo xtask testdata` from tests/data/llhttp/.\n");
    out.push_str("// Do not edit: `cargo xtask verify` fails if this differs from what the\n");
    out.push_str("// converter (xtask/src/testdata/llhttp.rs) produces.\n");
    out.push_str("// Source, commit and license: tests/data/llhttp/SOURCE.md.\n");
    out.push_str("const LLHTTP: &[Case] = &[\n");
    for t in &all {
        let mut msgs = String::new();
        for m in &t.msgs {
            let (a, b) = m.version.unwrap_or((0, 0));
            let fields: Vec<String> = m
                .fields
                .iter()
                .map(|(n, v)| format!("({}, {})", lit(n), lit(v)))
                .collect();
            write!(
                msgs,
                "Msg {{ version: ({a}, {b}), status: {}, fields: &[{}], body: {}, headers_done: {}, complete: {} }}, ",
                m.status,
                fields.join(", "),
                lit(&m.body),
                m.headers_done,
                m.complete
            )
            .map_err(|e| e.to_string())?;
        }
        let end = match &t.end {
            End::Eof => "End::Eof".to_owned(),
            End::Error { code, reason } => {
                format!("End::Error {{ code: {code}, reason: {reason:?} }}")
            }
        };
        writeln!(
            out,
            "    Case {{ id: {:?}, name: {:?}, ty: {:?}, skip_body: {}, input: {}, msgs: &[{}], end: {end} }},",
            t.id,
            t.name,
            t.ty,
            t.skip_body,
            lit(&t.input),
            msgs.trim_end()
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::read_file;

    const GOOD: &str = "T\n=\n\n## A test\n\n<!-- meta={\"type\": \"response\"} -->\n```http\nHTTP/1.1 200 OK\nContent-Length: 2\n\nab\\r\\n\n```\n\n```log\noff=0 message begin\noff=0 len=4 span[protocol]=\"HTTP\"\noff=4 protocol complete\noff=17 len=14 span[header_field]=\"Content-Length\"\noff=32 header_field complete\noff=34 len=1 span[header_value]=\"2\"\noff=35 header_value complete\noff=37 headers complete status=200 v=1/1 flags=20 content_length=2\noff=37 len=2 span[body]=\"ab\"\noff=39 len=1 span[body]=cr\noff=40 len=1 span[body]=lf\noff=41 message complete\n```\n";

    #[test]
    fn reads_the_shape() {
        let tests = read_file("response/x.md", GOOD).unwrap_or_default();
        assert_eq!(tests.len(), 1);
        let t = tests.first();
        assert_eq!(t.map(|t| t.id.as_str()), Some("response/x.md:4"));
        assert_eq!(
            t.map(|t| t.input.as_slice()),
            Some(&b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nab\r\n"[..])
        );
        let m = t.and_then(|t| t.msgs.first());
        assert_eq!(m.map(|m| m.status), Some(200));
        assert_eq!(m.map(|m| m.body.as_slice()), Some(&b"ab\r\n"[..]));
        assert_eq!(m.map(|m| m.fields.len()), Some(1));
        assert_eq!(m.map(|m| m.complete), Some(true));
    }

    #[test]
    fn fails_when_the_shape_changes() {
        for (what, bad) in [
            (
                "a new event",
                GOOD.replace("message complete", "message finished"),
            ),
            ("an unknown meta key", GOOD.replace("\"type\"", "\"kind\"")),
            (
                "a span of the wrong length",
                GOOD.replace("len=14", "len=13"),
            ),
            ("a new fence", GOOD.replace("```log", "```text")),
            (
                "a log line with no off=",
                GOOD.replace("off=0 message", "message"),
            ),
            ("an octal escape", GOOD.replace("ab\\r", "\\101\\r")),
            ("no heading", GOOD.replace("## A test", "A test")),
        ] {
            assert!(read_file("response/x.md", &bad).is_err(), "{what}");
        }
    }
}
