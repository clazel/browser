//! HTTP/1.1 message framing conformance (docs/phases/phase-3.md item 3.3).
//!
//! The proofs show the executable parser equals `spec.rs` (a transcription
//! of RFC 9112) on every input. This file checks the spec against the
//! outside world, in seven suites, each printing one `clazel-conformance:`
//! line (`xtask/src/conformance.rs`):
//!
//! 1. `RFC 9112 7.1 and 11 examples`: RFC 9112 has no wire example in §7.1
//!    or §11, so each case is one production of §7.1 (`chunked-body`,
//!    `chunk`, `chunk-size`, `last-chunk`, `chunk-data`), §7.1.1
//!    (`chunk-ext`), §7.1.2 (`trailer-section`), one step of §7.1.3's
//!    decoding, the response-splitting example of §11.1, the smuggling
//!    vectors of §11.2 and the truncation of §11.3, each written out as
//!    bytes with the answer the RFC's words give. Every case also runs
//!    through the incremental parser in pieces.
//! 2. `llhttp test/response and framing cases`: Node's HTTP parser's own
//!    tests (vendored under `tests/data/llhttp/`, converted into
//!    `tests/generated/llhttp.rs`): each input must give what llhttp's log
//!    says it gave (status, version, every field, body, and whether the
//!    message completes, errors or waits). Request-file cases are run as
//!    responses: the request line becomes `HTTP/<version> 200 OK`. Where
//!    llhttp is lenient by design, or a request is not a response, the case
//!    is in [`XFAIL`] with the reason, and is never counted as a pass.
//! 3. `httparse differential: random responses`: random well-formed heads,
//!    compared with what the generator wrote, with `httparse`, and with each
//!    other: status, version, reason, every field (name and value) and the
//!    length of the head.
//! 4. `httparse differential: mutated responses`: the same heads after random
//!    byte flips, insertions, deletions and truncations. Where the two
//!    parsers differ, the input must have one of the features of
//!    [`explain_ours_rejects`], [`explain_ours_accepts`] or the timing rule,
//!    each of which is one of our documented choices (`spec.rs`'s header, or
//!    the ABNF read literally), and the case counts as an expected
//!    difference, never as a pass.
//! 5. `httparse differential: llhttp corpus heads`: the heads of the vendored
//!    corpus, compared the same way.
//! 6. `httparse differential: handcrafted heads`: one input for every
//!    expected difference and every agreement worth stating, each with the
//!    verdict it must get.
//! 7. `framing by construction: random bodies`: messages framed by
//!    `Content-Length`, by the chunked coding (random chunk sizes in either
//!    case with leading zeros, extensions and trailers), by connection close,
//!    and with no body (`HEAD`, 1xx, 204, 304), built from a body known
//!    before it is framed. The expectation never comes from `src/`.
//!    `httparse` reads only the head, so it cannot check framing.
//!
//! The reference engine is `httparse` 1.10.1 (docs/DEPENDENCIES.md).
//! Every random suite uses a fixed seed. Under Miri the random suites run a
//! hundredth of their rounds and the corpus suites every eighth case.

use clazel_http::field::types::FieldLineBuf;
use clazel_http::message::body::{
    HeadExec, ResponseParser, parse_response_at_close_exec, parse_response_exec, read_head_exec,
};
use clazel_http::message::serialize::serialize_request;
use clazel_http::message::types::{ParseBuf, RequestBuf};
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// Utilities.
// ---------------------------------------------------------------------------

/// A small deterministic generator (xorshift), so failures reproduce.
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
    fn chance(&mut self, one_in: usize) -> bool {
        self.below(one_in) == 0
    }
    /// A byte from `lo` to `hi`, both included.
    fn between(&mut self, lo: u8, hi: u8) -> u8 {
        let span = usize::from(hi)
            .saturating_sub(usize::from(lo))
            .saturating_add(1);
        lo.saturating_add(u8::try_from(self.below(span)).unwrap_or(0))
    }
    fn byte(&mut self) -> u8 {
        self.between(0, 255)
    }
    fn pick<T: Copy>(&mut self, xs: &[T], default: T) -> T {
        xs.get(self.below(xs.len())).copied().unwrap_or(default)
    }
}

fn at(b: &[u8], i: usize) -> u8 {
    b.get(i).copied().unwrap_or(0)
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

fn show(b: &[u8]) -> String {
    b.escape_ascii().to_string()
}

/// Rounds of the random suites; Miri (an interpreter, about a thousand
/// times slower) runs a hundredth of them.
const RANDOM_ROUNDS: usize = if cfg!(miri) { 15 } else { 6000 };
const MUTATED_ROUNDS: usize = if cfg!(miri) { 150 } else { 60_000 };
const FRAMING_ROUNDS: usize = if cfg!(miri) { 8 } else { 3000 };
/// The corpus suites run every `CORPUS_STEP`th case.
const CORPUS_STEP: usize = if cfg!(miri) { 32 } else { 1 };

/// Print a suite's summary line, before the caller asserts.
fn summary(suite: &str, pass: usize, xfail: usize, fail: usize, total: usize) {
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
    assert_eq!(pass.saturating_add(xfail).saturating_add(fail), total);
}

fn bump(counts: &mut BTreeMap<String, usize>, key: &str) {
    let n = counts.entry(key.to_owned()).or_insert(0);
    *n = n.saturating_add(1);
}

fn print_counts(title: &str, counts: &BTreeMap<String, usize>) {
    for (k, v) in counts {
        println!("{title}: {k}: {v}");
    }
}

// ---------------------------------------------------------------------------
// The parser, run whole and in pieces.
// ---------------------------------------------------------------------------

/// Is `partial`, the first decided answer when `input[..fed]` had arrived,
/// the answer for all of `input`? (The octets after a message are only
/// those received so far.)
fn same_decision(partial: &ParseBuf, whole: &ParseBuf, input: &[u8], fed: usize) -> bool {
    match (partial, whole) {
        (
            ParseBuf::Done {
                response: a,
                rest: ra,
            },
            ParseBuf::Done {
                response: b,
                rest: rb,
            },
        ) => {
            let mut all = ra.clone();
            all.extend_from_slice(input.get(fed..).unwrap_or(&[]));
            a == b && &all == rb
        }
        (a, b) => a == b,
    }
}

/// Feeds `input` in pieces of `step` octets to the incremental parser. The
/// first decided answer must be the one-shot parse of all of it, and when
/// nothing is decided, closing must give the one-shot answer at close.
fn pieces_agree(input: &[u8], head: bool, step: usize) -> Result<(), String> {
    let whole = parse_response_exec(input, head);
    let mut p = ResponseParser::new(head);
    let mut fed = 0usize;
    for piece in input.chunks(step) {
        fed = fed.saturating_add(piece.len());
        match p.feed(piece) {
            ParseBuf::Incomplete => {
                if whole != ParseBuf::Incomplete && fed == input.len() {
                    return Err(format!(
                        "pieces of {step}: still Incomplete with all of it, one shot gives {whole:?}"
                    ));
                }
            }
            decided => {
                return if same_decision(&decided, &whole, input, fed) {
                    Ok(())
                } else {
                    Err(format!(
                        "pieces of {step}: decided {decided:?} after {fed} octets, one shot gives {whole:?}"
                    ))
                };
            }
        }
    }
    if whole != ParseBuf::Incomplete {
        // Empty input is never fed, so nothing was decided: only possible
        // when the one-shot answer is Incomplete.
        return Err(format!(
            "pieces of {step}: never decided, one shot gives {whole:?}"
        ));
    }
    let closed = p.close();
    let expected = parse_response_at_close_exec(input, head);
    if closed == expected {
        Ok(())
    } else {
        Err(format!(
            "pieces of {step}: at close {closed:?}, one shot at close gives {expected:?}"
        ))
    }
}

/// Pieces of 1, 3 and 16 octets (the incremental parser parses everything
/// received again for each piece, so Miri runs only the largest).
fn pieces_all(input: &[u8], head: bool) -> Result<(), String> {
    let steps: &[usize] = if cfg!(miri) { &[16] } else { &[1, 3, 16] };
    for &step in steps {
        pieces_agree(input, head, step)?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Suite 1: RFC 9112 §7.1 and §11.
// ---------------------------------------------------------------------------

/// What a case must give.
enum Want {
    /// A finished response: status, the number of header fields (trailers
    /// are never among them), content, and the octets after it.
    Done {
        status: u16,
        fields: usize,
        body: Vec<u8>,
        rest: Vec<u8>,
    },
    /// Invalid.
    Invalid,
    /// A transfer coding this client cannot decode.
    Unsupported,
    /// Incomplete, and Invalid when the connection closes.
    Truncated,
    /// Incomplete until the connection closes, then this content.
    CloseDelimited(Vec<u8>),
}

fn done(fields: usize, body: &[u8], rest: &[u8]) -> Want {
    Want::Done {
        status: 200,
        fields,
        body: body.to_vec(),
        rest: rest.to_vec(),
    }
}

/// A 200 response with `fields` (each ending in CRLF) and then `after`.
fn response(fields: &[u8], after: &[u8]) -> Vec<u8> {
    cat(&[b"HTTP/1.1 200 OK\r\n", fields, b"\r\n", after])
}

/// A chunked 200 response whose body is `wire`.
fn chunked(wire: &[u8]) -> Vec<u8> {
    response(b"Transfer-Encoding: chunked\r\n", wire)
}

struct Rfc {
    /// The RFC text the case is from.
    label: &'static str,
    input: Vec<u8>,
    head: bool,
    want: Want,
}

fn rfc_cases() -> Vec<Rfc> {
    let mut v: Vec<Rfc> = Vec::new();
    let mut add = |label: &'static str, input: Vec<u8>, want: Want| {
        v.push(Rfc {
            label,
            input,
            head: false,
            want,
        });
    };
    let head_with = |fields: &[u8]| cat(&[b"HTTP/1.1 200 OK\r\n", fields, b"\r\n"]);

    // ----- 7.1 chunked-body = *chunk last-chunk trailer-section CRLF -----
    add(
        "7.1 chunked-body: no chunk, just last-chunk and the final CRLF",
        chunked(b"0\r\n\r\n"),
        done(1, b"", b""),
    );
    add(
        "7.1 chunked-body: one chunk",
        chunked(b"5\r\nhello\r\n0\r\n\r\n"),
        done(1, b"hello", b""),
    );
    add(
        "7.1 chunked-body: several chunks, one holding CRLF",
        chunked(b"4\r\nWiki\r\n5\r\npedia\r\nE\r\n in\r\n\r\nchunks.\r\n0\r\n\r\n"),
        done(1, b"Wikipedia in\r\n\r\nchunks.", b""),
    );
    add(
        "7.1 chunked-body: the octets after the final CRLF are not the body",
        chunked(b"2\r\nhi\r\n0\r\n\r\nHTTP/1.1 200 OK\r\n\r\n"),
        done(1, b"hi", b"HTTP/1.1 200 OK\r\n\r\n"),
    );
    // ----- 7.1 chunk-size = 1*HEXDIG -----
    add(
        "7.1 chunk-size: lower-case hex digits",
        chunked(b"a\r\n0123456789\r\n0\r\n\r\n"),
        done(1, b"0123456789", b""),
    );
    add(
        "7.1 chunk-size: upper-case hex digits",
        chunked(b"A\r\n0123456789\r\n0\r\n\r\n"),
        done(1, b"0123456789", b""),
    );
    add(
        "7.1 chunk-size: mixed-case, two digits (1a = 26)",
        chunked(b"1a\r\nabcdefghijklmnopqrstuvwxyz\r\n0\r\n\r\n"),
        done(1, b"abcdefghijklmnopqrstuvwxyz", b""),
    );
    add(
        "7.1 chunk-size: leading zeros are digits",
        chunked(b"0005\r\nhello\r\n0\r\n\r\n"),
        done(1, b"hello", b""),
    );
    add(
        "7.1 chunk-size: a hundred leading zeros",
        chunked(&cat(&[&[b'0'; 100], b"5\r\nhello\r\n0\r\n\r\n"])),
        done(1, b"hello", b""),
    );
    add(
        "7.1 chunk-size: not a hex digit",
        chunked(b"g\r\nx\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk-size: a sign is not a digit (+5)",
        chunked(b"+5\r\nhello\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk-size: a sign is not a digit (-0)",
        chunked(b"-0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk-size: no 0x prefix",
        chunked(b"0x5\r\nhello\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk-size: at least one digit",
        chunked(b"\r\nhello\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk-size: no space before it",
        chunked(b" 5\r\nhello\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    // ----- 7.1 "MUST anticipate potentially large hexadecimal numerals" -----
    add(
        "7.1 large numeral: 20 hex digits (2^80 - 1) neither wraps nor panics",
        chunked(b"FFFFFFFFFFFFFFFFFFFF\r\nx"),
        Want::Invalid,
    );
    add(
        "7.1 large numeral: 2^64 - 1",
        chunked(b"FFFFFFFFFFFFFFFF\r\nx"),
        Want::Invalid,
    );
    add(
        "7.1 large numeral: 2^64 (one past a u64)",
        chunked(b"10000000000000000\r\nx"),
        Want::Invalid,
    );
    add(
        "7.1 large numeral: 2^32, which a 32-bit size would wrap to 0",
        chunked(b"100000000\r\nx"),
        Want::Invalid,
    );
    add(
        "7.1 large numeral: 1000 digits",
        chunked(&cat(&[&[b'F'; 1000], b"\r\nx"])),
        Want::Invalid,
    );
    add(
        "7.1 large numeral: just past the body limit (64 MiB + 1), decided at once",
        chunked(b"4000001\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 large numeral: exactly the body limit (64 MiB) waits for the data",
        chunked(b"4000000\r\n"),
        Want::Truncated,
    );
    // ----- 7.1 chunk-data = 1*OCTET, chunk-size octets -----
    add(
        "7.1 chunk-data: longer than chunk-size",
        chunked(b"2\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk-data: shorter than chunk-size",
        chunked(b"5\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk: chunk-data is followed by CRLF",
        chunked(b"1\r\naXY0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk: a bare LF does not end chunk-data",
        chunked(b"1\r\na\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk: a bare LF does not end the chunk-size line",
        chunked(b"1\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunk-data may hold any octet, NUL and 0xFF included",
        chunked(b"4\r\n\x00\xff\x0d\x0a\r\n0\r\n\r\n"),
        done(1, b"\x00\xff\r\n", b""),
    );
    // ----- 7.1 last-chunk = 1*("0") [ chunk-ext ] CRLF -----
    add(
        "7.1 last-chunk: several zeros",
        chunked(b"1\r\nx\r\n000\r\n\r\n"),
        done(1, b"x", b""),
    );
    add(
        "7.1 last-chunk: with an extension",
        chunked(b"0;done\r\n\r\n"),
        done(1, b"", b""),
    );
    // ----- 7.1 "The chunked coding does not define any parameters" -----
    add(
        "7.1 parameters on chunked are an error",
        response(b"Transfer-Encoding: chunked;q=1\r\n", b"0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1 chunked as the name alone, in any case, with whitespace",
        response(
            b"transfer-ENCODING:\t CHUNKED \t\r\n",
            b"1\r\nx\r\n0\r\n\r\n",
        ),
        done(1, b"x", b""),
    );
    // ----- 7.1.1 chunk-ext -----
    add(
        "7.1.1 chunk-ext: a name and value, then a bare name",
        chunked(b"4;a=b;c\r\nwiki\r\n0\r\n\r\n"),
        done(1, b"wiki", b""),
    );
    add(
        "7.1.1 chunk-ext: BWS around ';' and '=', and a quoted-string",
        chunked(b"5 ; x = \"y\"\r\npedia\r\n0\r\n\r\n"),
        done(1, b"pedia", b""),
    );
    add(
        "7.1.1 chunk-ext: a tab is BWS",
        chunked(b"3\t;\ta\t=\tb\r\nabc\r\n0\r\n\r\n"),
        done(1, b"abc", b""),
    );
    add(
        "7.1.1 chunk-ext: a quoted-string holding ';', '=', a quoted pair and a backslash",
        chunked(b"3;n=\"a;b=c\\\"d\\\\e\"\r\nabc\r\n0\r\n\r\n"),
        done(1, b"abc", b""),
    );
    add(
        "7.1.1 chunk-ext: \"A recipient MUST ignore unrecognized chunk extensions\" (200 of them)",
        chunked(&cat(&[
            b"3",
            &b";ext=value".repeat(200),
            b"\r\nabc\r\n0\r\n\r\n",
        ])),
        done(1, b"abc", b""),
    );
    add(
        "7.1.1 chunk-ext: on the last chunk, with a name and a value",
        chunked(b"0;sum=1234\r\n\r\n"),
        done(1, b"", b""),
    );
    add(
        "7.1.1 chunk-ext: ';' needs a name",
        chunked(b"3;\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.1 chunk-ext: '=' needs a value",
        chunked(b"3;a=\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.1 chunk-ext: a quoted-string must end",
        chunked(b"3;a=\"b\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.1 chunk-ext: whitespace is not a separator without ';'",
        chunked(b"3 x\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.1 chunk-ext: the name is a token",
        chunked(b"3;a(b)\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.1 chunk-ext: the value is one token or one quoted-string",
        chunked(b"3;a=b c\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.1 chunk-ext: no name before '='",
        chunked(b"3;=b\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.1 chunk-ext: a bare CR inside the line",
        chunked(b"3;a\rb\r\nabc\r\n0\r\n\r\n"),
        Want::Invalid,
    );
    // ----- 7.1.2 trailer-section = *( field-line CRLF ) -----
    add(
        "7.1.2 trailer-section: one trailer field, discarded (never merged into the header fields)",
        chunked(b"1\r\nx\r\n0\r\nX-Sum: abc\r\n\r\n"),
        done(1, b"x", b""),
    );
    add(
        "7.1.2 trailer-section: several, with whitespace around the value",
        chunked(b"1\r\nx\r\n0\r\nA: 1\r\nB:\t2 \r\nC:\r\n\r\n"),
        done(1, b"x", b""),
    );
    add(
        "7.1.2 trailer-section: a trailer Content-Length is not framing and not a header field",
        chunked(b"1\r\nx\r\n0\r\nContent-Length: 99\r\n\r\n"),
        done(1, b"x", b""),
    );
    add(
        "7.1.2 trailer-section: a trailer Transfer-Encoding is not a header field either",
        chunked(b"1\r\nx\r\n0\r\nTransfer-Encoding: gzip\r\n\r\nrest"),
        done(1, b"x", b"rest"),
    );
    add(
        "7.1.2 trailer-section: a line that is not a field-line",
        chunked(b"1\r\nx\r\n0\r\nnot a field\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.2 trailer-section: no whitespace before the colon (5.1)",
        chunked(b"1\r\nx\r\n0\r\nX : y\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.2 trailer-section: a bare LF inside a trailer value",
        chunked(b"1\r\nx\r\n0\r\nX: a\nb\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "7.1.2 trailer-section: 257 trailer lines are past our limit of 256",
        chunked(&cat(&[b"0\r\n", &b"T: v\r\n".repeat(257), b"\r\n"])),
        Want::Invalid,
    );
    add(
        "7.1.2 trailer-section: 256 trailer lines are not",
        chunked(&cat(&[b"0\r\n", &b"T: v\r\n".repeat(256), b"\r\n"])),
        done(1, b"", b""),
    );
    // ----- 7.1.3 Decoding Chunked -----
    add(
        "7.1.3 decoding: the content is the chunk-data in order, its length the sum of the sizes",
        chunked(b"1\r\na\r\n2\r\nbc\r\n3\r\ndef\r\n4\r\nghij\r\n0\r\n\r\n"),
        done(1, b"abcdefghij", b""),
    );
    add(
        "7.1.3 decoding: waiting for chunk-data",
        chunked(b"5\r\nhel"),
        Want::Truncated,
    );
    add(
        "7.1.3 decoding: waiting for the CRLF after chunk-data",
        chunked(b"5\r\nhello\r"),
        Want::Truncated,
    );
    add(
        "7.1.3 decoding: waiting for the last-chunk",
        chunked(b"5\r\nhello\r\n"),
        Want::Truncated,
    );
    add(
        "7.1.3 decoding: waiting for the trailer section to end",
        chunked(b"5\r\nhello\r\n0\r\nX: y\r\n"),
        Want::Truncated,
    );
    add(
        "7.1.3 decoding: waiting for the final CRLF",
        chunked(b"5\r\nhello\r\n0\r\n"),
        Want::Truncated,
    );
    // ----- 11.1 Response Splitting -----
    let injected = b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello";
    add(
        "11.1 response splitting: a Location echoing CRLF followed by a second response, no length: the second response is the first one's content",
        cat(&[b"HTTP/1.1 302 Found\r\nLocation: /x\r\n\r\n", injected]),
        Want::CloseDelimited(injected.to_vec()),
    );
    add(
        "11.1 response splitting: the same with a Content-Length of 0: the injected response is only the octets after the message, never parsed as a response",
        cat(&[
            b"HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 0\r\n\r\n",
            injected,
        ]),
        Want::Done {
            status: 302,
            fields: 2,
            body: Vec::new(),
            rest: injected.to_vec(),
        },
    );
    add(
        "11.1 response splitting: a raw LF in a field value",
        head_with(b"Location: /x\nSet-Cookie: a=b\r\n"),
        Want::Invalid,
    );
    add(
        "11.1 response splitting: a raw CR in a field value",
        head_with(b"Location: /x\rSet-Cookie: a=b\r\n"),
        Want::Invalid,
    );
    add(
        "11.1 response splitting: a NUL in a field value",
        head_with(b"Location: /x\0y\r\n"),
        Want::Invalid,
    );
    add(
        "11.1 response splitting: an encoded CRLF (%0D%0A) is only text",
        cat(&[
            b"HTTP/1.1 302 Found\r\nLocation: /x%0D%0ASet-Cookie: a=b\r\nContent-Length: 0\r\n\r\n",
        ]),
        Want::Done {
            status: 302,
            fields: 2,
            body: Vec::new(),
            rest: Vec::new(),
        },
    );
    // ----- 11.2 Request Smuggling (the response side of it) -----
    add(
        "11.2 smuggling: Transfer-Encoding and Content-Length together",
        response(
            b"Transfer-Encoding: chunked\r\nContent-Length: 5\r\n",
            b"0\r\n\r\n",
        ),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: Content-Length and Transfer-Encoding together, the other way round",
        response(
            b"Content-Length: 5\r\nTransfer-Encoding: chunked\r\n",
            b"0\r\n\r\n",
        ),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: the same, field names in other cases",
        response(
            b"CONTENT-LENGTH: 0\r\ntransfer-encoding: chunked\r\n",
            b"0\r\n\r\n",
        ),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: a Content-Length of 0 beside chunked",
        response(
            b"Transfer-Encoding: chunked\r\nContent-Length: 0\r\n",
            b"0\r\n\r\n",
        ),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: two different Content-Length values",
        response(b"Content-Length: 5\r\nContent-Length: 6\r\n", b"hello!"),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: a list of different Content-Length values",
        response(b"Content-Length: 5, 6\r\n", b"hello!"),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: identical Content-Length values are one value",
        response(b"Content-Length: 5\r\nContent-Length: 5\r\n", b"hello"),
        done(2, b"hello", b""),
    );
    add(
        "11.2 smuggling: a Content-Length list of identical values",
        response(b"Content-Length: 5, 5\r\n", b"hello"),
        done(1, b"hello", b""),
    );
    add(
        "11.2 smuggling: leading zeros are digits",
        response(b"Content-Length: 0005\r\n", b"hello"),
        done(1, b"hello", b""),
    );
    for (label, value) in [
        (
            "11.2 smuggling: an invalid Content-Length: a plus sign",
            &b"+5"[..],
        ),
        (
            "11.2 smuggling: an invalid Content-Length: a minus sign",
            b"-5",
        ),
        (
            "11.2 smuggling: an invalid Content-Length: a hex prefix",
            b"0x5",
        ),
        (
            "11.2 smuggling: an invalid Content-Length: a space inside",
            b"5 5",
        ),
        (
            "11.2 smuggling: an invalid Content-Length: a fraction",
            b"5.0",
        ),
        (
            "11.2 smuggling: an invalid Content-Length: an empty value",
            b"",
        ),
        (
            "11.2 smuggling: an invalid Content-Length: a trailing letter",
            b"5x",
        ),
        (
            "11.2 smuggling: an invalid Content-Length: a non-ASCII digit",
            b"\xd9\xa5",
        ),
        (
            "11.2 smuggling: an invalid Content-Length: a number past a u64",
            b"18446744073709551616",
        ),
        (
            "11.2 smuggling: an invalid Content-Length: a number past the body limit",
            b"67108865",
        ),
    ] {
        add(
            label,
            response(&cat(&[b"Content-Length: ", value, b"\r\n"]), b"hello"),
            Want::Invalid,
        );
    }
    add(
        "11.2 smuggling: whitespace before the colon of Transfer-Encoding (5.1)",
        response(b"Transfer-Encoding : chunked\r\n", b"0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: whitespace before the colon of Content-Length (5.1)",
        response(b"Content-Length : 5\r\n", b"hello"),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: a coding that only contains \"chunked\"",
        response(b"Transfer-Encoding: xchunked\r\n", b"0\r\n\r\n"),
        Want::Unsupported,
    );
    add(
        "11.2 smuggling: chunked is not the final coding",
        response(b"Transfer-Encoding: chunked, identity\r\n", b"0\r\n\r\n"),
        Want::Unsupported,
    );
    add(
        "11.2 smuggling: chunked in one line and another coding in the next",
        response(
            b"Transfer-Encoding: chunked\r\nTransfer-Encoding: identity\r\n",
            b"0\r\n\r\n",
        ),
        Want::Unsupported,
    );
    add(
        "11.2 smuggling: chunked applied twice",
        response(b"Transfer-Encoding: chunked, chunked\r\n", b"0\r\n\r\n"),
        Want::Unsupported,
    );
    add(
        "11.2 smuggling: a quoted coding name",
        response(b"Transfer-Encoding: \"chunked\"\r\n", b"0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: a vertical tab beside the coding",
        response(b"Transfer-Encoding: chunked\x0b\r\n", b"0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: an empty Transfer-Encoding",
        response(b"Transfer-Encoding:\r\n", b"0\r\n\r\n"),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: an empty Transfer-Encoding with a Content-Length",
        response(b"Transfer-Encoding:\r\nContent-Length: 5\r\n", b"hello"),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: a Transfer-Encoding in an HTTP/1.0 response is faulty framing (6.1)",
        cat(&[b"HTTP/1.0 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n"]),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: obs-fold is replaced by one SP (5.2), so a folded chunked is chunked",
        response(
            b"Transfer-Encoding:\r\n chunked\r\n",
            b"1\r\nx\r\n0\r\n\r\n",
        ),
        done(1, b"x", b""),
    );
    add(
        "11.2 smuggling: a Content-Length folded into the Transfer-Encoding line is part of its value, not a field",
        response(
            b"Transfer-Encoding: chunked\r\n Content-Length: 5\r\n",
            b"0\r\n\r\n",
        ),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: whitespace between the status line and the first field (2.2)",
        cat(&[b"HTTP/1.1 200 OK\r\n Transfer-Encoding: chunked\r\n\r\n0\r\n\r\n"]),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: bare LF as the line terminator",
        cat(&[b"HTTP/1.1 200 OK\nTransfer-Encoding: chunked\n\n0\r\n\r\n"]),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: bare LF after a field line",
        cat(&[b"HTTP/1.1 200 OK\r\nContent-Length: 5\nX: y\r\n\r\nhello"]),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: a bare CR in a field name",
        response(b"Content-Length\r: 5\r\n", b"hello"),
        Want::Invalid,
    );
    add(
        "11.2 smuggling: a 204 is ended by its head even with Transfer-Encoding and Content-Length (6.3 step 1 before 3)",
        cat(&[
            b"HTTP/1.1 204 No Content\r\nTransfer-Encoding: chunked\r\nContent-Length: 5\r\n\r\nhello",
        ]),
        Want::Done {
            status: 204,
            fields: 2,
            body: Vec::new(),
            rest: b"hello".to_vec(),
        },
    );
    // ----- 11.3 Message Integrity: truncation by closing -----
    add(
        "11.3 truncation: Content-Length, one octet short",
        response(b"Content-Length: 5\r\n", b"hell"),
        Want::Truncated,
    );
    add(
        "11.3 truncation: chunked, cut inside a chunk",
        chunked(b"a\r\n01234"),
        Want::Truncated,
    );
    add(
        "11.3 truncation: chunked, cut before the last-chunk",
        chunked(b"1\r\nx\r\n"),
        Want::Truncated,
    );
    add(
        "11.3 truncation: the head cut inside a field line",
        b"HTTP/1.1 200 OK\r\nContent-Le".to_vec(),
        Want::Truncated,
    );
    add(
        "11.3 truncation: the head cut before the empty line",
        b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\n".to_vec(),
        Want::Truncated,
    );
    add(
        "11.3 truncation: nothing at all",
        Vec::new(),
        Want::Truncated,
    );
    add(
        "11.3 truncation: no length is the case where closing ends the message (6.3 step 8)",
        response(b"Server: x\r\n", b"all of it"),
        Want::CloseDelimited(b"all of it".to_vec()),
    );
    // HEAD and the no-content statuses never have a body.
    v.push(Rfc {
        label: "6.3 step 1: a response to HEAD has no body whatever it says",
        input: head_with(b"Content-Length: 5\r\n"),
        head: true,
        want: Want::Done {
            status: 200,
            fields: 1,
            body: Vec::new(),
            rest: Vec::new(),
        },
    });
    v.push(Rfc {
        label: "6.3 step 1: a response to HEAD with Transfer-Encoding has no body",
        input: cat(&[&head_with(b"Transfer-Encoding: chunked\r\n"), b"extra"]),
        head: true,
        want: Want::Done {
            status: 200,
            fields: 1,
            body: Vec::new(),
            rest: b"extra".to_vec(),
        },
    });
    v
}

/// The answer for `input`, checked against what `want` says.
fn check_rfc(c: &Rfc) -> Result<(), String> {
    let open = parse_response_exec(&c.input, c.head);
    let closed = parse_response_at_close_exec(&c.input, c.head);
    match &c.want {
        Want::Done {
            status,
            fields,
            body,
            rest,
        } => match &open {
            ParseBuf::Done { response, rest: r }
                if response.status_line.status == *status
                    && response.fields.len() == *fields
                    && &response.body == body
                    && r == rest => {}
            other => {
                return Err(format!(
                    "expected Done({status}, {fields} fields, {:?}, rest {:?}), got {other:?}",
                    show(body),
                    show(rest)
                ));
            }
        },
        Want::Invalid => {
            if open != ParseBuf::Invalid {
                return Err(format!("expected Invalid, got {open:?}"));
            }
        }
        Want::Unsupported => {
            if open != ParseBuf::Unsupported {
                return Err(format!("expected Unsupported, got {open:?}"));
            }
        }
        Want::Truncated => {
            if open != ParseBuf::Incomplete || closed != ParseBuf::Invalid {
                return Err(format!(
                    "expected Incomplete then Invalid at close, got {open:?} then {closed:?}"
                ));
            }
        }
        Want::CloseDelimited(body) => {
            let ok = open == ParseBuf::Incomplete
                && matches!(&closed, ParseBuf::Done { response, rest }
                    if &response.body == body && rest.is_empty());
            if !ok {
                return Err(format!(
                    "expected Incomplete then Done({:?}) at close, got {open:?} then {closed:?}",
                    show(body)
                ));
            }
        }
    }
    pieces_all(&c.input, c.head)
}

#[test]
fn rfc_9112_examples() {
    let cases = rfc_cases();
    let mut failed = 0usize;
    // Miri checks every 8th case (all of them took 385 s there): it looks
    // for undefined behaviour in the paths they exercise, and the normal
    // test job checks every case.
    let stride = if cfg!(miri) { 8 } else { 1 };
    for c in cases.iter().step_by(stride) {
        if let Err(e) = check_rfc(c) {
            failed = failed.saturating_add(1);
            println!("FAIL {}: {e}\n  input {:?}", c.label, show(&c.input));
        }
    }
    // The request side of §11.1: what we write has no CR or LF but ours.
    let serialize_cases = serialize_checks();
    let serialize_failed = serialize_cases.iter().filter(|r| r.is_err()).count();
    for e in serialize_cases.iter().filter_map(|r| r.as_ref().err()) {
        println!("FAIL {e}");
    }
    let total = cases.len().saturating_add(serialize_cases.len());
    let fail = failed.saturating_add(serialize_failed);
    if !cfg!(miri) {
        summary(
            "RFC 9112 7.1 and 11 examples",
            total.saturating_sub(fail),
            0,
            fail,
            total,
        );
    }
    assert_eq!(fail, 0);
}

fn field(n: &[u8], v: &[u8]) -> FieldLineBuf {
    FieldLineBuf {
        name: n.to_vec(),
        value: v.to_vec(),
    }
}

/// §11.1: "prevent anything other than the server's core protocol
/// libraries from sending a CR or LF within the header section". Our
/// request serializer writes only valid requests, so injected octets in a
/// method, target or value are refused, and what is written parses.
fn serialize_checks() -> Vec<Result<(), String>> {
    let base = || RequestBuf {
        method: b"GET".to_vec(),
        target: b"/x".to_vec(),
        fields: vec![field(b"Host", b"example.com")],
    };
    let mut out = Vec::new();
    let good = serialize_request(&base());
    out.push(
        if good.as_deref() == Some(&b"GET /x HTTP/1.1\r\nHost: example.com\r\n\r\n"[..]) {
            Ok(())
        } else {
            Err(format!("11.1 serializer: the plain request gave {good:?}"))
        },
    );
    for (label, req) in [
        (
            "CRLF in a field value",
            RequestBuf {
                fields: vec![field(b"X", b"a\r\nInjected: 1")],
                ..base()
            },
        ),
        (
            "LF in a field value",
            RequestBuf {
                fields: vec![field(b"X", b"a\nInjected: 1")],
                ..base()
            },
        ),
        (
            "CR in a field value",
            RequestBuf {
                fields: vec![field(b"X", b"a\rb")],
                ..base()
            },
        ),
        (
            "CRLF in a field name",
            RequestBuf {
                fields: vec![field(b"X\r\nInjected", b"1")],
                ..base()
            },
        ),
        (
            "CRLF in the target",
            RequestBuf {
                target: b"/x\r\nHost: evil".to_vec(),
                ..base()
            },
        ),
        (
            "a space in the target",
            RequestBuf {
                target: b"/x HTTP/1.1\r\n".to_vec(),
                ..base()
            },
        ),
        (
            "CRLF in the method",
            RequestBuf {
                method: b"GE\r\nT".to_vec(),
                ..base()
            },
        ),
        (
            "an empty method",
            RequestBuf {
                method: Vec::new(),
                ..base()
            },
        ),
    ] {
        let got = serialize_request(&req);
        out.push(if got.is_none() {
            Ok(())
        } else {
            Err(format!(
                "11.1 serializer: {label} was written: {:?}",
                got.as_deref().map(show)
            ))
        });
    }
    out
}

// ---------------------------------------------------------------------------
// Suite 2: the llhttp fixtures.
// ---------------------------------------------------------------------------

/// What llhttp's log says about one message.
struct Msg {
    version: (u8, u8),
    /// 0 for a request.
    status: u16,
    fields: &'static [(&'static [u8], &'static [u8])],
    body: &'static [u8],
    headers_done: bool,
    complete: bool,
}

/// How llhttp's log ends.
enum End {
    /// Nothing more: the input ran out.
    Eof,
    Error {
        code: u32,
        reason: &'static str,
    },
}

/// One converted test.
struct Case {
    /// `response/sample.md:12`: the file and the line of the heading.
    id: &'static str,
    name: &'static str,
    /// The `type` of the test's meta comment.
    ty: &'static str,
    skip_body: bool,
    input: &'static [u8],
    msgs: &'static [Msg],
    end: End,
}

// `const LLHTTP: &[Case]`, generated from the vendored markdown files.
include!("generated/llhttp.rs");

const ASCII_WS: &[u8] = b" \t";

fn trim_ows(v: &[u8]) -> &[u8] {
    let start = v
        .iter()
        .position(|b| !ASCII_WS.contains(b))
        .unwrap_or(v.len());
    let end = v
        .iter()
        .rposition(|b| !ASCII_WS.contains(b))
        .map_or(start, |e| e.saturating_add(1));
    v.get(start..end).unwrap_or(&[])
}

/// A request is run as the response a server would send: the request line
/// `METHOD target HTTP/x.y` becomes `HTTP/x.y 200 OK`. Anything else is
/// left as it is.
fn as_response(data: &[u8]) -> Vec<u8> {
    let line_end = data
        .windows(2)
        .position(|w| w == b"\r\n")
        .unwrap_or(data.len());
    let line = data.get(..line_end).unwrap_or(&[]);
    let version = line.len().checked_sub(8).and_then(|s| line.get(s..));
    match version {
        Some(v)
            if v.starts_with(b"HTTP/")
                && at(v, 5).is_ascii_digit()
                && at(v, 6) == b'.'
                && at(v, 7).is_ascii_digit()
                && line.get(..line.len().saturating_sub(9)).is_some_and(|m| {
                    m.contains(&b' ') && !m.iter().any(|b| b.is_ascii_control())
                }) =>
        {
            cat(&[v, b" 200 OK", data.get(line_end..).unwrap_or(&[])])
        }
        _ => data.to_vec(),
    }
}

fn describe_fields(f: &[(Vec<u8>, Vec<u8>)]) -> String {
    f.iter()
        .map(|(n, v)| format!("{}: {}", show(n), show(v)))
        .collect::<Vec<_>>()
        .join(" | ")
}

fn rejected(p: &ParseBuf) -> bool {
    matches!(p, ParseBuf::Invalid | ParseBuf::Unsupported)
}

/// Run one converted test through the parser and compare with what llhttp
/// did. `Err` says how they differ.
fn run_llhttp(c: &Case) -> Result<(), String> {
    let is_request = c.ty.starts_with("request");
    let mut data = c.input.to_vec();
    for (i, m) in c.msgs.iter().enumerate() {
        if is_request {
            data = as_response(&data);
        }
        let open = parse_response_exec(&data, c.skip_body);
        let closed = parse_response_at_close_exec(&data, c.skip_body);
        let label = format!("message {i}");
        if m.complete {
            let ParseBuf::Done { response, rest } = open else {
                return Err(format!("{label}: llhttp completes it, we give {open:?}"));
            };
            let s = &response.status_line;
            if !is_request && s.status != m.status {
                return Err(format!(
                    "{label}: status {} (llhttp {})",
                    s.status, m.status
                ));
            }
            if m.headers_done && (s.major, s.minor) != m.version {
                return Err(format!(
                    "{label}: version {}.{} (llhttp {}.{})",
                    s.major, s.minor, m.version.0, m.version.1
                ));
            }
            let ours: Vec<(Vec<u8>, Vec<u8>)> = response
                .fields
                .iter()
                .map(|f| (f.name.clone(), f.value.clone()))
                .collect();
            let theirs: Vec<(Vec<u8>, Vec<u8>)> = m
                .fields
                .iter()
                .map(|(n, v)| (n.to_vec(), trim_ows(v).to_vec()))
                .collect();
            if ours != theirs {
                return Err(format!(
                    "{label}: fields [{}] (llhttp [{}])",
                    describe_fields(&ours),
                    describe_fields(&theirs)
                ));
            }
            if response.body != m.body {
                return Err(format!(
                    "{label}: body {:?} (llhttp {:?})",
                    show(&response.body),
                    show(m.body)
                ));
            }
            data = rest;
        } else {
            match &c.end {
                End::Error { code, reason } => {
                    let ours_rejects = rejected(&open)
                        || (open == ParseBuf::Incomplete && closed == ParseBuf::Invalid);
                    if !ours_rejects {
                        return Err(format!(
                            "{label}: llhttp errors ({code} {reason:?}), we give {open:?}, at close {closed:?}"
                        ));
                    }
                }
                End::Eof => {
                    if open != ParseBuf::Incomplete {
                        return Err(format!("{label}: llhttp waits for more, we give {open:?}"));
                    }
                    match &closed {
                        ParseBuf::Invalid => {}
                        ParseBuf::Done { response, rest }
                            if m.headers_done && response.body == m.body && rest.is_empty() => {}
                        other => {
                            return Err(format!(
                                "{label}: llhttp waits for more, at close we give {other:?}"
                            ));
                        }
                    }
                }
            }
            // The incremental parser agrees with the whole parse.
            return pieces_all(&data, c.skip_body);
        }
    }
    // Every message llhttp completed is done: what is left.
    match &c.end {
        End::Error { code, reason } => {
            let open = parse_response_exec(&as_if_response(is_request, &data), c.skip_body);
            let closed =
                parse_response_at_close_exec(&as_if_response(is_request, &data), c.skip_body);
            let ours_rejects =
                rejected(&open) || (open == ParseBuf::Incomplete && closed == ParseBuf::Invalid);
            if !ours_rejects {
                return Err(format!(
                    "after the last message: llhttp errors ({code} {reason:?}), we give {open:?} on {:?}",
                    show(&data)
                ));
            }
        }
        End::Eof => {
            if !data.is_empty() {
                return Err(format!(
                    "{} octets are left after the last message ({:?}); llhttp read them all",
                    data.len(),
                    show(&data)
                ));
            }
        }
    }
    pieces_all(&as_if_response(is_request, c.input), c.skip_body)
}

fn as_if_response(is_request: bool, data: &[u8]) -> Vec<u8> {
    if is_request {
        as_response(data)
    } else {
        data.to_vec()
    }
}

// The reasons llhttp's answer is not ours. Each is one of the choices listed
// at the top of `src/message/spec.rs`, or the literal reading of an ABNF rule.

/// `spec.rs`: "§6.3 step 3 (both `Transfer-Encoding` and `Content-Length`)
/// ought to be handled as an error: `Invalid`, never resolved in favour of
/// either."
const TE_AND_CL: &str = "Transfer-Encoding together with Content-Length is Invalid, never resolved in favour of either (spec.rs, RFC 9112 6.3 step 3 and 11.2); llhttp's `lenient chunked length` flag, which this case turns on, reads one of them";
/// `spec.rs`: "§6.3 step 4 for codings".
const CODINGS: &str = "a transfer coding other than a lone `chunked` is Unsupported, not decoded (spec.rs, RFC 9112 6.3 step 4: modelling choice); llhttp decodes `chunked` under another coding, or reads to the end of the connection";
/// `spec.rs`: "An empty line before the status line is rejected" (RFC 9112
/// 2.2 allows ignoring one only "prior to the request-line").
const LEADING_CRLF: &str = "an empty line before a status line is not skipped: RFC 9112 2.2 lets a recipient ignore one only before a request-line, so the status-line grammar starts at the first octet (spec.rs `read_head`); llhttp skips it, here between two pipelined messages";
/// `spec.rs`: "Only HTTP/1.x responses are parsed".
const VERSION_1X: &str = "only HTTP/1.x is parsed (spec.rs modelling choice: the major version must be 1); llhttp also reads HTTP/0.9, and any version in its lenient mode";
const NOT_HTTP: &str = "the status line starts with `HTTP/` (RFC 9112 2.3: HTTP-name is the case-sensitive \"HTTP\"); llhttp also reads RTSP/ and ICE/";
/// `spec.rs`: "The trailer section (§7.1.2) is parsed with the same
/// field-line grammar and dropped".
const TRAILERS: &str = "trailer fields are parsed and dropped, never merged into the header fields (spec.rs, RFC 9112 7.1.2: \"MAY selectively retain or discard\", \"MUST NOT merge\"); llhttp's log lists them as header fields";
/// `spec.rs`: "Lines end only at CRLF" and "A bare CR ... makes its element
/// invalid".
const BARE_LF: &str = "lines end only at CRLF and a bare CR or LF is invalid (spec.rs, RFC 9112 2.2: the first of the two options it gives); llhttp's lenient mode, which this case turns on, accepts a lone LF or CR as a line end";
/// `spec.rs`: "Whitespace between a field name and the colon (§5.1) is
/// rejected".
const SPACE_BEFORE_COLON: &str = "whitespace between a field name and the colon is rejected (spec.rs, RFC 9112 5.1); llhttp's lenient headers mode, which this case turns on, accepts it";
const LENIENT_CHUNK: &str = "chunk framing is strict: `chunk-size [ chunk-ext ] CRLF chunk-data CRLF` with no whitespace after the size and a CRLF after the data (spec.rs, RFC 9112 7.1); llhttp's lenient mode, which this case turns on, accepts the variation";
const LENIENT_FOLD: &str = "an obs-fold is replaced by one SP (spec.rs, RFC 9112 5.2), so a folded `Transfer-Encoding` value reads \"chunked abc\", which is no coding list (Invalid); llhttp's lenient headers mode, which this case turns on, reads it differently";
const AFTER_CLOSE: &str = "the octets after a message are returned as `rest` for the caller to discard (RFC 9112 9.6, 6.3: never parsed as another response); llhttp's lenient `data after close` mode, which this case turns on, drops them";

/// Cases where llhttp's answer is not ours by design: (id, reason). A case
/// listed here that agrees, or one that differs and is not listed, fails the
/// suite.
const XFAIL: &[(&str, &str)] = &[
    ("request/content-length.md:189", SPACE_BEFORE_COLON),
    ("request/content-length.md:229", TE_AND_CL),
    ("request/content-length.md:519", BARE_LF),
    ("request/transfer-encoding.md:212", TRAILERS),
    ("request/transfer-encoding.md:556", TE_AND_CL),
    ("request/transfer-encoding.md:706", CODINGS),
    ("request/transfer-encoding.md:739", CODINGS),
    ("request/transfer-encoding.md:777", CODINGS),
    ("request/transfer-encoding.md:819", CODINGS),
    ("request/transfer-encoding.md:1051", BARE_LF),
    ("request/transfer-encoding.md:1166", LENIENT_CHUNK),
    ("request/transfer-encoding.md:1241", LENIENT_CHUNK),
    ("response/connection.md:191", AFTER_CLOSE),
    ("response/connection.md:492", LEADING_CRLF),
    ("response/connection.md:586", LEADING_CRLF),
    ("response/invalid.md:151", BARE_LF),
    ("response/invalid.md:304", BARE_LF),
    ("response/lenient-version.md:4", VERSION_1X),
    ("response/pipelining.md:4", LEADING_CRLF),
    ("response/sample.md:40", NOT_HTTP),
    ("response/sample.md:60", NOT_HTTP),
    ("response/sample.md:645", VERSION_1X),
    ("response/sample.md:695", LEADING_CRLF),
    ("response/transfer-encoding.md:67", CODINGS),
    ("response/transfer-encoding.md:98", CODINGS),
    ("response/transfer-encoding.md:134", CODINGS),
    ("response/transfer-encoding.md:413", LENIENT_FOLD),
];

#[test]
fn llhttp_fixtures() {
    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut fail = 0usize;
    let mut total = 0usize;
    for c in LLHTTP.iter().step_by(CORPUS_STEP) {
        total = total.saturating_add(1);
        let listed = XFAIL.iter().find(|(id, _)| *id == c.id);
        match (run_llhttp(c), listed) {
            (Ok(()), None) => pass = pass.saturating_add(1),
            (Err(_), Some(_)) => xfail = xfail.saturating_add(1),
            (Ok(()), Some((_, reason))) => {
                fail = fail.saturating_add(1);
                println!(
                    "FAIL {} ({}): expected to differ ({reason}), but agrees",
                    c.id, c.name
                );
            }
            (Err(e), None) => {
                fail = fail.saturating_add(1);
                println!(
                    "FAIL {} ({}) [{}]: {e}\n  input {:?}",
                    c.id,
                    c.name,
                    c.ty,
                    show(c.input)
                );
            }
        }
    }
    if !cfg!(miri) {
        assert_eq!(total, LLHTTP.len());
    }
    summary(
        "llhttp test/response and framing cases",
        pass,
        xfail,
        fail,
        total,
    );
    assert_eq!(fail, 0);
}

// ---------------------------------------------------------------------------
// Suites 3 to 6: the differential against `httparse`.
// ---------------------------------------------------------------------------

/// A response head as one engine read it.
#[derive(Debug, PartialEq, Eq, Clone)]
struct Head {
    major: u8,
    minor: u8,
    status: u16,
    reason: Vec<u8>,
    fields: Vec<(Vec<u8>, Vec<u8>)>,
    /// Octets of the head, the empty line included.
    len: usize,
}

#[derive(Debug, Clone)]
enum Read {
    Complete(Head),
    Partial,
    Reject,
}

fn ours(buf: &[u8]) -> Read {
    match read_head_exec(buf) {
        HeadExec::Done { head, next } => Read::Complete(Head {
            major: head.status_line.major,
            minor: head.status_line.minor,
            status: head.status_line.status,
            reason: head.status_line.reason.clone(),
            fields: head
                .fields
                .iter()
                .map(|f| (f.name.clone(), f.value.clone()))
                .collect(),
            len: next,
        }),
        HeadExec::Incomplete => Read::Partial,
        HeadExec::Invalid => Read::Reject,
    }
}

/// More fields than we accept, so that only our limit can differ.
const THEIR_FIELDS: usize = 300;

fn theirs(buf: &[u8]) -> Read {
    let mut headers = [httparse::EMPTY_HEADER; THEIR_FIELDS];
    let mut r = httparse::Response::new(&mut headers);
    match r.parse(buf) {
        Ok(httparse::Status::Complete(n)) => Read::Complete(Head {
            major: 1,
            minor: r.version.unwrap_or(9),
            status: r.code.unwrap_or(0),
            reason: r.reason.unwrap_or("").as_bytes().to_vec(),
            fields: r
                .headers
                .iter()
                .map(|h| (h.name.as_bytes().to_vec(), h.value.to_vec()))
                .collect(),
            len: n,
        }),
        Ok(httparse::Status::Partial) => Read::Partial,
        Err(_) => Read::Reject,
    }
}

/// How two heads that both parsed differ, if they do. `httparse` gives an
/// empty reason phrase when it holds obs-text, so then ours is not compared.
fn diff(a: &Head, b: &Head) -> Option<String> {
    let reason_skipped = a.reason.iter().any(|&c| c >= 0x80);
    if (a.major, a.minor, a.status, a.len) != (b.major, b.minor, b.status, b.len) {
        return Some(format!(
            "ours HTTP/{}.{} {} head of {} octets, theirs HTTP/{}.{} {} of {}",
            a.major, a.minor, a.status, a.len, b.major, b.minor, b.status, b.len
        ));
    }
    if !reason_skipped && a.reason != b.reason {
        return Some(format!(
            "reason ours {:?}, theirs {:?}",
            show(&a.reason),
            show(&b.reason)
        ));
    }
    if a.fields != b.fields {
        return Some(format!(
            "fields ours [{}], theirs [{}]",
            describe_fields(&a.fields),
            describe_fields(&b.fields)
        ));
    }
    None
}

// Why the two parsers may differ. Each is a choice of `spec.rs` or the
// ABNF read literally.

/// `spec.rs`: "Lines end only at CRLF."
const T_BARE_LF: &str = "a bare LF is not a line end (spec.rs: lines end only at CRLF)";
/// `spec.rs`: "An empty line before the status line is rejected".
const T_LEADING: &str = "an empty line before the status line is not skipped (spec.rs; RFC 9112 2.2 only before a request-line)";
/// `spec.rs`: "Only HTTP/1.x responses are parsed"; httparse takes only 1.0
/// and 1.1.
const T_VERSION: &str =
    "HTTP/1.x with x other than 0 and 1 (spec.rs parses every 1.x; httparse only 1.0 and 1.1)";
/// `spec.rs`: "An obs-fold is replaced by a single SP".
const T_FOLD: &str =
    "an obs-fold is replaced by one SP (spec.rs, RFC 9112 5.2); httparse rejects it";
/// `spec.rs`: "Limits".
const T_LIMIT: &str = "past our limits: 8192 octets a line, 256 field lines (spec.rs)";
/// `spec.rs`: a line is judged when its CRLF has arrived, and a field line
/// when the next line has (an obs-fold may continue it).
const T_TIMING: &str = "decided later: we judge a line at its CRLF and a field line at the next line (spec.rs, obs-fold lookahead), httparse at the first bad octet";

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    /// Same answer, same head.
    Agree(&'static str),
    /// Different answers, with the documented reason.
    Explained(&'static str),
    Unexplained(String),
}

fn has_bare_lf(b: &[u8]) -> bool {
    b.iter()
        .enumerate()
        .any(|(i, &c)| c == b'\n' && (i == 0 || at(b, i.saturating_sub(1)) != b'\r'))
}

/// The octets before the first CR or LF.
fn first_line(b: &[u8]) -> &[u8] {
    let end = b
        .iter()
        .position(|&c| c == b'\r' || c == b'\n')
        .unwrap_or(b.len());
    b.get(..end).unwrap_or(&[])
}

fn starts_with_empty_line(b: &[u8]) -> bool {
    b.starts_with(b"\r\n") || b.starts_with(b"\n")
}

/// `HTTP/1.d` first, with a minor digit other than 0 and 1.
fn other_version(b: &[u8]) -> bool {
    let l = first_line(b);
    l.starts_with(b"HTTP/1.") && at(l, 7).is_ascii_digit() && !matches!(at(l, 7), b'0' | b'1')
}

fn has_fold(b: &[u8]) -> bool {
    b.windows(3).any(|w| {
        w.first() == Some(&b'\r')
            && w.get(1) == Some(&b'\n')
            && matches!(w.get(2), Some(b' ' | b'\t'))
    })
}

/// A line over 8192 octets, or more than 256 lines after the status line,
/// before the first empty line.
fn past_limits(b: &[u8]) -> bool {
    let mut lines = 0usize;
    let mut rest = b;
    loop {
        let Some(i) = rest.windows(2).position(|w| w == b"\r\n") else {
            return rest.len() > 8192;
        };
        if i > 8192 {
            return true;
        }
        if i == 0 {
            return false;
        }
        lines = lines.saturating_add(1);
        // The status line is the first line; the limit is on field lines.
        if lines > 257 {
            return true;
        }
        rest = rest.get(i.saturating_add(2)..).unwrap_or(&[]);
    }
}

/// Every LF with no CR before it, preceded by one.
fn fix_bare_lf(b: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(b.len());
    for (i, &c) in b.iter().enumerate() {
        if c == b'\n' && (i == 0 || at(b, i.saturating_sub(1)) != b'\r') {
            out.push(b'\r');
        }
        out.push(c);
    }
    out
}

fn strip_leading_empty_lines(b: &[u8]) -> Vec<u8> {
    let mut rest = b;
    loop {
        if let Some(r) = rest.strip_prefix(b"\r\n") {
            rest = r;
        } else if let Some(r) = rest.strip_prefix(b"\n") {
            rest = r;
        } else {
            return rest.to_vec();
        }
    }
}

fn version_as_1_1(b: &[u8]) -> Vec<u8> {
    cat(&[b"HTTP/1.1", b.get(8..).unwrap_or(&[])])
}

/// Each `OWS CRLF RWS` as one SP, as RFC 9112 5.2 says to read it.
fn unfold(b: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::with_capacity(b.len());
    let mut i = 0usize;
    while i < b.len() {
        if at(b, i) == b'\r' && at(b, i.saturating_add(1)) == b'\n' {
            let mut j = i.saturating_add(2);
            if matches!(at(b, j), b' ' | b'\t') {
                while matches!(at(b, j), b' ' | b'\t') {
                    j = j.saturating_add(1);
                }
                while matches!(out.last(), Some(b' ' | b'\t')) {
                    out.pop();
                }
                out.push(b' ');
                i = j;
                continue;
            }
        }
        out.push(at(b, i));
        i = i.saturating_add(1);
    }
    out
}

/// The `ours`-rejects-and-`httparse`-accepts features: the tag, and the
/// input with the feature repaired. `None`: no feature.
fn repair_for_ours_rejects(b: &[u8]) -> Option<(&'static str, Vec<u8>)> {
    if has_bare_lf(b) {
        Some((T_BARE_LF, fix_bare_lf(b)))
    } else if starts_with_empty_line(b) {
        Some((T_LEADING, strip_leading_empty_lines(b)))
    } else if past_limits(b) {
        Some((T_LIMIT, Vec::new()))
    } else {
        None
    }
}

/// The `ours`-accepts-and-`httparse`-rejects features.
fn repair_for_ours_accepts(b: &[u8]) -> Option<(&'static str, Vec<u8>)> {
    if other_version(b) {
        Some((T_VERSION, version_as_1_1(b)))
    } else if has_fold(b) {
        Some((T_FOLD, unfold(b)))
    } else {
        None
    }
}

/// The input with the bytes that end it: a CRLF for an unterminated line
/// and the empty line.
fn completed(b: &[u8]) -> Vec<u8> {
    cat(&[b, b"\r\n\r\n"])
}

/// Compare the two parsers on `buf`. A difference is explained only when
/// the input has one of the features above *and repairing that feature
/// makes the two agree* (or reach another explained difference).
fn judge(buf: &[u8], depth: usize) -> Verdict {
    let (o, t) = (ours(buf), theirs(buf));
    match (&o, &t) {
        (Read::Complete(a), Read::Complete(b)) => match diff(a, b) {
            None => Verdict::Agree("both accept, same head"),
            Some(d) => Verdict::Unexplained(d),
        },
        (Read::Reject, Read::Reject) => Verdict::Agree("both reject"),
        (Read::Partial, Read::Partial) => Verdict::Agree("both wait"),
        _ => {
            let o2 = if matches!(o, Read::Partial) {
                ours(&completed(buf))
            } else {
                o.clone()
            };
            let t2 = if matches!(t, Read::Partial) {
                theirs(&completed(buf))
            } else {
                t.clone()
            };
            let repaired = |found: Option<(&'static str, Vec<u8>)>| match found {
                None => Verdict::Unexplained(format!(
                    "ours {o:?} (then {o2:?}), theirs {t:?} (then {t2:?}): no documented feature in the input"
                )),
                Some((tag, _)) if tag == T_LIMIT => Verdict::Explained(tag),
                Some((tag, fixed)) => {
                    if depth >= 4 {
                        return Verdict::Unexplained(format!("{tag}: repairs do not end"));
                    }
                    match judge(&fixed, depth.saturating_add(1)) {
                        Verdict::Unexplained(why) => Verdict::Unexplained(format!(
                            "{tag} is present, but without it the parsers still differ: {why}"
                        )),
                        _ => Verdict::Explained(tag),
                    }
                }
            };
            match (&o2, &t2) {
                (Read::Reject, Read::Reject) => Verdict::Explained(T_TIMING),
                (Read::Reject, Read::Complete(_)) => repaired(repair_for_ours_rejects(buf)),
                (Read::Complete(_), Read::Reject) => repaired(repair_for_ours_accepts(buf)),
                (Read::Complete(a), Read::Complete(b)) if diff(a, b).is_none() => {
                    Verdict::Explained(T_TIMING)
                }
                _ => Verdict::Unexplained(format!(
                    "ours {o:?} (then {o2:?}), theirs {t:?} (then {t2:?})"
                )),
            }
        }
    }
}

// ----- Generating well-formed heads -----

const TCHAR: &[u8] =
    b"!#$%&'*+-.^_`|~abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";

/// A visible octet: VCHAR or obs-text.
fn vis(r: &mut Rng) -> u8 {
    if r.chance(8) {
        r.between(0x80, 0xFF)
    } else {
        r.between(0x21, 0x7E)
    }
}

fn ows(r: &mut Rng, most: usize) -> Vec<u8> {
    let n = r.below(most.saturating_add(1));
    (0..n).map(|_| r.pick(b" \t", b' ')).collect()
}

/// A `field-value`: starts and ends with a visible octet, SP and HTAB between.
fn field_value(r: &mut Rng) -> Vec<u8> {
    if r.chance(6) {
        return Vec::new();
    }
    let n = r.below(30).saturating_add(1);
    (0..n)
        .map(|i| {
            if i > 0 && i.saturating_add(1) < n && r.chance(5) {
                r.pick(b" \t", b' ')
            } else {
                vis(r)
            }
        })
        .collect()
}

/// A well-formed head with what it says.
struct Gen {
    bytes: Vec<u8>,
    head: Head,
}

fn gen_head(r: &mut Rng) -> Gen {
    let minor = r.pick(&[0u8, 1], 1);
    let status = u16::try_from(r.below(1000)).unwrap_or(200);
    let reason: Vec<u8> = if r.chance(8) {
        Vec::new()
    } else {
        let n = r.below(20).saturating_add(1);
        (0..n)
            .map(|_| match r.below(8) {
                0 => b' ',
                1 => b'\t',
                _ => vis(r),
            })
            .collect()
    };
    let mut bytes = format!("HTTP/1.{minor} {status:03} ").into_bytes();
    bytes.extend_from_slice(&reason);
    bytes.extend_from_slice(b"\r\n");
    let mut fields = Vec::new();
    for _ in 0..r.below(12) {
        let n = r.below(12).saturating_add(1);
        let name: Vec<u8> = (0..n).map(|_| r.pick(TCHAR, b'a')).collect();
        let value = field_value(r);
        bytes.extend_from_slice(&name);
        bytes.push(b':');
        bytes.extend_from_slice(&ows(r, 2));
        bytes.extend_from_slice(&value);
        bytes.extend_from_slice(&ows(r, 2));
        bytes.extend_from_slice(b"\r\n");
        fields.push((name, value));
    }
    bytes.extend_from_slice(b"\r\n");
    let len = bytes.len();
    Gen {
        bytes,
        head: Head {
            major: 1,
            minor,
            status,
            reason,
            fields,
            len,
        },
    }
}

#[test]
fn differential_random_responses() {
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    let mut pass = 0usize;
    let mut fail = 0usize;
    for _ in 0..RANDOM_ROUNDS {
        let g = gen_head(&mut r);
        // Octets after the head are the body; neither parser reads them.
        let mut buf = g.bytes.clone();
        for _ in 0..r.below(40) {
            buf.push(r.between(0, 255));
        }
        let (o, t) = (ours(&buf), theirs(&buf));
        let problem = match (&o, &t) {
            (Read::Complete(a), Read::Complete(b)) => {
                if *a != g.head {
                    Some(format!("ours read {a:?}, the generator wrote {:?}", g.head))
                } else {
                    diff(a, b)
                }
            }
            _ => Some(format!("ours {o:?}, theirs {t:?}")),
        };
        match problem {
            None => pass = pass.saturating_add(1),
            Some(p) => {
                fail = fail.saturating_add(1);
                if fail <= 10 {
                    println!("FAIL {p}\n  input {:?}", show(&buf));
                }
            }
        }
    }
    summary(
        "httparse differential: random responses",
        pass,
        0,
        fail,
        RANDOM_ROUNDS,
    );
    assert_eq!(fail, 0);
}

// ----- Mutating them -----

/// Octets worth putting into a head.
const INTERESTING: &[u8] = b"\r\n \t:;,\"/.0aHTP\x00\x7f\x80\xff\\";

const FRAGMENTS: &[&[u8]] = &[
    b"\r\n",
    b"\n",
    b"\r",
    b"\r\n ",
    b"\r\n\t",
    b" ",
    b"HTTP/1.1 ",
    b": ",
    b"\r\n\r\n",
    b"  ",
    b"Content-Length: 5\r\n",
];

fn mutate(r: &mut Rng, base: &[u8]) -> Vec<u8> {
    let mut b = base.to_vec();
    for _ in 0..r.below(3).saturating_add(1) {
        if b.is_empty() {
            b.push(r.between(0, 255));
            continue;
        }
        let pos = r.below(b.len());
        match r.below(6) {
            0 => {
                // flip one bit
                if let Some(c) = b.get_mut(pos) {
                    *c ^= 1u8 << r.below(8);
                }
            }
            1 => {
                if let Some(c) = b.get_mut(pos) {
                    *c = if r.chance(2) {
                        r.pick(INTERESTING, b' ')
                    } else {
                        r.between(0, 255)
                    };
                }
            }
            2 => {
                let c = if r.chance(2) {
                    r.pick(INTERESTING, b' ')
                } else {
                    r.between(0, 255)
                };
                b.insert(pos, c);
            }
            3 => {
                b.remove(pos);
            }
            4 => {
                let frag = r.pick(FRAGMENTS, b"\r\n");
                let tail = b.split_off(pos);
                b.extend_from_slice(frag);
                b.extend_from_slice(&tail);
            }
            _ => b.truncate(pos),
        }
    }
    b
}

#[test]
fn differential_mutated_responses() {
    let mut r = Rng(0xD1B5_4A32_D192_ED03);
    let (mut pass, mut xfail, mut fail) = (0usize, 0usize, 0usize);
    let mut agree: BTreeMap<String, usize> = BTreeMap::new();
    let mut explained: BTreeMap<String, usize> = BTreeMap::new();
    for _ in 0..MUTATED_ROUNDS {
        let mut base = gen_head(&mut r).bytes;
        for _ in 0..r.below(8) {
            base.push(r.between(0, 255));
        }
        let buf = mutate(&mut r, &base);
        match judge(&buf, 0) {
            Verdict::Agree(class) => {
                pass = pass.saturating_add(1);
                bump(&mut agree, class);
            }
            Verdict::Explained(tag) => {
                xfail = xfail.saturating_add(1);
                bump(&mut explained, tag);
            }
            Verdict::Unexplained(why) => {
                fail = fail.saturating_add(1);
                if fail <= 10 {
                    println!("FAIL {why}\n  input {:?}", show(&buf));
                }
            }
        }
    }
    print_counts("mutated agreements", &agree);
    print_counts("mutated expected differences", &explained);
    summary(
        "httparse differential: mutated responses",
        pass,
        xfail,
        fail,
        MUTATED_ROUNDS,
    );
    assert_eq!(fail, 0);
}

#[test]
fn differential_llhttp_corpus() {
    let (mut pass, mut xfail, mut fail, mut total) = (0usize, 0usize, 0usize, 0usize);
    let mut explained: BTreeMap<String, usize> = BTreeMap::new();
    for c in LLHTTP.iter().step_by(CORPUS_STEP) {
        total = total.saturating_add(1);
        let buf = as_if_response(c.ty.starts_with("request"), c.input);
        match judge(&buf, 0) {
            Verdict::Agree(_) => pass = pass.saturating_add(1),
            Verdict::Explained(tag) => {
                xfail = xfail.saturating_add(1);
                bump(&mut explained, tag);
            }
            Verdict::Unexplained(why) => {
                fail = fail.saturating_add(1);
                println!(
                    "FAIL {} ({}): {why}\n  input {:?}",
                    c.id,
                    c.name,
                    show(&buf)
                );
            }
        }
    }
    print_counts("corpus expected differences", &explained);
    summary(
        "httparse differential: llhttp corpus heads",
        pass,
        xfail,
        fail,
        total,
    );
    assert_eq!(fail, 0);
}

// ----- Handcrafted heads -----

/// What `judge` must say about an input.
enum Expect {
    Agree,
    Explained(&'static str),
}

fn handcrafted() -> Vec<(&'static str, Vec<u8>, Expect)> {
    let ok = b"HTTP/1.1 200 OK\r\n";
    let mut v: Vec<(&'static str, Vec<u8>, Expect)> = Vec::new();
    let mut add = |label: &'static str, input: Vec<u8>, e: Expect| v.push((label, input, e));
    // Agreements.
    add(
        "a plain response",
        b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add("no fields", cat(&[ok, b"\r\n"]), Expect::Agree);
    add(
        "an empty reason phrase, with its SP",
        b"HTTP/1.1 204 \r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "HTTP/1.0",
        b"HTTP/1.0 200 OK\r\nServer: x\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "status 000, which is three digits",
        b"HTTP/1.1 000 Zero\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "four digits of status",
        b"HTTP/1.1 2000 OK\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "two digits of status",
        b"HTTP/1.1 20 OK\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "two SP after the version",
        b"HTTP/1.1  200 OK\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "a lower-case HTTP",
        b"http/1.1 200 OK\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "whitespace before the colon",
        cat(&[ok, b"X : y\r\n\r\n"]),
        Expect::Agree,
    );
    add(
        "whitespace before the first field name",
        cat(&[ok, b" X: y\r\n\r\n"]),
        Expect::Agree,
    );
    add(
        "an empty field name",
        cat(&[ok, b": y\r\n\r\n"]),
        Expect::Agree,
    );
    add(
        "a field line with no colon",
        cat(&[ok, b"Just text\r\n\r\n"]),
        Expect::Agree,
    );
    add(
        "a DEL in a value",
        cat(&[ok, b"X: a\x7fb\r\n\r\n"]),
        Expect::Agree,
    );
    add(
        "a NUL in a value",
        cat(&[ok, b"X: a\0b\r\n\r\n"]),
        Expect::Agree,
    );
    add(
        "a bare CR in a value",
        cat(&[ok, b"X: a\rb\r\n\r\n"]),
        Expect::Agree,
    );
    add(
        "obs-text in a value and a reason",
        b"HTTP/1.1 200 \xe9\xe8\r\nX: caf\xe9\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "values with leading and trailing whitespace",
        cat(&[ok, b"A:\t \t v \t\r\nB:   \r\nC:w\r\n\r\n"]),
        Expect::Agree,
    );
    add(
        "repeated field names",
        cat(&[ok, b"Set-Cookie: a=b\r\nSet-Cookie: c=d\r\n\r\n"]),
        Expect::Agree,
    );
    add(
        "a head with octets after it",
        cat(&[ok, b"\r\nbody that is not a head"]),
        Expect::Agree,
    );
    add(
        "a head with its last CRLF missing",
        cat(&[ok, b"X: y\r\n"]),
        Expect::Agree,
    );
    add("only the status line", ok.to_vec(), Expect::Agree);
    add("nothing", Vec::new(), Expect::Agree);
    add(
        "garbage with a CRLF",
        b"garbage\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    // Expected differences, one for each feature.
    add(
        "LF as the line terminator everywhere",
        b"HTTP/1.1 200 OK\nContent-Length: 0\n\n".to_vec(),
        Expect::Explained(T_BARE_LF),
    );
    add(
        "LF after only one field line",
        cat(&[ok, b"A: 1\nB: 2\r\n\r\n"]),
        Expect::Explained(T_BARE_LF),
    );
    add(
        "LF ending the status line",
        b"HTTP/1.1 200 OK\nA: 1\r\n\r\n".to_vec(),
        Expect::Explained(T_BARE_LF),
    );
    add(
        "an empty line before the status line",
        cat(&[b"\r\n", ok, b"\r\n"]),
        Expect::Explained(T_LEADING),
    );
    add(
        "two empty lines before the status line",
        cat(&[b"\r\n\r\n", ok, b"\r\n"]),
        Expect::Explained(T_LEADING),
    );
    add(
        "no SP after the status code",
        b"HTTP/1.1 301\r\nLocation: /\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "HTTP/1.2",
        b"HTTP/1.2 200 OK\r\n\r\n".to_vec(),
        Expect::Explained(T_VERSION),
    );
    add(
        "HTTP/2.0 over HTTP/1",
        b"HTTP/2.0 200 OK\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "HTTP/0.9",
        b"HTTP/0.9 200 OK\r\n\r\n".to_vec(),
        Expect::Agree,
    );
    add(
        "HTTP/1.2",
        b"HTTP/1.2 200 OK\r\n\r\n".to_vec(),
        Expect::Explained(T_VERSION),
    );
    add(
        "an obs-fold",
        cat(&[ok, b"X: a\r\n b\r\n\r\n"]),
        Expect::Explained(T_FOLD),
    );
    add(
        "an obs-fold with a tab, after a value with trailing whitespace",
        cat(&[ok, b"X: a \r\n\t  b\r\n\r\n"]),
        Expect::Explained(T_FOLD),
    );
    add(
        "an obs-fold on an empty first value",
        cat(&[ok, b"X:\r\n  v\r\n\r\n"]),
        Expect::Explained(T_FOLD),
    );
    let mut many = ok.to_vec();
    many.extend_from_slice(&b"A: 1\r\n".repeat(256));
    many.extend_from_slice(b"\r\n");
    add("256 field lines, our limit", many, Expect::Agree);
    let mut too_many = ok.to_vec();
    too_many.extend_from_slice(&b"A: 1\r\n".repeat(257));
    too_many.extend_from_slice(b"\r\n");
    add("257 field lines", too_many, Expect::Explained(T_LIMIT));
    let mut long_ok = cat(&[ok, b"X: "]);
    long_ok.extend_from_slice(&[b'a'; 8192usize.saturating_sub(3)]);
    long_ok.extend_from_slice(b"\r\n\r\n");
    add("a field line of 8192 octets", long_ok, Expect::Agree);
    let mut long = cat(&[ok, b"X: "]);
    long.extend_from_slice(&[b'a'; 8200]);
    long.extend_from_slice(b"\r\n\r\n");
    add(
        "a field line past 8192 octets",
        long,
        Expect::Explained(T_LIMIT),
    );
    add(
        "a bad value octet on a line that is not yet ended",
        cat(&[ok, b"X: a\x01"]),
        Expect::Explained(T_TIMING),
    );
    add(
        "a bad value octet on the last line, ended but not followed by another",
        cat(&[ok, b"X: a\x01\r\n"]),
        Expect::Explained(T_TIMING),
    );
    add(
        "a version that is wrong before its line ends",
        b"HTTX/1.1 2".to_vec(),
        Expect::Explained(T_TIMING),
    );
    v
}

#[test]
fn differential_handcrafted_heads() {
    let cases = handcrafted();
    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut fail = 0usize;
    for (label, input, want) in &cases {
        let got = judge(input, 0);
        let ok = match (&got, want) {
            (Verdict::Agree(_), Expect::Agree) => {
                pass = pass.saturating_add(1);
                true
            }
            (Verdict::Explained(a), Expect::Explained(b)) if a == b => {
                xfail = xfail.saturating_add(1);
                true
            }
            _ => false,
        };
        if !ok {
            fail = fail.saturating_add(1);
            println!("FAIL {label}: {got:?}\n  input {:?}", show(input));
        }
    }
    summary(
        "httparse differential: handcrafted heads",
        pass,
        xfail,
        fail,
        cases.len(),
    );
    assert_eq!(fail, 0);
}

// ---------------------------------------------------------------------------
// Suite 7: framing by construction.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Length,
    Chunked,
    Close,
    NoBody,
}

/// A message framed from a body known beforehand.
struct Framed {
    msg: Vec<u8>,
    /// Octets after the message (never part of it).
    extra: Vec<u8>,
    request_is_head: bool,
    status: u16,
    fields: Vec<(Vec<u8>, Vec<u8>)>,
    body: Vec<u8>,
    kind: Kind,
}

fn random_bytes(r: &mut Rng, most: usize) -> Vec<u8> {
    let n = r.below(most.saturating_add(1));
    (0..n).map(|_| r.byte()).collect()
}

/// The chunked coding of `body`, with every freedom RFC 9112 7.1 gives.
fn chunk_wire(r: &mut Rng, body: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut rest = body;
    while !rest.is_empty() {
        let most = rest.len().min(if r.chance(10) { 200 } else { 40 });
        let size = r.below(most).saturating_add(1);
        let (data, tail) = rest.split_at(size);
        rest = tail;
        let hex = if r.chance(2) {
            format!("{size:x}")
        } else {
            format!("{size:X}")
        };
        out.extend_from_slice(&vec![b'0'; r.below(4)]);
        out.extend_from_slice(hex.as_bytes());
        if r.chance(4) {
            out.extend_from_slice(r.pick(
                &[&b";a=b"[..], b" ; x = \"y\"", b";n", b"\t;k=v;j;l=\"q;r\""],
                b";n",
            ));
        }
        out.extend_from_slice(b"\r\n");
        out.extend_from_slice(data);
        out.extend_from_slice(b"\r\n");
    }
    out.extend_from_slice(&vec![b'0'; r.below(3).saturating_add(1)]);
    if r.chance(4) {
        out.extend_from_slice(b";done");
    }
    out.extend_from_slice(b"\r\n");
    for i in 0..r.below(3) {
        out.extend_from_slice(format!("X-Trailer-{i}: ").as_bytes());
        out.extend_from_slice(&field_value(r));
        out.extend_from_slice(b"\r\n");
    }
    out.extend_from_slice(b"\r\n");
    out
}

fn framed(r: &mut Rng, kind: Kind) -> Framed {
    let request_is_head = kind == Kind::NoBody && r.chance(2);
    let status = if kind == Kind::NoBody && !request_is_head {
        r.pick(&[100u16, 101, 199, 204, 304], 204)
    } else {
        r.pick(&[200u16, 201, 206, 301, 302, 400, 404, 500, 503], 200)
    };
    let mut fields: Vec<(Vec<u8>, Vec<u8>)> = (0..r.below(4))
        .map(|i| (format!("X-Field-{i}").into_bytes(), field_value(r)))
        .collect();
    let body = match kind {
        Kind::Length | Kind::Chunked => random_bytes(r, 300),
        Kind::Close => random_bytes(r, 200),
        Kind::NoBody => Vec::new(),
    };
    let mut wire_body = Vec::new();
    let mut framing: Option<(Vec<u8>, Vec<u8>)> = None;
    match kind {
        Kind::Length => {
            let zeros = "0".repeat(r.below(4));
            framing = Some((
                r.pick(
                    &[&b"Content-Length"[..], b"content-length", b"CONTENT-LENGTH"],
                    b"Content-Length",
                )
                .to_vec(),
                format!("{zeros}{}", body.len()).into_bytes(),
            ));
            wire_body.extend_from_slice(&body);
        }
        Kind::Chunked => {
            framing = Some((
                r.pick(
                    &[
                        &b"Transfer-Encoding"[..],
                        b"transfer-encoding",
                        b"TRANSFER-ENCODING",
                    ],
                    b"Transfer-Encoding",
                )
                .to_vec(),
                r.pick(&[&b"chunked"[..], b"Chunked", b"CHUNKED"], b"chunked")
                    .to_vec(),
            ));
            wire_body.extend_from_slice(&chunk_wire(r, &body));
        }
        Kind::Close => wire_body.extend_from_slice(&body),
        Kind::NoBody => {
            // A length or a coding that would give a body, unless the status or HEAD says none.
            if r.chance(2) {
                framing = Some((b"Content-Length".to_vec(), b"7".to_vec()));
            } else if request_is_head && r.chance(2) {
                framing = Some((b"Transfer-Encoding".to_vec(), b"chunked".to_vec()));
            }
        }
    }
    if let Some(f) = framing {
        let at = r.below(fields.len().saturating_add(1));
        fields.insert(at, f);
    }
    let mut msg = format!("HTTP/1.1 {status} Reason\r\n").into_bytes();
    for (n, v) in &fields {
        msg.extend_from_slice(n);
        msg.push(b':');
        msg.extend_from_slice(&ows(r, 2));
        msg.extend_from_slice(v);
        msg.extend_from_slice(&ows(r, 2));
        msg.extend_from_slice(b"\r\n");
    }
    msg.extend_from_slice(b"\r\n");
    msg.extend_from_slice(&wire_body);
    let extra = if kind == Kind::Close {
        Vec::new()
    } else {
        random_bytes(r, 10)
    };
    Framed {
        msg,
        extra,
        request_is_head,
        status,
        fields,
        body,
        kind,
    }
}

fn check_framed(r: &mut Rng, f: &Framed) -> Result<(), String> {
    let mut input = f.msg.clone();
    input.extend_from_slice(&f.extra);
    let open = parse_response_exec(&input, f.request_is_head);
    let closed = parse_response_at_close_exec(&input, f.request_is_head);
    let done = if f.kind == Kind::Close {
        if open != ParseBuf::Incomplete {
            return Err(format!(
                "close-delimited: expected Incomplete, got {open:?}"
            ));
        }
        &closed
    } else {
        &open
    };
    let ParseBuf::Done { response, rest } = done else {
        return Err(format!("expected a finished response, got {done:?}"));
    };
    if response.status_line.status != f.status {
        return Err(format!(
            "status {} (wrote {})",
            response.status_line.status, f.status
        ));
    }
    let got: Vec<(Vec<u8>, Vec<u8>)> = response
        .fields
        .iter()
        .map(|x| (x.name.clone(), x.value.clone()))
        .collect();
    if got != f.fields {
        return Err(format!(
            "fields [{}] (wrote [{}])",
            describe_fields(&got),
            describe_fields(&f.fields)
        ));
    }
    if response.body != f.body {
        return Err(format!(
            "body of {} octets (wrote {})",
            response.body.len(),
            f.body.len()
        ));
    }
    if rest != &f.extra {
        return Err(format!(
            "rest {:?} (extra {:?})",
            show(rest),
            show(&f.extra)
        ));
    }
    // Nothing is decided before the bytes that justify it: every proper
    // prefix of a length- or chunk-framed message is incomplete, and an
    // error when the connection closes.
    if matches!(f.kind, Kind::Length | Kind::Chunked) {
        for _ in 0..3 {
            let cut = r.below(f.msg.len());
            let prefix = f.msg.get(..cut).unwrap_or(&[]);
            let p = parse_response_exec(prefix, f.request_is_head);
            let c = parse_response_at_close_exec(prefix, f.request_is_head);
            if p != ParseBuf::Incomplete || c != ParseBuf::Invalid {
                return Err(format!(
                    "the first {cut} of {} octets: {p:?}, at close {c:?}",
                    f.msg.len()
                ));
            }
        }
    }
    let step = if r.chance(20) {
        1
    } else {
        r.pick(&[2usize, 3, 7, 16, 64], 7)
    };
    pieces_agree(&input, f.request_is_head, step)
}

#[test]
fn framing_by_construction() {
    let mut r = Rng(0xA076_1D64_78BD_642F);
    let mut fail = 0usize;
    let mut per_kind: BTreeMap<String, usize> = BTreeMap::new();
    for round in 0..FRAMING_ROUNDS {
        let kind = r.pick(
            &[Kind::Length, Kind::Chunked, Kind::Close, Kind::NoBody],
            Kind::Length,
        );
        let f = framed(&mut r, kind);
        bump(&mut per_kind, &format!("{kind:?}"));
        if let Err(e) = check_framed(&mut r, &f) {
            fail = fail.saturating_add(1);
            if fail <= 10 {
                println!(
                    "FAIL round {round} ({kind:?}): {e}\n  message {:?} + extra {:?}",
                    show(&f.msg),
                    show(&f.extra)
                );
            }
        }
    }
    print_counts("messages per framing", &per_kind);
    summary(
        "framing by construction: random bodies",
        FRAMING_ROUNDS.saturating_sub(fail),
        0,
        fail,
        FRAMING_ROUNDS,
    );
    assert_eq!(fail, 0);
}
