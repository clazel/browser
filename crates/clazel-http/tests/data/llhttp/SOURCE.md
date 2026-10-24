# `llhttp` response and framing fixtures

Upstream: https://github.com/nodejs/llhttp/tree/69936dbc22922e596a05dfa912fc11d9a7af2136/test
Commit: 69936dbc22922e596a05dfa912fc11d9a7af2136
License: MIT (Copyright 2018 Fedor Indutny; the upstream `LICENSE`, copied into `LICENSE.md`)

llhttp is Node.js's HTTP/1.x parser. Its tests are markdown files: a heading,
a `<!-- meta={...} -->` line, an ```` ```http ```` block (the input) and a
```` ```log ```` block (the events llhttp's test parser printed). The files
here are copied byte for byte from the repository's `test/` directory at
that commit (the most recent commit of `main` when they were vendored,
1 October 2026, "build(deps-dev): bump eslint from 10.2.1 to 10.4.1
(#859)"), from a fresh `git clone` of `https://github.com/nodejs/llhttp`
read through before they were copied. Their names here join the directory
and the file name with `-`, because `cargo xtask testdata` reads a flat
directory:

| Here | Upstream |
|------|----------|
| `response-connection.md`, `response-content-length.md`, `response-finish.md`, `response-invalid.md`, `response-lenient-version.md`, `response-pausing.md`, `response-pipelining.md`, `response-sample.md`, `response-transfer-encoding.md` | `test/response/*.md`: every file |
| `request-content-length.md`, `request-transfer-encoding.md` | `test/request/content-length.md` and `test/request/transfer-encoding.md` |

Not vendored: the rest of `test/request/` (request lines, methods, URIs,
`Connection`, pausing, pipelining: a browser never parses a request) and
`test/url.md`. The two request files are the cases of the framing rules
(`Content-Length`, chunked coding) that a client sees too: for a client the
test replaces the request line with a status line `HTTP/<version> 200 OK`
and runs the rest through the response parser.

To update, copy the same files from a newer commit, change the commit
above, and run `cargo xtask testdata`; the converter fails if the shape of
the markdown changed.

`xtask/src/testdata/llhttp.rs` converts them into
`tests/generated/llhttp.rs`, read by `tests/conformance_http.rs`. Each test
becomes a row with the input octets (read as upstream's `test/md-test.ts`
reads them), and what llhttp's log says: for each message its status,
version, header fields and body, and whether the log ends with an error.
A row's id is the file and the line of the test's heading (`response/sample.md:12`),
which is what upstream's own test names use. The test runs every row through
the proven parser and compares. Where llhttp is lenient by design, or a
request is not a response, the row is listed in the test as an expected
failure with its reason; none is counted as a pass.
