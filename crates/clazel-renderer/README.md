# clazel-renderer

The renderer process. Its first act is to enter the OS sandbox
(`sandbox::enter`, Phase 2), before it reads a byte. Then it takes the
documents the kernel commits to it (`Commit`, `Body` frames, `BodyEnd`;
phase-4.md item 4.12): a user script (kind 1) runs as in Phase 2, and a
document (kind 0) goes through the document pipeline of phase-4.md item 4.13
and is sent back as one `Display`.

Tier 0: tests only. The pipeline is glue; every step that reads the page's
bytes is a function of the crate that proves it, at that crate's own tier.

## The document pipeline (`src/pipeline.rs`)

| Step | Function | Crate, item |
|------|----------|-------------|
| Content type | parse a MIME type from bytes, then the MIME type sniffing algorithm with it as the supplied type | `clazel-mime`, Phase 1 |
| Encoding | the encoding sniffing algorithm (BOM, transport `charset`, prescan of 1024 bytes, windows-1252) | `clazel-html` `sniff/`, 4.2 |
| Decoding | Encoding §6 "decode" (UTF-8, the single-byte encodings, UTF-16, replacement, x-user-defined) | `clazel-encoding`, 4.3 |
| Parsing | preprocessing, the tokenizer and the tree builder (`exec::driver::parse_real`) | `clazel-html`, `clazel-treebuilder`, 4.7, 4.10 |
| Change the encoding | on the parser's first `ChangeEncoding`: §13.2.3.4, then decode and parse once more, confidence certain | `clazel-html` `sniff/`, 4.2 |
| Links | the document base URL (first `<base href>`), each `<a href>` and `<iframe src>` parsed against it; one that fails is not a link | `clazel-url`, Phase 1 |
| Layout | title, lines of the terminal's width, numbered links | `clazel-text`, 4.14 (tier 0) |

`text/plain` is decoded with the same sniff and shown as one preformatted
block; any other type shows "`<type>` is not shown" with the URL; an encoding
with no decoder here (the multi-byte ones, item 4.4) shows "encoding `<name>`
is not supported" and no links. The modelling choices are listed at the top
of `src/pipeline.rs`.

The host passes the terminal width as `--width N` (default 80).

## What is checked, and how

- `tests/pipeline.rs`: one test per rule (title, text and resolved links;
  `<base href>`; an unparsable `href`; sniffing an absent or unknown type;
  `text/plain`; other types; transport encoding, BOM and prescan; the
  restart; an encoding without a decoder; the `<meta content>` mapping; the
  display limit; hostile bytes never panic).
- `tests/conformance_encoding.rs`: every html5lib-tests `encoding/*.dat`
  case through the pipeline's HTML path, the restart included: the seven
  cases `clazel-html`'s sniffer test lists as needing the parser's restart
  pass here.
- `crates/clazel/tests/browse.rs`: `clazel browse` against an in-process
  server through the real sandboxed renderer, following a link it parsed.

## The display limit

A `Display` must fit one frame (`MAX_FRAME`, 1 MiB). A page whose title,
text and links are larger is cut: the title to 1024 characters, the links to
a quarter of the frame, the text at a line to the rest, and its last line
says how much was kept.

## Memory

The renderer is single-threaded and allocates in proportion to the body.
With `B` the body's bytes (at most 64 MiB, `MAX_BODY`, checked as the
`Body` frames arrive), `N` the nodes of the tree (at most
`clazel_dom::exec::MAX_NODES` = 4,000,000):

| Term | Bound | At the limits |
|------|-------|---------------|
| The body | `B` | 64 MiB |
| Decoded input (every decoder gives at most one code point per byte) | `4·B` | 256 MiB |
| The preprocessed copy the driver tokenizes | `4·B` | 256 MiB |
| Node records (`ExecNode`, 168 bytes, checked by a test) and child lists | `176·N` | 671 MiB |
| Text node data (each input code point is in at most one `Text` node) | `4·B` | 256 MiB |
| Attributes | see below | not bounded by `B` |
| The page (`clazel-text`'s bound: `2·(T + A) + 162·N` characters) | at most 4 bytes each | see below |
| The `Display` frame | 1 MiB | 1 MiB |

The first parse's tree and input are freed before a restart builds the
second, so the parser's terms count once.

What this does not bound, stated plainly: the tree builder copies an
element's attributes each time it reconstructs the active formatting
elements or runs the adoption agency, so attribute storage grows with the
number of copies (at most `N`) times the largest attribute list, not with
`B`; and the page's text is bounded by `T + A + N`, not by `B` alone. Both
are capped by `MAX_NODES` but the cap is large (gigabytes in the worst
case). Phase 4 item 4.16 measures the hostile pages against these terms;
until it does, the numbers above are the arithmetic, not a measurement.
