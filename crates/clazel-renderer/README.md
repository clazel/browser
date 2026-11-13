# clazel-renderer

The renderer process. Its first act is to enter the OS sandbox
(`sandbox::enter`, Phase 2), before it reads a byte. Then it takes the
documents the kernel commits to it (`Commit`, `Body` frames, `BodyEnd`;
phase-4.md item 4.12): a user script (kind 1) runs as in Phase 2, and a
document (kind 0) goes through the document pipeline of phase-4.md item 4.13
and is sent back as one `Display`.

Tier 0: tests only. The pipeline is glue; every step that reads the page's
bytes is a function of the crate that proves it, at that crate's own tier.

## The GPU process's list socket (item 5.23), for item 5.20

The host starts a renderer paired with a GPU process (`launch::Gpus`,
`launch::spawn_with_list`) with `--list-fd N`: a socket inherited by number
(its close-on-exec flag cleared for that one start, through `clazel-sys`). Item
5.20's renderer is to open it again through `/dev/fd/N` **before** entering its
sandbox, and write each display list with `clazel_gpu::channel::write_list` (4
bytes of length, little-endian, then the list as `clazel_displaylist` encodes it,
at most 256 MiB). The kernel's `Viewport` gives the size to lay out at; the GPU
process draws every list in order at the size its `GpuViewport` gives. In text
mode (no GPU process) no `--list-fd` is passed. Only macOS has this so far.

`launch` also holds the host's side of the GPU processes (`Gpus`: start, reader
threads, the ring of pixels, ending with the renderer) and the log's rendering of a
frame (`describe`), so that the host shell (`crates/clazel/src`) only routes and
stays under its 300 lines.

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
case).

Measured (Phase 4 item 4.16, `crates/clazel/tests/hostile_pages.rs`):
each hostile page is loaded into a real sandboxed renderer, and its peak
resident set (`VmHWM` on Linux, sampled with `ps` on macOS) is checked
against these terms for the page's `B`, `N` and attributes, plus 16 MiB for
the process itself. On macOS arm64, debug build: 64 MiB of words, 1,007
MiB of a 1,361 MiB bound; 64 MiB of `&amp;` (an ignored test), 675 MiB;
a page cut at `MAX_NODES`, 1,327 of 3,480 MiB; the active formatting list
reconstructed 2,000 times (604,305 nodes from 18,977 bytes, 57 MiB of
attribute copies), 335 of 571 MiB; every other page under 20 MiB.

## The graphical pipeline (phase-5.md item 5.20)

`src/page/`, beside item 4.13's text path (`pipeline.rs`, `Display`), which
stays as it is until item 5.26 (item 5.18's decision). `run_graphics(r, w,
list, fonts)` reads the kernel's messages from `r`, sends `Title` and
`Navigate` to `w`, and writes display lists to `list`, the GPU process's
socket:

1. to 4. item 4.13's content type, encodings, parse and base URL;
   `text/plain` becomes one `pre` block and any other type a drawn notice;
5. the style sources in tree order (item 5.8): `style` elements, links and
   `style` attributes;
6. the wait for linked sheets (`page/sheets.rs`): the seam for item 5.19.
   Today every pending link fails at once, so pages render with their
   `style` elements and attributes and the user agent sheet;
7. to 10. the cascade (5.7) for the viewport in CSS pixels, boxes (5.13),
   layout at the viewport's width (5.14, 5.15) in the fonts read before the
   sandbox, paint (5.16) at the viewport's scale;
11. per frame (`page/frame.rs`): the items that meet the viewport at the
    scroll offset, offset by it, the glyph masks (5.17) the GPU process does
    not hold yet, encoded (5.17a) and written as a 4-byte big-endian length
    and the list;
12. `Title` when the title changes.

`Viewport` lays out and paints again; `Input` scrolls (clamped to the page)
and paints again, or hit-tests a click against the links' regions and sends
`Navigate`; a key does nothing yet. `src/page/mod.rs` lists every modelling
choice; `src/page/state.rs` states each state and contract.

### Decisions taken for 5.20

- **A sibling module, not `pipeline.rs` itself**: the text path stays whole
  for Phases 2 to 4's tests, and `page/` calls its steps 1 to 4.
- **Fonts**: `--font PATH` arguments, read in `main.rs` before the sandbox
  is entered; the first face of each file; the bytes live for the process.
  With no face, layout uses em boxes and no text is drawn.
- **`text/plain` and notices** are made into HTML documents (`<pre>` and
  `<p>`, escaped) and drawn by the same pipeline with the user agent sheet.
- **The viewport**: at most 8,192 device pixels a side (the GPU process's
  limit); scale 2, or 1 for any other value; the CSS viewport is the device
  one divided by the scale. Nothing is painted before a viewport, or for a 0
  by 0 one.
- **The title** is `document.title` (the first `title`, stripped and
  collapsed), at most 1,024 characters, sent when it differs from the last
  one sent.
- **Scroll** is vertical, clamped to the page's height; a click goes to the
  topmost link region; a key does nothing.
- **Masks** stay live in the GPU process across lists under ids the
  renderer gives, within 5.17a's limits (65,536 masks, 64 MiB): uploaded
  once, freed only when a frame's new masks would pass a limit; a frame's
  fills, clips and glyphs are capped at half of 5.17a's item limit, its
  clip kept balanced.
- **The socket's framing** (a 4-byte big-endian length, then a list) is
  ours; the GPU process's reader is not built yet.

### What waits

- **The list socket**: the host must create a socket pair at the GPU
  spawn and hand the renderer its end; adopting an inherited descriptor and
  clearing its close-on-exec flag needs a new audited `clazel-sys` call
  (phase-5.md, item 5.18's plan), outside this item. Until then the binary
  runs the text path, and `run_graphics` is exercised by the tests with
  in-memory sockets.
- **Linked style sheets**: item 5.19's `FetchStyle` and `Style*` messages.
  Wiring them is `SheetWait::start` with fetches, a request per pending
  index, `SheetWait::answer` per reply, and rendering once ready.
- **The GPU process's list reader** (it decodes and validates; the framing
  above is what it will read).

### Memory (item 5.20's terms, added to 4.13's above)

Sizes measured on this build (aarch64, `std::mem::size_of`): a computed
style 432 bytes, a box 120, a box fragment 96 (`Option` adds 8), a line box
56, a placed glyph 24, a paint item 56, a 5.17a item 32, a style sheet
source 216. With `N` nodes and `M` boxes (item 5.13 makes at most a
principal box, a marker and wrappers per node; 5.26 measures `M`):

| Term | Bound | At `N` = 4,000,000 |
|------|-------|--------------------|
| Style sheets (`style` element text is in the tree, counted above; parsed rules) | in proportion to their text | not separately bounded |
| Linked sheets (item 5.19) | the body limit each, times 5.19's per-document count | waits for 5.19 |
| The computed table (one record per node) | `432·N` | 1.7 GB |
| Each box's style while laying out and painting (`flow::style::box_styles`, made by each pass) | `432·M` | `M` boxes |
| The box tree, fragments and layout state | about `350·M` | `M` boxes |
| Glyphs (one per character, in shaping, lines and paint) | `24·C` per copy, three copies | `C` characters ≤ the text's |
| The display list | `56` per item, at most one background, four border strips, three decorations and a text item per box or run | in proportion to `M` and runs |
| One frame's 5.17a items | at most 524,288 draws (32 bytes) and the new masks | 16 MiB and at most 64 MiB of coverage |

Only the display list is kept between frames (with the document tree, the
style sources and the mask table); the computed table, boxes and fragments
are dropped once a viewport's list is painted. None of this is measured yet:
item 5.26's hostile pages measure it, as 4.16's did for the text path.
