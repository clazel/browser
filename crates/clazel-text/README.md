# clazel-text

The text layout for Clazel's Phase 4 browser: a parsed document to its
title, its text as lines of at most a given width, and a numbered list of
its links. Part of [Clazel](../../README.md), a web browser whose parsers
of untrusted input carry machine-checked proofs.

This crate parses nothing. It reads the arena that `clazel-treebuilder`
builds (`clazel-dom`'s `exec::Arena`) and is replaced by CSS layout in
Phase 5.

## What it is

One pure function, `layout(doc, width) -> Page { title, lines, links }`,
and `layout_with(doc, width, resolve)`, which takes the URL resolver of
Phase 4 item 4.13: an `a href` or `iframe src` value is a link only when
`resolve` returns `Some(url)`, and `links` lists that URL. `layout` records
the raw attribute value. Every rule is cited where a standard has one and
marked ours where it does not; the full list of modelling choices is at the
top of `src/lib.rs`.

- **Hidden** (HTML §15.3.1): `area`, `base`, `basefont`, `datalist`,
  `head`, `link`, `meta`, `noembed`, `noframes`, `param`, `rp`, `script`,
  `style`, `template`, `title`; any element with `hidden`;
  `input type=hidden`; a `dialog` without `open` (§15.3.3). `noscript` is
  shown (scripting is off). The first `title` is `Page.title` (§3.1.3
  `document.title`).
- **Blocks** (§15.3.2, §15.3.3, §15.3.6, §15.3.7, §15.3.8; the element
  lists are quoted in the code) start a new line; `p` and `h1` to `h6` have
  one empty line around them (ours). Everything else is inline.
- **Text**: ASCII whitespace collapses to one space and is trimmed at line
  edges (ours, CSS is Phase 5), except in `pre`, `listing`, `plaintext`,
  `xmp` (§15.3.3) and `textarea` (§15.3.10); `br` breaks the line.
- **Lists, rules, tables** (ours): `* ` or `N. ` before an `li`; `hr` is
  `min(width, 80)` hyphens; table rows are lines and cells are separated by
  two spaces, as Lynx does.
- **Links and images** (ours, as Lynx): `[n]` after each link, `n` its
  1-based index in `links`; an `iframe` is its `[n]` only; `img` is
  `[alt]`, `[image]` without `alt`, nothing with `alt=""`.
- **Wrapping** at `width` columns on spaces; a longer word, and
  preformatted text, is broken at the width. **Width 0 means no
  wrapping.** Every scalar value is one column.
- **Printable output** (ours): surrogates and control characters other than
  ASCII whitespace become U+FFFD, so the result can go to a terminal.

Not modelled: CSS of any kind (margins, indentation, alignment, columns of
tables, `display` set by the page), East Asian width, combining marks and
bidirectional text (Phase 5), images (Phase 6), forms beyond their text,
nested browsing contexts (an `iframe` is a link), `ol`'s `start`,
`reversed` and `li`'s `value`, `details`/`summary` and `fieldset`
rendering, and SVG and MathML rendering (their text is shown inline,
except `script` and `style`).

## The bound

With `T` the code points of every `Text` node, `A` those of every `img`'s
`alt`, and `N` the arena's nodes, for every width:

- `title + Σ line ≤ T + A + 80 · N` scalar values (`PER_NODE_CHARS`; an
  `hr` is the largest addition, a list or link marker at most 22);
- `lines.len() ≤ T + A + 82 · N` (`PER_NODE_LINES`).

The argument is in the crate docs (`src/lib.rs`, "The bound"). It is
checked, not proven.

## Verification

Tier 0, the policy's tier for layout: tests only. No panics by
construction as far as the workspace lints reach (no indexing, no
unchecked arithmetic, no `unwrap`), not by proof. The walk is iterative
and visits at most `arena.len()` nodes, so neither a deep tree nor a
malformed arena can overflow the stack or loop.

- **Unit tests** (`src/tests.rs`, 30): at least one per rule above, on
  documents built by the real parser, plus width 0 and 1, an empty
  document, and a million nested `div`s.
- **Golden test** (`tests/golden.rs`): the 1,761 document cases of the
  html5lib tree-construction suite (vendored in `clazel-treebuilder`) are
  parsed by `exec::driver::parse_real` with scripting off and laid out at
  width 80; the output is compared byte for byte with `tests/golden/*.txt`,
  one file per `.dat`. The 206 `#document-fragment` cases and the 6
  scripted cases are not laid out. `CLAZEL_BLESS=1 cargo test -p
  clazel-text --test golden` regenerates the fixtures; review the diff.
- **Bound** (`tests/bound.rs`, and every golden case): both inequalities,
  and no line longer than a non-zero width, on 400 generated tag-soup
  documents at widths 0, 1, 2, 3, 7, 40, 80 and 200.

## Left

Item 4.16's hostile pages (the bound measured on large inputs), a Kani
harness over bounded documents (welcome, not required), and wiring into
the renderer (4.13) and `clazel browse` (4.15).

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
