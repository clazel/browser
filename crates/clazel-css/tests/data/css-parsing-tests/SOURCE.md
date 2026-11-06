# `css-parsing-tests`, CSS Syntax parsing cases

Upstream: https://github.com/servo/rust-cssparser/tree/9f3ceddf398f5ce4ab76fdad1b42ccb6c578a926/src/css-parsing-tests
Commit: 9f3ceddf398f5ce4ab76fdad1b42ccb6c578a926
License: CC0-1.0 (`LICENSE.md`, the suite's `LICENSE` file; `rust-cssparser` itself is MPL-2.0, but this directory carries its own dedication)

The ten `.json` files are copied byte for byte from `src/css-parsing-tests/` at
that commit, and `LICENSE.md` is that directory's `LICENSE`. To update, copy the
files from a newer commit, change the commit above, and run `cargo xtask testdata`.

`xtask/src/testdata/css_parsing_tests.rs` converts them into
`tests/generated/css_parsing_tests.rs`, a table of 301 cases, all of them. The table
keeps the JSON values as they are. `tests/suite_table.rs` checks the table.
`tests/conformance_tokens.rs` runs `component_value_list.json` and
`one_component_value.json` against the tokenizer; item 5.4's conformance test will
run the rest, which need the parser.

**This is not an official suite.** The suite's README says it is based on the 2013
draft of CSS Syntax Level 3, though at least one case is newer (below), and it
records one parser's reading. Where a case
differs from the text item 5.2 pins, the spec decides, and the case is listed as an
expected failure with the reason. Rule 7's official evidence is WPT's `css/css-syntax/`.

The converter checks every value against the README, so a changed file fails the
conversion. The files differ from the README in three ways, and the converter
follows the files:

- `stylesheet_bytes.json`'s results are `[rules, encoding name]`, not just the rules.
- `urange.json`'s inputs are comma-separated, so each result is a list with one entry
  per range, each `null` or `[start, end]`.
- `declaration_list.json`'s last case has a qualified rule in the list, which the
  README does not allow. It is what nested rules need, so that file has been
  changed since the 2013 draft.

Not vendored, for now: `color3*.json` and `color4*.json`, which belong to item 5.6
and are most of the directory's size; the `make_color*.py` scripts that generate
some of them; and `README.rst`.
