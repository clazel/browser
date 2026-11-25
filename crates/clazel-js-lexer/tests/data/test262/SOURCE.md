# Test262, the ECMAScript conformance suite (the syntax subset)

Upstream: https://github.com/tc39/test262
Commit: e91219cb6b87865703ce8619b5bc0f7c2bf608e1
License: BSD-3-Clause (`LICENSE.md`, the repository's `LICENSE`; each test file also carries its own copyright header, kept as it is)
Subset: from `test/language/`, every test whose frontmatter has `negative:` with phase `parse`, `early` or `resolution`, and every test under the lexical directories `asi`, `comments`, `directive-prologue`, `future-reserved-words`, `identifier-resolution`, `identifiers`, `keywords`, `line-terminators`, `literals`, `punctuators`, `reserved-words`, `source-text`, `statementList`, `types` and `white-space`; plus all of the generator and async function directories (items 7.7 to 7.9): `test/language/statements/` `generators`, `async-function` and `async-generator`, `test/language/expressions/` `generators`, `async-function`, `async-arrow-function`, `async-generator`, `await` and `yield`, and `test/built-ins/` `GeneratorPrototype`, `GeneratorFunction`, `AsyncFunction`, `AsyncGeneratorPrototype`, `AsyncGeneratorFunction`, `AsyncFromSyncIteratorPrototype` and `AsyncIteratorPrototype`; plus all of `test/built-ins/Date/` (item 7.9, `Date`); plus all of the directories of code compiled at run time (items 7.7 to 7.9): `test/built-ins/eval`, `test/language/eval-code`, `test/language/statements/with` and `test/built-ins/Function` but one file, `test/built-ins/Function/prototype/toString/line-terminator-normalisation-CR.js`, whose lines end in CR alone, which the table's frontmatter reader (`xtask/src/testdata/test262.rs`) does not read; plus every `*_FIXTURE.js` in a directory that holds a vendored test, all of `harness/`, and `features.txt`.

The commit is Test262's last before the pinned ECMA-262 2026 commit (2026-03-30; see
`SPEC-PIN.md` in the crate's root). Test262 has no edition tags.

The files are copied byte for byte, under the same paths as upstream (`test/language/...`,
`harness/...`, `features.txt`). `.gitattributes` stores them without line-ending conversion: some
tests use CR, CRLF and the Unicode line separators on purpose.

8,770 files, 12,720,866 bytes (LICENSE.md and SOURCE.md not counted): 8,560 tests (and their fixtures), `harness/` and `features.txt`.

What it is for: items 7.2 and 7.3 (the lexer and the parser) run the tests that parse or
fail to parse; the negative ones carry the early errors. The tests of the rest of
`test/language/` (positive ones in `expressions/` and `statements/`), the rest of `test/built-ins/`
and `test/annexB/` are not vendored: they join with the items that record their
results (phase-7.md 7.7 to 7.11). The Intl, Temporal, Atomics and SharedArrayBuffer
directories never will, by 7.0(b).

`xtask/src/testdata/test262.rs` converts it into `tests/generated/test262.rs`, one row per
test with its frontmatter (`flags`, `features`, `includes`, `negative`) and whether it is an
expected failure, with the reason: a feature excluded by 7.0(b), or newer than the edition
(263 tests). The table also holds a SHA-256 over every vendored file, so an edit to a
harness file or a fixture makes it stale. To update, copy the subset from a newer commit,
change the commit above, and run `cargo xtask testdata`.

This is an official suite (the language committee's own), so it is rule 7's evidence
for the lexer and the parser.
