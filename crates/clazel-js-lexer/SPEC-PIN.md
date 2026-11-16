# Pins for the JavaScript crates (phase-7.md item 7.1)

## The language spec: ECMA-262, 2026 edition

Upstream: https://github.com/tc39/ecma262
Edition: ES2026, tag `es2026` (an annotated tag, object `f7db29f16c5175a93f0d6e8fb27a8e3cb9b97a9e`, dated 2026-07-02)
Commit: 0248456c758431e4bb8e5d26333ff1865123c9cd
Commit date: 2026-03-31 (the `es2026-candidate-2026-03-31` tag is the same commit)
License: Ecma International's software and document licences (the text is not copied here)

**The spec text is not vendored.** Nothing reads it: the lexer's spec (item 7.2) is
transcribed by hand with the section and step numbers quoted (CLAUDE.md rule 5,
docs/SPEC-STYLE.md), and its header names this commit. A copy of `spec.html`
(about 3 MB, plus its Unicode property tables) would be a file no tool checks. Vendor
it, with a converter, only if a later item reads it (for example, to check the
transcribed grammar against the spec's own grammar productions).

The newer tag `es2026-errata` (`d89c03f2db8a597bc915b363a6518d0cc8acdbc0`) holds
editorial fixes made after publication. It is not the edition, so it is not the pin.

## Test262

Upstream: https://github.com/tc39/test262
Commit: e91219cb6b87865703ce8619b5bc0f7c2bf608e1
Commit date: 2026-03-30 (the last commit before the pinned ECMA-262 commit)
License: BSD-3-Clause (the repository's `LICENSE`)

Test262 has no edition tags. This is its last commit on or before the date of the
pinned ECMA-262 commit, so its tests for features that stage 4 had not reached then
are tagged with the proposal (`features.txt` lists them), and the converter marks
those as expected failures.

**Not vendored yet.** The tests item 7.0(b)'s scope needs are about 63 MB (measured
at this commit, below), over the 40 MB this item set as the limit. The converter
(`xtask/src/testdata/test262.rs`, registered as `test262`) is written and was run on a
trial copy of the subset proposed below; the data waits for a decision on the subset.
When it is vendored, it goes in `tests/data/test262/` with its own `SOURCE.md` and
`LICENSE.md`.

Sizes of the files in the repository at the pinned commit (bytes, files):

| Directory | Bytes | Files |
|---|---|---|
| `test/language/` (all) | 41,712,225 | 22,510 |
| `test/built-ins/` (all) | 24,888,741 | 23,482 |
| of which `Temporal/`, `Atomics/`, `SharedArrayBuffer/` (out of scope) | 5,617,163 | 5,062 |
| `test/intl402/` (out of scope) | 9,865,071 | 3,323 |
| `test/annexB/` | 1,468,085 | 1,086 |
| `src/` (the templates the generated tests come from; not needed) | 2,546,137 | 2,777 |
| `harness/` | 297,656 | 42 |
| everything the GitHub tree API listed (it truncates; `test/staging/` is not counted) | 81,453,206 | 53,366 |

In scope and vendored in full, about 63 MB (language 41.7, built-ins 19.3, annexB 1.5, harness 0.4): `language/`, `built-ins/` without the
three directories above, `annexB/`, `harness/`. The generated table would be
about 12 MB (225 bytes a test).

Proposed subset for items 7.2 and 7.3 (the lexer and the parser), measured:
`test/language/` tests that are `negative` at the `parse`, `early` or `resolution`
phase (4.7 MB), plus the lexical directories (`asi`, `comments`, `directive-prologue`,
`future-reserved-words`, `identifier-resolution`, `identifiers`, `keywords`,
`line-terminators`, `literals`, `punctuators`, `reserved-words`, `source-text`,
`statementList`, `types`, `white-space`), the `_FIXTURE` files beside them, `harness/`
and `features.txt`: 5,255 files, 8.7 MB, 5,212 tests (263 of them expected failures
as newer than the edition). The remaining directories join, each with the item that
records their results (phase-7.md 7.9: "each group lands with its Test262
directory's results recorded").
