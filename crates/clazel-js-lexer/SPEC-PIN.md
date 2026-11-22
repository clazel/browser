# The language spec pin (phase-7.md item 7.1)

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


Test262's pin is in `tests/data/test262/SOURCE.md`, with the subset vendored and why.
It is the last Test262 commit before the commit above.
