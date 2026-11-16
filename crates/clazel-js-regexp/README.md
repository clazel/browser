# clazel-js-regexp

Part of [Clazel](../../README.md). The ECMAScript pattern parser, the matcher
and the Unicode tables behind `\p{..}` and case folding
([phase-7.md](../../docs/phases/phase-7.md) item 7.10).

Nothing is implemented yet (tier 0, target tier 1). Item 7.1 vendored the
Unicode 18.0.0 files the tables will be generated from: see
`tests/data/ucd-regexp/SOURCE.md`.
