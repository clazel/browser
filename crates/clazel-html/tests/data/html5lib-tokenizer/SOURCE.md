# html5lib-tests `tokenizer/`: every tokenizer case

Upstream: https://github.com/html5lib/html5lib-tests/tree/c777c408b61078ea2eb4acefc2535f54dbc8b28a/tokenizer
Commit: c777c408b61078ea2eb4acefc2535f54dbc8b28a
Date: 2026-10-01 ("Add tokenizer tests for processing instructions")
License: MIT (`LICENSE.md`, copied from `LICENSE` at the root of the repository at that commit)

Files, copied byte for byte from `tokenizer/` at that commit, with their
SHA-256:

| File | SHA-256 |
|------|---------|
| `README.md` | 248e7c2d2be32a98d59108f53f78bd6b6d2eb8da15d3b50a2602abd67c779b90 |
| `contentModelFlags.test` | 77784a505a528950761cfb3c76617afade28b27c3be2a8c37dce3c3d8988391d |
| `domjs.test` | 3273e7861bbdb094571e4b0813ffdd934fe2bfd65864600fef62e8e3b807131a |
| `entities.test` | fe17483810a00247579f5f129ca9c007fbab6755ba839523e29aa9f8875f4085 |
| `escapeFlag.test` | edbd2e070a14fc67f6bbc104e50207f0fe206a21891c260deea3d227b32c93c9 |
| `namedEntities.test` | a7f0e59ff7653820330548776cb3031c18e45f5fd1481a9813d9c7acee89bd6e |
| `numericEntities.test` | 679296c976252322ece27e2b113a5358a0aa3b0b8ecd2d6d9b365f9d1b0f9632 |
| `pendingSpecChanges.test` | 6b56d81ca09afa47d8cb0f33e3fb7169010c3a64493e608ebec921ac098ff8e9 |
| `test1.test` | 524fcfa4d561a14f0c4e72e0573549abe6341fd4dfb8e16bc2dcf59a608a7219 |
| `test2.test` | f0e2bf7d21de13a8e930d350d0a5ad364e2546ce9ca8e938ab8cb63a5bbe417d |
| `test3.test` | 87817f985e6b137562b6f50c1b92b65db63514f800426b5e42b0d184ca59e846 |
| `test4.test` | c4967118aecbf8eb2ca34d5c5306f536614acca03e58610f75fbd9efa89fbb42 |
| `unicodeChars.test` | 22b7263a840da38179b13693bbfe72f0507dcd41951622456a0d3f5300ba42bd |
| `unicodeCharsProblematic.test` | 3c166d5cfa24ee60fd7310ff0f5057e4ae0c649842ec446b5949215759e19a68 |
| `xmlViolation.test` | 193a2f52d81adb4df4e056e3489f3bae79b3fc65253ccf31423a0e2f9c128d5c |
| `LICENSE.md` (from `LICENSE`) | ff512aac9ef231d504be5afaf4429005024e4b2aaf257be39524f37b8402aaf2 |

To update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/html5lib_tokenizer.rs` converts the cases into
`tests/generated/html5lib_tokenizer.rs`, read by
`tests/conformance_tokenizer.rs`. `README.md` is vendored because it says
what a case means (preprocessing before tokenizing, `doubleEscaped`,
`initialStates`, `lastStartTag`, coalesced character tokens); the converter
fails if those lines change. Its token list still shows
`["ProcessingInstruction", data]`, while the cases (added with the living
standard's processing instruction states) carry the target and the data,
three entries, which is what the converter reads.

**Converted:** every case of every file (6,827 cases), each run once per
initial state it names. **Ignored:** the `errors` arrays, since parse
errors are not modelled (Phase 4 item 4.6). The four `xmlViolation.test`
cases expect the "coercing an HTML DOM into an infoset" tweaks on top of
tokenization, which this crate does not implement; they are run and
counted as expected failures if their output differs, never as passes.

The tree construction tests, which html5lib-tests no longer carries (its
README at this commit says they are maintained in WPT
`html/syntax/parsing`), are not vendored here.
