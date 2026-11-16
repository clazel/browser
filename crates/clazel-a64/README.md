# clazel-a64

Part of [Clazel](../../README.md). The A64 (64-bit Arm) subset the JIT emits:
its semantics, encoder and decoder ([jit.md](../../docs/phases/jit.md) item
J.4).

Nothing is implemented yet (tier 0, target tier 2). Item J.2 vendored or
pinned the sources the semantics will be written against, in `tests/data/`:

| Suite | What | Held as |
|---|---|---|
| `sail-arm` | the Sail Armv9.4-A model: A64 base instructions and shared pseudocode (BSD-3-Clause-Clear) | 3.9 MB, vendored |
| `arm-mrs` | Arm's machine-readable specification, 2026-09 release (BSD-3-Clause) | licence and README vendored; `Instructions.json` (116,678,333 bytes) pinned by SHA-256 |

Each has a `SOURCE.md` with the upstream, the commit (or the SHA-256) and the
licence. The tables in `tests/generated/` list every file's size and hash.

## Are the two A64 sources independent? No.

The Sail Arm model's README says its Sail files "are derived from the 2023-03
version of Arm's ASL specification using the automatic ASL-to-Sail
translation tool". Arm's machine-readable specification (`Instructions.json`)
carries the same ASL as the operation of each instruction. So the two are one
source in two syntaxes (the Sail model is from the 2023-03 ASL, the JSON from
2026-09), and they share Arm's own errors, if any. jit.md items J.2 and J.4
say each semantics is transcribed from independent sources; for A64 no
second, independent formal source was found. The Arm Architecture Reference
Manual's prose and the hardware differential tests on the macOS runner (exit
criterion 3) are independent evidence; a person should decide whether the
second A64 transcription is made from the prose, and what the crate header
says.

The `arm-mrs` JSON is also the only machine-readable encoding table
(`Instructions.json` has every encoding with its fixed and variable bits), so
the decoder differential against `yaxpeax-arm` can be checked against it as
well.
