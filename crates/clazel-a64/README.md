# clazel-a64

Part of [Clazel](../../README.md). The A64 (64-bit Arm) subset the JIT emits:
its semantics, encoder and decoder ([jit.md](../../docs/phases/jit.md) item
J.4).

The primary spec (`src/spec.rs`, from the Sail Arm model) is written; no encoder or decoder exists yet (tier 0, target tier 2). Item J.2 vendored or
pinned the sources the semantics will be written against, in `tests/data/`:

| Suite | What | Held as |
|---|---|---|
| `sail-arm` | the Sail Armv9.4-A model: A64 base instructions and shared pseudocode (BSD-3-Clause-Clear) | 3.9 MB, vendored |
| `arm-mrs` | Arm's machine-readable specification, 2026-09 release (BSD-3-Clause) | licence and README vendored; `Instructions.json` (116,678,333 bytes) pinned by SHA-256 |
| `arm-arm` | Arm Architecture Reference Manual for A-profile (DDI 0487), issue M.d | pinned by URL, size (129,014,701 bytes) and SHA-256, not vendored (Arm's terms forbid copying) |

Each has a `SOURCE.md` with the upstream, the commit (or the SHA-256) and the
licence. The tables in `tests/generated/` list every file's size and hash.

## Where the transcriptions come from

Decided by the user on 2026-11-16 (jit.md, the note under J.4):

- The **primary spec** is transcribed from the Sail Arm model and Arm's ASL.
- The **independent transcription** is made from the Arm Architecture
  Reference Manual's prose, by a **different session** that does not read the
  primary transcription.
- The **hardware differential tests** on the macOS runner (exit criterion 3)
  are the further check against both.

## The two formal A64 sources are one source

The Sail Arm model's README says its Sail files "are derived from the 2023-03
version of Arm's ASL specification using the automatic ASL-to-Sail
translation tool". Arm's machine-readable specification (`Instructions.json`)
carries the same ASL as the operation of each instruction. So the two are one
source in two syntaxes (the Sail model is from the 2023-03 ASL, the JSON from
2026-09), and they share Arm's own errors, if any. That is why the second
transcription comes from the manual's prose.

The `arm-mrs` JSON is also the only machine-readable encoding table
(`Instructions.json` has every encoding with its fixed and variable bits), so
the decoder differential against `yaxpeax-arm` can be checked against it as
well.
