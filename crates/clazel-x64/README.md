# clazel-x64

Part of [Clazel](../../README.md). The x86-64 subset the JIT emits: its
semantics, encoder and decoder ([jit.md](../../docs/phases/jit.md) item J.3).

The primary spec (`src/spec.rs`, from ACL2) and the encoder/decoder contracts (`src/contract.rs`, `src/api.rs`) are written; no encoder or decoder exists yet (tier 0, target tier 2). Item J.2 vendored or
pinned the sources the semantics will be written against, in `tests/data/`:

| Suite | What | Held as |
|---|---|---|
| `acl2-x86isa` | the ACL2 x86isa model (BSD-3-Clause), files of the J.3 subset | 2.6 MB, vendored |
| `sail-x86-from-acl2` | the Sail model translated from it (BSD-3-Clause, BSD-2-Clause) | 0.8 MB, vendored |
| `intel-sdm` | Intel SDM volume 2, version 093 | pinned by URL, size and SHA-256, not vendored (Intel's terms forbid redistribution) |

Each has a `SOURCE.md` with the upstream, the commit (or the SHA-256) and the
licence. The tables in `tests/generated/` list every file's size and hash.

## Where the transcriptions come from

Decided by the user on 2026-11-16 (jit.md, the note under J.3):

- The **primary spec** is transcribed from the ACL2 x86isa model.
- The **independent transcription** is made from the Intel SDM's prose and
  pseudocode, by a **different session** that does not read the primary
  transcription.
- The **hardware differential tests** (exit criterion 3) are the further
  check against both.
- The Sail x86 translation is kept **only as a check on our reading of
  ACL2**. It is **not independent of ACL2**, and the crate header must not
  call it a second source.

## The two x86 models are not independent

jit.md item J.2 required this to be read before the ACL2 and Sail models
count as two sources. The finding:

- **The Sail model that J.2 names, `rems-project/sail-x86-from-acl2`, is a
  mechanical translation of the ACL2 x86isa model.** Its README says so in its
  title and first paragraph: it "translates the X86isa formal model of the x86
  ISA, written in ACL2 by Shilpi Goel, Warren A. Hunt, Jr., and Matt Kaufmann,
  into Sail". The translator is by Patrick Taylor (a 2020 student project,
  supervised by Alasdair Armstrong and Peter Sewell), later extended by Thomas
  Bauereiss. The model files are a snapshot of its output, and `model/LICENSE`
  carries the ACL2 model's licence as the one it derives from.
- The files confirm it. `model/add_spec.sail` has `gpr_add_spec_1` where
  `machine/instructions/add-spec.lisp` has `gpr-add-spec-1`, with the same
  steps, in the same order, naming the same helpers (`cf_spec8`,
  `add_af_spec8`). `model/conditional.sail` has `jcc_cmovcc_setcc_spec` with
  the ACL2 condition table, and the ACL2 `let rflags_var = ...` bindings
  survive in it.
- So an error in the ACL2 model's reading of the SDM is in the Sail model as
  well, and a differential test between them tests the translator (and
  Sail's typing of it), not the semantics. They share their authors' ancestry,
  their reading of the manual and their test evidence. **They are one source.**
- The translated model is also narrower: it has no SSE2 scalar double
  instruction (the ACL2 books in `machine/instructions/fp/` were not
  translated), so it cannot even check the `addsd`/`sqrtsd`/`ucomisd` part of
  the subset as a copy.

Another Sail x86 model, `shina-lab/sail-x86`, was considered as the second
source and rejected: a single author, no review we could find, and its
floating-point arithmetic left external. Other formal models (the K
framework's x86-64 semantics, Intel's XED encoding tables) are not pinned.
