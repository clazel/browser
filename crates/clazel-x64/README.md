# clazel-x64

Part of [Clazel](../../README.md). The x86-64 subset the JIT emits: its
semantics, encoder and decoder ([jit.md](../../docs/phases/jit.md) item J.3).

Nothing is implemented yet (tier 0, target tier 2). Item J.2 vendored or
pinned the sources the semantics will be written against, in `tests/data/`:

| Suite | What | Held as |
|---|---|---|
| `acl2-x86isa` | the ACL2 x86isa model (BSD-3-Clause), files of the J.3 subset | 2.6 MB, vendored |
| `sail-x86-from-acl2` | the Sail model translated from it (BSD-3-Clause, BSD-2-Clause) | 0.8 MB, vendored |
| `sail-x86-shina` | a Sail model written from the Intel manuals (MIT) | 0.6 MB, vendored |
| `intel-sdm` | Intel SDM volume 2, version 093 | pinned by URL and SHA-256, not vendored (Intel's terms forbid redistribution) |

Each has a `SOURCE.md` with the upstream, the commit (or the SHA-256) and the
licence. The tables in `tests/generated/` list every file's size and hash.

## Are the two x86 models independent? No.

jit.md item J.2 requires this to be read before the ACL2 and Sail models count
as two sources. The finding:

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
  their reading of the manual and their test evidence. **They are one source
  for the purpose of J.2.**
- The translated model is also narrower: it has no SSE2 scalar double
  instruction (the ACL2 books in `machine/instructions/fp/` were not translated),
  so it could not check the `addsd`/`sqrtsd`/`ucomisd` part of the subset even
  as a copy.

A second source that is not a translation:

- **`shina-lab/sail-x86`** (vendored as `sail-x86-shina`, MIT) is a Sail model
  written from the Intel SDM and the AMD manual, and its README and files
  mention neither ACL2 nor x86isa. It covers SSE2 scalar double. Its
  authorship is one person (Rui Ueyama, with many commits carrying an AI
  co-author line); it was created in 2026-03 and has no external review that
  we found; its floating-point arithmetic is `extern`, supplied by its
  emulator; it states hardware agreement from KVM runs on two hosts (its commit
  messages give counts of passing cases). It is independent in lineage, and
  its weight as evidence is a person's decision.
- Other sources, not pinned: the K framework's x86-64 semantics (Dasgupta et
  al., PLDI 2019, derived from Stoke's specifications, so a separate
  lineage from ACL2) and Intel's XED tables (machine-readable encodings, not
  semantics). A person may prefer one of them.
- The strongest evidence the plan has is not a model at all: exit criterion 3's
  hardware differential tests (running every template on real CPUs on two
  OSes) and the decoder differential against `iced-x86`.

What this means for item J.3 and for the "Risks" paragraph of jit.md: unless a
person accepts `sail-x86-shina` (or another source) as the second, the
"independent transcription from the second source" of J.3 is an independent
transcription of the *same* ACL2 semantics (or of the SDM's pseudocode), and
the crate header must say that, as jit.md's Risks section already requires.
