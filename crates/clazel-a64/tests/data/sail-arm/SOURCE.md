# The Sail model of the Armv9.4-A architecture: the A64 base instructions and the shared pseudocode (a subset of its files)

Upstream: https://github.com/rems-project/sail-arm/tree/5416ef6b43e9527c38dc71fb752259c1d01a47e1/arm-v9.4-a
Commit: 5416ef6b43e9527c38dc71fb752259c1d01a47e1
License: BSD-3-Clause-Clear (Arm Limited, Thomas Bauereiss, Brian Campbell, Alasdair Armstrong, Alastair Reid, Peter Sewell). `LICENSE.md` is `arm-v9.4-a/LICENSE` at this commit, copied unchanged.

The commit is the tip of `master` of rems-project/sail-arm on 2026-11-16
("Import tweaks for Lean output", 2026-11-09). Copied byte for byte from
`arm-v9.4-a/`, the paths relative to it kept:

- `README.md`, `LICENSE.md` (the repository's `LICENSE`);
- `src/instrs64.sail`: the AArch64 base instructions (2.1 MB), one file, so
  the subset of jit.md item J.4 is a part of it;
- `src/v8_base.sail`: the shared pseudocode they call (1.7 MB);
- `src/prelude.sail`, `builtins.sail`, `decode_start.sail`, `decode_end.sail`,
  `map_clauses.sail`, `event_clauses.sail`, `termination_measures.sail`,
  `interface.sail`, `mem.sail`, `fetch.sail`.

Not vendored: the AArch32 instructions (`instrs32.sail`), SVE and SME
(`instrs64_sve.sail`, `instrs64_sme.sail`, 5 MB together), the generated
system-register glue (`sysregs_autogen.sail`, 8 MB), the Coq, Isabelle, Lean
and C snapshots, and the other versions (`arm-v8.5-a`, `arm-v9.3-a`).

**This model is derived from Arm's own ASL.** Its README says the Sail files
"are derived from the 2023-03 version of Arm's ASL specification using the
automatic ASL-to-Sail translation tool" and that the ASL came as a snapshot
provided by Arm. So it is not independent of Arm's machine-readable
specification (`arm-mrs`, Arm's 2026-09 release of the same ASL): see
`crates/clazel-a64/README.md`. By the user's decision of 2026-11-16 (jit.md,
the note under J.4) the primary spec is transcribed from this model and
Arm's ASL, and the independent transcription from the Arm Architecture
Reference Manual's prose (`arm-arm`).

To update, copy the files from a newer commit, change the commit above, and
run `cargo xtask testdata`. `xtask/src/testdata/isa.rs` writes
`tests/generated/sail_arm.rs`, the inventory of paths, sizes and hashes.
Nothing reads the model yet.
