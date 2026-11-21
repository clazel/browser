# The Sail x86 model translated mechanically from the ACL2 x86isa model (a subset of its files)

Upstream: https://github.com/rems-project/sail-x86-from-acl2/tree/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf
Commit: 0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf
License: BSD-3-Clause for the model snapshot (`model/LICENSE`: Patrick Taylor and Capabilities Limited, and the University of Texas for the ACL2 model it derives from; `LICENSE.md` is a copy of it); BSD-2-Clause for the translator and the rest of the repository (`LICENCE`).

The commit is the tip of `master` of rems-project/sail-x86-from-acl2 on
2026-11-16 ("Update README.md", 2024-11-29; its last model change is "Update
model snapshot"). Its README says the model is "automatically translated"
from the ACL2 x86isa model by a translator written by Patrick Taylor and
extended by Thomas Bauereiss (supervised by Alasdair Armstrong and Peter
Sewell). **This model is therefore not an independent source from
`acl2-x86isa`**: the functions keep the ACL2 names (`gpr_add_spec_1`,
`jcc_cmovcc_setcc_spec`) and the structure of the ACL2 books line by line.
The analysis is in `crates/clazel-x64/README.md`. By the user's decision of
2026-11-16 (jit.md, the note under J.3) it is kept **only as a check on our
reading of ACL2**; the independent transcription comes from Intel's SDM.

Copied byte for byte, from the repository root, `README.md` and `LICENCE`; from
`model/`, the files of the integer subset of jit.md item J.3: the prelude and
register files, the ModR/M, SIB and prefix decoding, RFLAGS, linear and
physical memory, `step.sail` and the two- and three-byte opcode dispatch, and
the books for `add`, `sub`, `and`, `or`, `xor`, shifts and rotates,
`multiply`, `conditional`, `jump_and_loop`, `mov`, `move`, `subroutine` and
`signextend`.

Not vendored: the translator (`translator/`), the documentation, the
generated test patches, `evex_opcodes_dispatch.sail` and
`vex_opcodes_dispatch.sail` (1.3 MB, AVX), and the books outside the subset.
**The translated model appears to have no SSE2 scalar double instructions**:
none of the vendored files mentions `addsd`, `sqrtsd` or `ucomisd`, and the
files not vendored are named for integer, string, segment and system
instructions and for the AVX dispatch (the floating-point books of the ACL2
model, `machine/instructions/fp/`, were not translated; only the shuffle and
unpack and `mov` SSE books were). It can serve as a second source for the
integer subset at most.

To update, copy the files from a newer commit, change the commit above, and
run `cargo xtask testdata`. `xtask/src/testdata/isa.rs` writes
`tests/generated/sail_x86_from_acl2.rs`, the inventory of paths, sizes and
hashes. Nothing reads the model yet.
