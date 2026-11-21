# Arm's open-source machine-readable specification of the A-profile architecture (README and licence vendored, Instructions.json pinned)

Upstream: https://kernel.googlesource.com/pub/scm/linux/kernel/git/maz/AARCHMRS/+/1346b16d47619400448f3cb6d4f22d62d3b76848
Commit: 1346b16d47619400448f3cb6d4f22d62d3b76848
SHA-256: ef75f3ec02df1b9b9c0612f4ea259d6710ac3de686b097d8f9c83d1d97aa800a Instructions.json
Size: 116678333 Instructions.json
License: BSD-3-Clause (Arm Limited), as stated in `notice.html` (the package's own notice; `LICENSE.md` is its text). Redistribution is allowed.

Arm publishes the package as `AARCHMRS_OPENSOURCE_A_profile_FAT-2026-09` on its
developer site (the "Exploration Tools" page of the A-profile architecture; the
site redirected our client to support.arm.com and was not fetched). The commit
above is a mirror of that release in a git repository (Marc Zyngier's
AARCHMRS repository at kernel.googlesource.com, whose commit message is the
release name, 2026-10-15). The mirror is third-party: a person should compare
its hashes with the tarball from Arm's site before relying on it.

Vendored, byte for byte: `README.md` and `notice.html` (the licence; schema
2.9.6).

**`Instructions.json` is pinned, not vendored.** It holds the A64, A32 and T32
instruction sets with their encodings and their ASL operations, and it is
116,678,333 bytes (116 MB), far over this suite's size budget, and it cannot
be cut to the A64 base instructions without rewriting it. The pin above is
the SHA-256 of the file as stored in the commit (LF line endings). A reader
(jit.md item J.4) fetches the commit, takes `Instructions.json` and checks the
hash. `Features.json` and `Registers.json` are not needed for the subset.

`xtask/src/testdata/isa.rs` writes `tests/generated/arm_mrs.rs`, the inventory
of the two vendored files and the table of the pin. Nothing reads the
specification yet. The Sail model derived from the same ASL is `sail-arm`.
