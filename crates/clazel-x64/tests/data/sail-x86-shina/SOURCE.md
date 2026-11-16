# A Sail model of x86-64 written from the Intel manuals (a subset of its files)

Upstream: https://github.com/shina-lab/sail-x86/tree/1829cb6ecc5f924b0fd920582953a2402357a12a
Commit: 1829cb6ecc5f924b0fd920582953a2402357a12a
License: MIT (`LICENSE.md` is the repository's `LICENSE`, copied unchanged; Copyright (c) 2026 Rui Ueyama).

The commit is the tip of `main` of shina-lab/sail-x86 on 2026-11-16
("XSAVEC, XGETBV, FPREM and FCMOV: undefined where one manual leaves open what
the other defines", 2026-10-23). Its README says it is "based on the Intel
Software Developer's Manual (SDM) and actual hardware behavior", and the
commit messages cite SDM and AMD APM page numbers and compare the model with
KVM runs on an AMD Zen 4 and an Intel Xeon host.

**Why it is here:** the other Sail model (`sail-x86-from-acl2`) is a
mechanical translation of the ACL2 model, so it cannot be the second,
independent source jit.md item J.2 asks for. This one has no relation to ACL2
that its README or the files read here state, and it covers SSE2 scalar
double. It is not a peer-reviewed or long-established source: the repository
was created in 2026-03, has about 1,380 commits by one author, many with an AI
co-author line, and its floating-point arithmetic is `extern` (soft-float
supplied by the emulator, `model/extern.sail`). Whether it may count as the
second source is a decision for a person (`crates/clazel-x64/README.md`).

Copied byte for byte: `README.md`, `docs/x86-64-completeness-checklist.md`,
and from `model/` the files of item J.3's subset and what they need:
`x86.sail_project` (the build order), `prelude`, `core_types`, `extern`, `regs`,
`rflags`, `exceptions`, `paging`, `mem`, `operands`, `branchless`, `insn_simd`,
`insn_prefixes`, `insn_modrm`, `insn_alu`, `insn_sse_fp`, `insn_baseline`,
`insn_groups`, `insn_dispatch` and `fetch_execute`.

Not vendored: VEX, EVEX, AMX, x87, MMX, SSE integer, XSAVE, VMX, SMM,
virtual-8086, interrupts and crypto (`model/` is 1.5 MB in all), and the
emulators, tests, proofs and reports. Without them the model does not build as
it stands (`x86.sail_project` lists the rest); it is a text to read, as the
other suites are.

To update, copy the files from a newer commit, change the commit above, and
run `cargo xtask testdata`. `xtask/src/testdata/isa.rs` writes
`tests/generated/sail_x86_shina.rs`, the inventory of paths, sizes and
hashes. Nothing reads the model yet.
