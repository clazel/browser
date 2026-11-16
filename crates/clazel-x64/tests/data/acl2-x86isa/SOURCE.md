# The ACL2 x86isa model of the x86-64 instruction set (a subset of its files)

Upstream: https://github.com/acl2/acl2/tree/33b05575eaf9f54734bf36e6f4bd8ee094ff2ee1/books/projects/x86isa
Commit: 33b05575eaf9f54734bf36e6f4bd8ee094ff2ee1
License: BSD-3-Clause. The files are ACL2 Community Books, and each carries its own copyright header (Regents of the University of Texas; later years also Yahya Sohail and Intel Corporation), which supersedes the repository's `LICENSE`. `LICENSE.md` is the repository's `LICENSE` at this commit, copied unchanged.

The commit is the tip of `master` of acl2/acl2 on 2026-11-16 (committed
07:06 UTC). The model is by Shilpi Goel, Warren A. Hunt Jr. and Matt Kaufmann
(University of Texas at Austin, with later contributors). Copied byte for
byte, with the paths relative to `books/projects/x86isa/` kept:

- `README`, `portcullis/` (the package and the constants the books use);
- `utils/`: the data structures (`structures.lisp` and the others), without
  the `.sys` certification caches;
- `machine/`: the fetch, prefix, ModR/M and SIB decoding, the opcode
  listing (`inst-listing.lisp`), the register and memory accessors, RFLAGS,
  and the dispatch;
- `machine/instructions/`: the instruction books the subset of jit.md item
  J.3 reads: `add`, `sub`, `and`, `or`, `xor` (and their `-spec` books),
  `arith-and-logic`, shifts and rotates, `multiply`, `logical`,
  `conditional` (`jcc`, `cmovcc`, `setcc`), `jump-and-loop` (`jmp`),
  `move`, `move-sse` (`movq`), `subroutine` (`ret`), `signextend`, `flags`;
- `machine/instructions/fp/`: the SSE2 floating-point books (`addsd`,
  `subsd`, `mulsd`, `divsd`, `sqrtsd`, `ucomisd` and the conversions), and
  `logical.lisp`, which holds the `comisd`/`ucomisd` instruction
  (`x86-comis?/ucomis?-Op/En-RM`). The arithmetic books call Russinoff's RTL
  library, which is the suite `acl2-rtl`.

Not vendored: the proofs (`proofs/`, 12.8 MB), the Linux and virtualization
projects, the `.sys` caches, the x87, SSE integer, MMX, string, segmentation,
paging-only and system-call books, and the images. The instruction books
include ACL2 system books (`centaur/bitops` and others) that are not
vendored; a reader of the model does not need them, and running it would need
the whole ACL2 distribution.

To update, copy the files from a newer acl2/acl2 commit, change the commit
above, and run `cargo xtask testdata`. `xtask/src/testdata/isa.rs` writes
`tests/generated/acl2_x86isa.rs`, the inventory of paths, sizes and hashes.
Nothing reads the model yet. How this model relates to the Sail one is in
`crates/clazel-x64/README.md`.
