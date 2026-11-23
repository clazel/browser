# Russinoff's RTL library, the floating-point definitions the ACL2 x86isa model uses

Upstream: https://github.com/acl2/acl2/tree/33b05575eaf9f54734bf36e6f4bd8ee094ff2ee1/books/rtl/rel11
Commit: 33b05575eaf9f54734bf36e6f4bd8ee094ff2ee1
License: BSD-3-Clause. `LICENSE.md` is `books/rtl/rel11/license.txt` at this commit, copied unchanged (Advanced Micro Devices, 1995-2013; David M. Russinoff). Files with their own licence header (`portcullis.lisp`: ForrestHunt, Inc., BSD-3-Clause) keep it.

The same acl2/acl2 commit as `acl2-x86isa`. The x86isa SSE books
(`machine/instructions/fp/`) define `addsd`, `subsd`, `mulsd`, `divsd`,
`sqrtsd` and the conversions with this library's functions (`rtl::rnd`,
`rtl::decode`, the `excps.lisp` exception rules), so the J.3 spec of the
floating-point instructions is read from these files. Copied byte for byte,
with the paths relative to `books/rtl/rel11/` kept:

- `package.lsp`, `portcullis.lisp`: the `RTL` package;
- `lib/`: every `.lisp` file, the library's whole interface. The J.3 spec
  reads `defs.lisp`, `reps.lisp`, `round.lisp` and `excps.lisp`; the others
  (`basic`, `bits`, `log`, `float` and the rest) define what those use.

Not vendored: `support/` (the proofs behind `lib/`), `rel9-rtl-pkg/`, the
`.acl2` certification files and the `.sys` caches.

To update, copy the files from a newer acl2/acl2 commit (keeping it equal to
`acl2-x86isa`'s), change the commit above, and run `cargo xtask testdata`.
`xtask/src/testdata/isa.rs` writes `tests/generated/acl2_rtl.rs`, the
inventory of paths, sizes and hashes.
