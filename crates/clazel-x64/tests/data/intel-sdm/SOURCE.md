# Intel 64 and IA-32 Architectures Software Developer's Manual, volume 2 (A-Z), pinned and not vendored

Upstream: https://cdrdv2-public.intel.com/929352/325383-093-sdm-vol-2abcd.pdf
SHA-256: d137a7887787bbb06c1a8b8bafd51958d8d2e16b4dff987a03226c845cca1516 325383-093-sdm-vol-2abcd.pdf
Size: 11294447 325383-093-sdm-vol-2abcd.pdf
License: Intel copyright, no licence to redistribute. See `LICENSE.md`.

Version 093 of "Combined Volumes 2A, 2B, 2C and 2D: Instruction Set Reference,
A-Z" (order number 325383), the latest on Intel's page
https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
on 2026-11-16 (the link there, https://cdrdv2.intel.com/v1/dl/getContent/671110,
redirects to the URL above). The encoding tables of jit.md item J.3 are
Appendix A (the opcode maps) and the "Instruction Operand Encoding" tables of
each instruction page; the operations are the pseudocode of each page.

The PDF is not in this repository, because Intel's terms of use
(https://www.intel.com/content/www/us/en/legal/terms-of-use.html) say its
documents may not be copied or posted, and the PDF carries no open licence. So
the pin is the URL, the size and the SHA-256 above: a reader fetches the file
and compares. If Intel moves or replaces the file, the hash no longer matches
and the pin must be changed by a person, after reading the new edition's
change list.

`xtask/src/testdata/isa.rs` writes `tests/generated/intel_sdm.rs`, the table
of this pin. Intel's XED encoder/decoder tables (Apache-2.0,
https://github.com/intelxed/xed) are a machine-readable form of the same
encoding data and are not pinned here; whether to pin them is a decision for a
person.
