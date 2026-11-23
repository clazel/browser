# Wuffs DEFLATE and zlib test data (`wuffs-deflate`), for `clazel-deflate`

Upstream: https://github.com/google/wuffs
Commit: b36a81d3352604fee1fee3661f39909706b1b966
License: MIT or Apache-2.0, our choice (Wuffs' `LICENSE-MIT` at that commit, unchanged, as `LICENSE.md`; `LICENSE-APACHE` is the alternative)

From the directory `test/data/` of that commit (`main` on 2026-11-16): `romeo.txt` with its raw DEFLATE encodings (`romeo.txt.deflate`, `romeo.txt.fixed-huff.deflate`) and its zlib encoding, `midsummer.txt` and `pi.txt` with their zlib encodings. The `.gz`, `.bz2`, `.xz`, `.zst` and other files beside them are not vendored, and neither is `DCI-P3-D65.icc` with its `.zlib` (an ICC profile from color.org, whose licence was not checked). Each file is copied byte for byte, unmodified.

Provenance, from `test/data/README.md` at that commit: `romeo.txt` and `midsummer.txt` are excerpts of Shakespeare (copied from shakespeare.mit.edu), `pi.txt` is the digits of pi, and `romeo.txt.fixed-huff.deflate` was made from `romeo.txt` by a custom program of the Wuffs authors.

Files and their SHA-256 (`xtask/src/testdata/wuffs_deflate.rs` checks each):

- `midsummer.txt`: sha256 `354bbbd7d0f2f642daa949b5028be5475be26a5c2a8780eb509e8ee6a3d3dbcc`
- `midsummer.txt.zlib`: sha256 `0b9606b57407c63dd9c92352aadedfb033897007059c2dd7434ef23fc93157b1`
- `pi.txt`: sha256 `85a1390d22006a80ad783ef1d2abe233ad12d23470ac5d4500e4bc4f154cbcb9`
- `pi.txt.zlib`: sha256 `a8acd5de3c15568f2dcc0ebaf2efc56213fbbce375a26a67f10fabf48c4d68bf`
- `romeo.txt`: sha256 `4854f5102035d288e8b8d6727cf25e0a44369e0a2dbaed7c02093bf3020979da`
- `romeo.txt.deflate`: sha256 `44338a75b7c341ad4a18024fe4b5baad06fcf558cb51fecbd98399d6cbbb1433`
- `romeo.txt.fixed-huff.deflate`: sha256 `b893df87de159528c544462f9de49f0ceccf8f5b9302ce4a4dd3fead76b8231d`
- `romeo.txt.zlib`: sha256 `7104dd00aa342367c1f4706bbd61aabb53dbc1811c35072d025f803d3284a921`
