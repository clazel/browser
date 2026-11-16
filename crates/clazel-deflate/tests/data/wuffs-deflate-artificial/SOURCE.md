# Wuffs artificial DEFLATE test data (`wuffs-deflate-artificial`), for `clazel-deflate`

Upstream: https://github.com/google/wuffs
Commit: b36a81d3352604fee1fee3661f39909706b1b966
License: MIT or Apache-2.0, our choice (Wuffs' `LICENSE-MIT` at that commit, unchanged, as `LICENSE.md`; `LICENSE-APACHE` is the alternative)

From the directory `test/data/artificial-deflate/` of that commit (`main` on 2026-11-16): each `*.deflate` stream and its `*.deflate.decompressed` expected output (the output is empty for `distance-code-31`, whose stream is invalid: the decoder must fail). The `.commentary.txt` and `.make-artificial.txt` files beside them upstream are not vendored. These are hand-crafted by Wuffs' authors for corner cases (README: "artificially generated test data, often to explicitly test corner cases"). Each file is copied byte for byte, unmodified.

Files and their SHA-256 (`xtask/src/testdata/wuffs_deflate.rs` checks each):

- `backref-crosses-blocks.deflate`: sha256 `fabf4df822edb6d7f7cf7c5d060248c51f6407c3fc3ff8d4563ba94c28454a1b`
- `backref-crosses-blocks.deflate.decompressed`: sha256 `ad97f19de6c241378d96edf4a893a221f22d447ca5e76d258bc5cbdb2f5351cc`
- `degenerate-huffman-0-bit.deflate`: sha256 `621ebbf05385415d00908e5ca3a4ffdc70cfec03de55fb4f4d5bdd97df646337`
- `degenerate-huffman-0-bit.deflate.decompressed`: sha256 `1cbec737f863e4922cee63cc2ebbfaafcd1cff8b790d8cfd2e6a5d550b648afa`
- `degenerate-huffman-1-bit.deflate`: sha256 `3f93098dd90731d2b55a238ac2b498d7749a62d84f81759f0b4f28bb0592177f`
- `degenerate-huffman-1-bit.deflate.decompressed`: sha256 `62579587ef6152187a29b864c44b69fa9e89319b87a81871607c541b9b3a297a`
- `distance-32768.deflate`: sha256 `60618406028da59f4d562ee8c94f0a50ceddf33815b7fd2db00458cac723ea9d`
- `distance-32768.deflate.decompressed`: sha256 `db94f7f1b46a9ad5c6455d5206fe6931c00f4a3bb66e1a96aa10e437d8cfc166`
- `distance-code-31.deflate`: sha256 `ed3afb34bc519d2e64a2008e0f39dc812a7d7da047881bdda41952c0c1215652`
- `distance-code-31.deflate.decompressed`: sha256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `huffman-primlen-9.deflate`: sha256 `eaf00db859c5030783bf8f57795c4376674e650de811152186fa424caa81fe2c`
- `huffman-primlen-9.deflate.decompressed`: sha256 `b493d48364afe44d11c0165cf470a4164d1e2609911ef998be868d46ade3de4e`
