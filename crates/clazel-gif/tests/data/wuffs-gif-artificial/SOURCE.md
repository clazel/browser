# Wuffs GIF test data (`wuffs-gif-artificial`), for `clazel-gif`

Upstream: https://github.com/google/wuffs
Commit: b36a81d3352604fee1fee3661f39909706b1b966
License: MIT or Apache-2.0, our choice (Wuffs' `LICENSE-MIT` at that commit, unchanged, as `LICENSE.md`; `LICENSE-APACHE` is the alternative)

The directory `test/data/artificial-gif/` of that commit (`main` on 2026-11-16), the `*.gif` files only; the `.giflzw`, `.indexes.giflzw`, `pi.txt.giflzw` and `.make-artificial.txt` files beside them upstream are not vendored. Each file is copied byte for byte, unmodified.

These are hand-crafted by Wuffs' authors for corner cases (README: "artificially generated test data, often to explicitly test corner cases").

Files and their SHA-256 (`xtask/src/testdata/wuffs_gif.rs` checks each, and that it starts with `GIF89a`):

- `background-color.gif`: sha256 `24fbf48b9b1fa9aeaff40ae28f78b8ccdcb9f2974e3007e21d6c3a8830ec6565`
- `empty-palette.gif`: sha256 `1a8f32f725bf9dff244eaf809788d695071c479c5ebbe709540616cc8bed8a16`
- `frame-out-of-bounds.gif`: sha256 `e7400346e44ca927bba35fefb8498a8dc5a03fa4bae38886ad6753c95e3a0056`
- `metadata-empty.gif`: sha256 `7bd07fdc0fdeffc309d72f56e6fb3abd96a9b82334a6abc5c6b499cea6ce692e`
- `metadata-full.gif`: sha256 `a8b4f021f9a6d28ec8684709464e0514f930c4e88318ff5aa82b7a01948298d1`
- `multiple-graphic-controls.gif`: sha256 `c128ccd6f668677a325397556971d56537087970f4104050fe8a0b0b8e13be82`
- `multiple-loop-counts.gif`: sha256 `705e9b699560b0b91bd879f7be41c4ba63dc1d33c4cdad3ff2d99722073d6a33`
- `no-frames.gif`: sha256 `6f6005cbba527f08deaf121fbf0f5a3bde0e40f6e527e7c47f486d081dd247c5`
- `pixel-data-none.gif`: sha256 `9a539467d2bfe5b3f6150c0b99a65c996944fb5c236fc1e059c5728fea2b4cac`
- `pixel-data-not-enough.gif`: sha256 `2be98d75d305b577ccd85dc35cc900fc8cf85af18fe7c4979606b9c7d1a924bd`
- `pixel-data-too-much-bad-lzw.gif`: sha256 `4f7f3f373e1a87fb41770a5fb67f23715e4eec214e783ff82408bef93d764876`
- `pixel-data-too-much-good-lzw.gif`: sha256 `39abfd5655627265a9f3efa444aa5a661bafad93bea7725fbb60deb3576ea053`
- `small-frame-interlaced.gif`: sha256 `760b700013eda776d04c0ffe55e645bd4774804106664bc10e596d453ae25a93`
- `transparent-index.gif`: sha256 `32d3409a79b75614ef385354d54f148f08856f8e9ce0d55054582ff7f40f4461`
- `zero-width-frame.gif`: sha256 `dd18a256eb564db70cb0ae2785bb04ec28f7ffc30d8154c1ef9fa91f2e6f641c`
