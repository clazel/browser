# Wuffs GIF test data (`wuffs-gif`), for `clazel-gif`

Upstream: https://github.com/google/wuffs
Commit: b36a81d3352604fee1fee3661f39909706b1b966
License: MIT or Apache-2.0, our choice (Wuffs' `LICENSE-MIT` at that commit, unchanged, as `LICENSE.md`; `LICENSE-APACHE` is the alternative)

The directory `test/data/` of that commit (`main` on 2026-11-16), the `*.gif` files only; the `.giflzw`, `.indexes.giflzw`, `pi.txt.giflzw` and `.make-artificial.txt` files beside them upstream are not vendored. Each file is copied byte for byte, unmodified.

Provenance, from `test/data/README.md` at that commit: `animated-red-blue.gif` and `gifplayer-muybridge.gif` are original animations by Nigel Tao; `bricks-*` are encodings of an original photo by Nigel Tao; `harvesters.gif`, `hat.gif`, `hibiscus.regular.gif` and `hippopotamus.*` are encodings of artworks the Metropolitan Museum of Art lists as public domain; `hibiscus.primitive.gif` is that Tiffany image run through `fogleman/primitive`; `muybridge.gif` is derived from a public-domain Wikipedia image; `pjw-thumbnail.gif` is derived from a photo by Rob Pike; `transparent-1x1.gif` is made by a small Go program. Wuffs' README says some files derive from third-party images; these are the ones used here.

Files and their SHA-256 (`xtask/src/testdata/wuffs_gif.rs` checks each, and that it starts with `GIF89a`):

- `animated-red-blue.gif`: sha256 `808d6cb5fbc61e54f16e51b16b503ca8a05b854e9a3c63b5952a2de2b9ea57b5`
- `bricks-dither.gif`: sha256 `9b001ecb5c457a67bd9208841aedd8603777bac6c341bc4fee5409a9143aaecd`
- `bricks-gray.gif`: sha256 `9788d5a21a06fb07eaa3bfd9ce77ae50908a519daf4fc71aef2d456b8eb9bee2`
- `bricks-nodither.gif`: sha256 `3b2629e4ecf260b8da13bda6fd262a2f7ab4f90940662d9cb3cce19d00aac08f`
- `gifplayer-muybridge.gif`: sha256 `821394939530703742617a6ac4c7fe2061d475d599acdbcf0a33c5b4d7622aef`
- `harvesters.gif`: sha256 `58c297d017200571c847fea54bd3a44f562086e12cd28b6cebd9089227037c7d`
- `hat.gif`: sha256 `da46a35274a6b3db483a2e527cc031b0f37522d2d09bf24a64e368566b47ba08`
- `hibiscus.primitive.gif`: sha256 `a6e9077c85644ff2a33466af78b2b2d8034cfaad8bfcd2b01789cd09303404c4`
- `hibiscus.regular.gif`: sha256 `8eb6f6df68e98b404615f8853f4ca5ec027d27afaeda20ba69dfdeb60b91e74e`
- `hippopotamus.interlaced.gif`: sha256 `c93248c130cf16fe6f068a6091b45ccc21065170ec0d7aa9a99514f20986f567`
- `hippopotamus.interlaced.truncated.gif`: sha256 `bb0687ba3f668861a5fdf0de6db70cbd6ab77fba49cb90b6b9338c3bfe119656`
- `hippopotamus.masked-with-muybridge.gif`: sha256 `10e29cd2484e5b332d4b2ad8b70c19bd9209bf9512cae42f263a15f2db301e69`
- `hippopotamus.regular.gif`: sha256 `0ab0b9850a813975e07b4d166947bdd6e5e6b6f6a0f346f105fbbf2fa604217c`
- `muybridge.gif`: sha256 `5b5650cd1a4b2ff1c969959d565bf5504689a99de2e004797ed39dda57f34f59`
- `pjw-thumbnail.gif`: sha256 `10e1f3847e8c9952bbccfe73955e53fb150ae1bb1a25dd31c4cb06377eed14c3`
- `transparent-1x1.gif`: sha256 `693d949d8c3fdc7fd4ace7c340b5f177a9f0c5be7bafee8bc93a7d88b7523d75`
