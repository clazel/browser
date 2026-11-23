# libjpeg-turbo test images and their reference output (`libjpeg-turbo-testimages`), for `clazel-jpeg`

Upstream: https://github.com/libjpeg-turbo/libjpeg-turbo
Commit: 7b4993786d856cbccabfc0ed2f923ba000e326cc
License: mixed, stated in `LICENSE.md` (a copy of `testimages/LICENSE.txt`, the IJG licence of `README.ijg` and `LICENSE.md` of that commit): `testorig.jpg`, `testimgint.jpg` and `testimgari.jpg` under the IJG licence, `monkey12.jpg` under the Modified BSD licence with an ICC profile the ICC lets anyone copy unaltered; the `.ref` files are decoder output for them

Tag `3.2.1` of libjpeg-turbo (that commit). Four of the JPEG files of its `testimages/`, copied byte for byte; the other files there (PNG, PPM, PGM, BMP, ICC and `test.scan`) are not vendored. `testorig.ppm` of the same directory, which `scripts/jpeg-reference.py` encodes the `jpeg-corpus` suite from, is not vendored either.

- `testorig.jpg`: sha256 `acc6ec555d41d15b368320edaa3b20958ee6fa97cb6e4a18d1213d5ae8bec73b`. 227 by 149, baseline, 4:2:0 (what libjpeg-turbo's own tests decode against `testorig.ppm`).
- `testimgint.jpg`: sha256 `491679b8057739b3c8e5bacd1e918efb1691d271cbbd69820ff8d480dcb90963`. 227 by 149, baseline (written with the integer DCT).
- `testimgari.jpg`: sha256 `4672c7f08864cd0a8c73a4fa4b66ca32b635d38464551c1ecf06564ae8c89b38`. Arithmetic coding: `clazel-jpeg` must refuse it (no reference).
- `monkey12.jpg`: sha256 `a3cb218412cecfa877a4adee520aa3d58ac0d6d0f36a7a2541e598324ce481e3`. 12-bit samples: `clazel-jpeg` must refuse it (no reference).

References, made by `scripts/jpeg-reference.py` (see its header for the format) by decoding the files above with the installed libjpeg-turbo 2.1.5 (Ubuntu 24.04, `libjpeg-turbo8` 2.1.5-2ubuntu2, libjpeg 8 API) at its defaults, **not** with a build of 3.2.1 (see the README of `clazel-jpeg`):

- `testorig.ref`: sha256 `f6a65c8d4aa34236bd9070a2bfb3815944f86116cddd1f39489659ec05dc499e`.
- `testimgint.ref`: sha256 `2b721ca923beaebd552a7b4943f7d6f5b08be083c5139a9da294dad05f4ee003`.
