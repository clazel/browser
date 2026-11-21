# JPEG files made for `clazel-jpeg` and libjpeg-turbo's output for them (`jpeg-corpus`)

Upstream: https://github.com/libjpeg-turbo/libjpeg-turbo
Commit: 7b4993786d856cbccabfc0ed2f923ba000e326cc
License: the pixels are `testimages/testorig.ppm` of libjpeg-turbo 3.2.1 (IJG licence, see `LICENSE.md`); the encoder that made the files is `scripts/jpeg-reference.py` of this repository

One file, `corpus.pack`, made by `python3 scripts/jpeg-reference.py <libjpeg-turbo checkout at the commit above> <dir>` (the format is in the script's header): 132 JPEG files and libjpeg-turbo's decoding of each. The script is a small baseline JPEG encoder (float DCT, the T.81 Annex K tables) that cuts parts of `testorig.ppm` and codes them with every sampling ratio the decoder reads (4:4:4, 4:2:2, 4:2:0, 4:4:0, 4:1:1, 4:1:0, 1 by 2 chroma, mixed and 4:1:0-like ratios), with and without restart intervals, interleaved and one scan per component, as gray, YCbCr, RGB (Adobe transform 0 and component ids `R`, `G`, `B`), CMYK and YCCK (Adobe), SOF1 and 16-bit quantization tables, at sizes from 1 by 1 to 227 by 149, and with each EXIF orientation from 1 to 8 in both byte orders. The references are made by libjpeg-turbo 2.1.5 (Ubuntu 24.04, `libjpeg-turbo8` 2.1.5-2ubuntu2, libjpeg 8 API) at its defaults (`ISLOW` IDCT, fancy upsampling), **not** by a build of 3.2.1 (see the README of `clazel-jpeg`); orientation is not applied by libjpeg, the test applies it to the reference.

- `corpus.pack`: sha256 `6f1a51a27b87e0c3f38a1658bcb1962b2d4e3aafca4a0cf8bb9b3c22c5a4994a`.
