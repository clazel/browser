# Progressive JPEG files and a scan script for `clazel-jpeg` (`jpeg-progressive`)

Upstream: https://github.com/libjpeg-turbo/libjpeg-turbo
Commit: 7b4993786d856cbccabfc0ed2f923ba000e326cc
License: see `LICENSE.md` (IJG licence; `test.scan`'s is inferred, a person should confirm it)

`progressive.pack` is made by `python3 scripts/jpeg-progressive.py <jpegtran> <dir>` (its header gives the format, the variants and how to get `jpegtran`) from the baseline files of the 6.5 suites `libjpeg-turbo-testimages` (`testorig.jpg`, `testimgint.jpg`) and `jpeg-corpus` (every file libjpeg-turbo reads): 654 files, 134 each of the variants `default` (`jpegtran -progressive`), `restart` (with a restart interval of 3 blocks), `spectral` and `successive` (scan scripts made by the script: spectral selection only, and successive approximation with DC and AC refinement), and 118 of `libjpeg-turbo-scan` (`-scans test.scan`, the files with three components). `jpegtran` is a lossless transcoding, so each file holds the coefficients of its baseline original; the script asserts, for every file it writes, that libjpeg-turbo's decoding of it equals its decoding of the original, so the references of the 6.5 suites are the references of these files. The tool is libjpeg-turbo 2.1.5 (Ubuntu 24.04, `libjpeg-turbo-progs` 2.1.5-2ubuntu2, with `libjpeg-turbo8` of the same version), **not** a build of 3.2.1 (see the README of `clazel-jpeg`).

- `progressive.pack`: sha256 `0880edeb9bdc285e60d9b2546d0d02cfb2b0797c5d96211d387e111b1d92cb30`.
- `test.scan`: sha256 `a6e81cd5f36367b301e1d1c20902ec70357e4eb66ad8105a39bacc394475b144`. Copied byte for byte from `testimages/test.scan` of the commit above: libjpeg-turbo's own progressive scan script, the one its tests give `cjpeg -scans`.
