# Unicode 18.0.0 data for line breaking

Version: Unicode 18.0.0 (UAX #14 revision 57, 2026-09-01)
License: Unicode License v3 (`LICENSE.md`, copied from https://www.unicode.org/license.txt)

Each file is copied byte for byte from unicode.org. Upstream URLs:

- https://www.unicode.org/Public/18.0.0/ucd/LineBreak.txt
  (Date: 2026-08-07, 14:59:16 GMT)
- https://www.unicode.org/Public/18.0.0/ucd/auxiliary/LineBreakTest.txt
  (Date: 2026-08-07, 14:42:50 GMT)
- https://www.unicode.org/Public/18.0.0/ucd/EastAsianWidth.txt
  (Date: 2026-06-29, 15:25:05 GMT)
- https://www.unicode.org/Public/18.0.0/ucd/emoji/emoji-data.txt
  (Date: 2026-01-30, 22:30:17 GMT)
- https://www.unicode.org/Public/18.0.0/ucd/extracted/DerivedGeneralCategory.txt
  (Date: 2026-06-29, 15:25:02 GMT)

`cargo xtask check` hashes every file and fails if one differs from the
line below, or if the directory holds anything else:

SHA-256: ae8cf1970c73f3f1a12d77852df96c4b2b1723ca8b388e36bb5739250c6849de LineBreak.txt
SHA-256: fd9ff9eca411080085b41471bba79ae19d9db2e16924f9770b8509f1affd3f95 LineBreakTest.txt
SHA-256: a0cf29eacd00cfcaec4381c6b7c281685f18dbb4e7ff82b4076ccb342ca839aa EastAsianWidth.txt
SHA-256: 80d00f8e616a0ef27fd6b8de3b758c06383b5d917e2977709578e68baf733bf1 emoji-data.txt
SHA-256: d6b151d2d40ee9b1876d26f417980f45ffae47b6055ccf7203cb31f07a030f94 DerivedGeneralCategory.txt

The version is the one `clazel-idna` pins (`crates/clazel-idna/data/unicode-18.0.0/`),
so the browser has one Unicode version. UAX #14 revision 57 is the annex for
Unicode 18.0.0, and `LineBreakTest.txt` is its test file ("Default Line_Break
Test").

`xtask/src/linebreak.rs` turns the property files into
`crates/clazel-layout/src/text/data.rs`; the generated file's header lists what
it derives. `LineBreakTest.txt` is not converted: the conformance test
(`crates/clazel-layout/tests/conformance_linebreak.rs`) includes it as it is.
To update: copy the files of a newer version, change the directory name, URLs
and hashes, and run `cargo xtask tables`.

What each file provides:
- LineBreak.txt: Line_Break, with its `@missing` default XX (UAX #14 LB1).
- LineBreakTest.txt: the conformance cases.
- EastAsianWidth.txt: East_Asian_Width F, W and H, the set `$EastAsian` of
  UAX #14 §6 (rules LB19a and LB30).
- emoji-data.txt: Extended_Pictographic (LB30b); its other properties are not
  read.
- DerivedGeneralCategory.txt: General_Category Mn and Mc (LB1's resolution of
  SA), Pi and Pf (LB15a, LB15b, LB19), Cn (LB30b), and for CSS Text 3, Zs
  ("other space separators", §4.1) and Cc (control characters, §4).
