# Unicode 18.0.0 Character Database files for ECMAScript regular expressions

Upstream: https://www.unicode.org/Public/18.0.0/
License: Unicode License v3 (`LICENSE.md`, the copy `clazel-idna/data/unicode-18.0.0/` made of https://www.unicode.org/license.txt)

Version: Unicode 18.0.0, the version of `clazel-idna/data/unicode-18.0.0/` and
`clazel-layout/data/unicode-18.0.0/`. unicode.org publishes these files
outside version control, so there is no commit: each file is pinned by the
SHA-256 below, and its header names its version and date. Each is copied byte
for byte. Upstream URLs, under https://www.unicode.org/Public/18.0.0/:

- ucd/CaseFolding.txt  (Date: 2026-02-03, 23:09:45 GMT)
- ucd/extracted/DerivedBinaryProperties.txt  (Date: 2026-02-03, 23:09:50 GMT)
- ucd/DerivedCoreProperties.txt  (Date: 2026-08-07, 16:19:42 GMT)
- ucd/extracted/DerivedGeneralCategory.txt  (Date: 2026-06-29, 15:25:02 GMT)
- ucd/DerivedNormalizationProps.txt  (Date: 2026-02-03, 23:09:53 GMT)
- ucd/PropList.txt  (Date: 2026-08-07, 16:20:14 GMT)
- ucd/PropertyAliases.txt  (Date: 2026-02-03, 23:10:11 GMT)
- ucd/PropertyValueAliases.txt  (Date: 2026-06-24, 13:39:29 GMT)
- ucd/ScriptExtensions.txt  (Date: 2026-08-06, 18:14:47 GMT)
- ucd/Scripts.txt  (Date: 2026-06-29, 15:25:26 GMT)
- ucd/SpecialCasing.txt  (Date: 2026-05-19, 02:48:44 GMT)
- ucd/UnicodeData.txt
- ucd/emoji/emoji-data.txt  (Date: 2026-01-30, 22:30:17 GMT)
- emoji/emoji-sequences.txt  (Date: 2026-04-30, 22:40:18 GMT)
- emoji/emoji-zwj-sequences.txt  (Date: 2026-01-09, 12:44:43 GMT)

`cargo xtask testdata` checks every file against the hash below, that each
file's header says 18.0, that `UnicodeData.txt` and
`DerivedNormalizationProps.txt` are byte for byte `clazel-idna`'s, and that
the directory holds nothing else; `tests/generated/ucd_regexp.rs` is the
inventory it writes.

SHA-256: a004797658a457bec4dc11683e39f69249ea3b595b752dbea6721c4c9f587b0d CaseFolding.txt
SHA-256: f4336d325727d94c31f06b660488f5213a5b6f6cf8bb55b090f87bac704805a5 DerivedBinaryProperties.txt
SHA-256: 09c928886a178fcafd93c29e4bd59073a058e5a100b716d425cb563ab50f68c9 DerivedCoreProperties.txt
SHA-256: d6b151d2d40ee9b1876d26f417980f45ffae47b6055ccf7203cb31f07a030f94 DerivedGeneralCategory.txt
SHA-256: 98ac7f67d985fe781e317f6182e885e94cabb0c314769e6dd73e48b226931ccd DerivedNormalizationProps.txt
SHA-256: f438f532e8737bb8a2702126cdf9c4af5e357c58c7acf9d9eb2fc7c1a1d955d6 PropList.txt
SHA-256: 83b8df695f9da543dba02b0be2b8bd72f0b52836ad264be113c6d285021ef025 PropertyAliases.txt
SHA-256: 06c4c8eaf7b0bf34abe73b113da1215bd784ac254d4c223600b90267caa4bbbd PropertyValueAliases.txt
SHA-256: 5c9d34a922f687726f2a8bcf57d49f905987e51f1b21b58c95a00fbe255cec23 ScriptExtensions.txt
SHA-256: 0071fd81b6aeae25f6e8bce8efec3066a6476a91b49bdb2f52dc76e817862a6a Scripts.txt
SHA-256: 8538dea57c184f1ef3783885ea79677b10f6efa06423717157e63712f14d1ad2 SpecialCasing.txt
SHA-256: 0736451de439ae7baf1425136617da495e09ee5afbe6e394374db7009ea08950 UnicodeData.txt
SHA-256: 80d00f8e616a0ef27fd6b8de3b758c06383b5d917e2977709578e68baf733bf1 emoji-data.txt
SHA-256: 1823dce71f3dd9cb0ad1976797baee4ffbdc1909756f43af8ce4c57f732843a4 emoji-sequences.txt
SHA-256: f61b5213bdf85a57741a9f903cb38d0f39a3d13be6ff4aca3b39857e859a9191 emoji-zwj-sequences.txt

What RegExp reads from each (item 7.10 writes the generator; `cargo xtask
tables` will run it, as it does for `clazel-idna`):
- UnicodeData.txt, DerivedGeneralCategory.txt: General_Category (`\p{Lu}`,
  `\p{gc=Cn}`, `\p{Any}`, `\p{Assigned}`), and the simple case mappings.
- PropertyAliases.txt, PropertyValueAliases.txt: the property and value names
  and aliases ECMA-262 resolves for `\p{..}` (it accepts only names these files
  list, and only the properties of its own tables).
- Scripts.txt, ScriptExtensions.txt: Script and Script_Extensions.
- PropList.txt, DerivedCoreProperties.txt, DerivedBinaryProperties.txt,
  DerivedNormalizationProps.txt, emoji-data.txt: the binary properties of
  ECMA-262's table of binary properties (for example `Alphabetic`, `ID_Start`,
  `Changes_When_NFKC_Casefolded`, `Bidi_Mirrored`, `Emoji`).
- CaseFolding.txt: the simple case folding Canonicalize uses for `/iu` and
  `/iv`.
- SpecialCasing.txt: the full upper-casing `toUppercase` uses for `/i`
  without `u`.
- emoji-sequences.txt, emoji-zwj-sequences.txt: the properties of strings of
  the `v` flag (`RGI_Emoji`, `Basic_Emoji`, `Emoji_Keycap_Sequence`,
  `RGI_Emoji_Flag_Sequence`, `RGI_Emoji_Modifier_Sequence`,
  `RGI_Emoji_Tag_Sequence`, `RGI_Emoji_ZWJ_Sequence`).

Not vendored, because the table above does not need it: `LineBreak.txt`,
`EastAsianWidth.txt` (those are `clazel-layout`'s), the `Test` files, and
`emoji-variation-sequences.txt`. `Script_Extensions` of a code point with
no entry in ScriptExtensions.txt is its Script, which the generator applies.
