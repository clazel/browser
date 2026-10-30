# Unicode Consortium mapping files for the single-byte encodings

Upstream: https://www.unicode.org/Public/MAPPINGS/
Commit: none (unicode.org publishes these files outside version control; each file below is pinned by its SHA-256 and its own header gives its version and date)
Retrieved: 2026-10-29
License: Unicode License v3 (`LICENSE`, copied from https://www.unicode.org/license.txt). The Unicode Terms of Use (https://www.unicode.org/copyright.html) make every data file under https://www.unicode.org/Public/ a "Unicode Data File" under that license; the ISO 8859 and KOI8 files also say so in their headers. The Microsoft files carry no notice of their own.

A second body's tables for the single-byte indexes of the Encoding
Standard (Phase 4 item 4.3): the Encoding Standard's `indexes.json` is
checked against them by `xtask/src/encoding_indexes.rs` (`cargo xtask
check` and `tables`), with every difference listed there and below. They
are copied byte for byte from:

- `VENDORS/MICSFT/WINDOWS/CP874.TXT`, `CP1250.TXT` to `CP1258.TXT`
  (windows-874, windows-1250 to windows-1258)
- `VENDORS/MICSFT/PC/CP866.TXT` (IBM866)
- `VENDORS/MISC/KOI8-R.TXT`, `KOI8-U.TXT` (KOI8-R, KOI8-U)
- `ISO8859/8859-2.TXT` to `8859-16.TXT` (ISO-8859-2 to ISO-8859-16; ISO-8859-8-I
  is a label sharing ISO-8859-8's index, so it is checked with it)

Not vendored: Apple's `VENDORS/APPLE/ROMAN.TXT` and `CYRILLIC.TXT`
(macintosh, x-mac-cyrillic). Their headers say "all rights reserved" and
grant no permission to redistribute, so those two indexes have no second
body's check here; both matched these files when compared by hand on
2026-10-29 (bytes 0x80 to 0xFF).

The differences, each checked to occur (so this list cannot go stale):

- windows-874 and windows-1250 to windows-1258: every byte from 0x80 to 0x9F
  that Microsoft's file leaves undefined is, in the Encoding Standard, the
  C1 control with the byte's value (U+0080 to U+009F). For windows-1252 these
  are 0x81, 0x8D, 0x8F, 0x90 and 0x9D.
- windows-1255 0xCA: U+05BA HEBREW POINT HOLAM HASER FOR VAV in the Encoding
  Standard; undefined in Microsoft's file.
- KOI8-U 0xAE and 0xBE: U+045E and U+040E (Belarusian short u, as in
  KOI8-RU) in the Encoding Standard; U+255D and U+256C (box drawing) in
  RFC 2319's KOI8-U, which the Unicode file transcribes.

`cargo xtask check` hashes the files and fails if one differs from the
lines below, or if the directory holds anything else:

SHA-256: 3441c37377c6721586255282ef4302c0ca61796674361959b3a2591f823a0e67 8859-10.TXT
SHA-256: 375cc8d45b331c29e5630bf5c821c85572ffba60487d4d279341bbd13f46750f 8859-13.TXT
SHA-256: 5e72e1c79b2907504111c0965953261c4584cb984465cd88d616452c12fd3782 8859-14.TXT
SHA-256: bc72d7bd5be1d15bdad8e684f9ae9f573c361bb73812c3084ed1b7622a05e58f 8859-15.TXT
SHA-256: 9164ce844b2bf3f56805c2e9ab8453cc53868757e7f75c4b8dcee7376894d55c 8859-16.TXT
SHA-256: 020946e114335b17e7d29fe8a8449786cffed714cf409b11d0b3a375197188d1 8859-2.TXT
SHA-256: 23b2d7815946cb1232c71a1543033afc396c750ffa19a3771662cf23e6194552 8859-3.TXT
SHA-256: e717699903bef2144234279a598ce39b44502942c9cc23a2ce2069a65f46b00d 8859-4.TXT
SHA-256: 9a2efea39673f95c5daa277c46ad09a41e95f27c225270424a604d033db9bd8f 8859-5.TXT
SHA-256: 7012241bd7143a3bf98861e497cd3cc092edebc3e063fc7d576420f22d22f11e 8859-6.TXT
SHA-256: 94f4a1c89ba6b2e1c1f8b30676cb5d15f232dbac36ae4ad20018a65e0f3fb9a3 8859-7.TXT
SHA-256: cbe3205c5c6f92589d6a8673d56c51d89659ae290185457e6e2f81fee7a1ad2d 8859-8.TXT
SHA-256: e6535e3c81f4aff1a4b369c46e588a2423d6a75da341e01a6cea108c7542c19a CP1250.TXT
SHA-256: d9d491808bd7956c26ef8ed07fa63015bfab32860720e07d5bf3a64a609927ee CP1251.TXT
SHA-256: f607ae328b4dff5e9bfef725f5fff0ae23f38797f8a5b95998a0d2735c0e8fad CP1252.TXT
SHA-256: 85d917854926ef09b22abefd19c7b61494e229fa391b648dc332f1fac0879ce3 CP1253.TXT
SHA-256: f93569399f81abce90441793c118d2524770b58d9c5774de3233c64d88c9fca0 CP1254.TXT
SHA-256: 67ab4e3e7c088be41e0f230fa9c2c5b9a803395bec8027a5ee77df74432290c7 CP1255.TXT
SHA-256: fd5835c5e3be668d4fa3dc3d0d3a6491795646fc9629c0892f45dd08aa72f367 CP1256.TXT
SHA-256: 5ac72f382ea4f64fe61854e0dae7d311583bd1dd20797697d4dce32b175a268b CP1257.TXT
SHA-256: 2457d5d0fbb1d444136c579edc488d0a34474d58a36b6eb2adacba88c068df2e CP1258.TXT
SHA-256: abcc96dd4253321eb5e542c1ece3adab10df0cc20ec5d1124a0cec22d636c924 CP866.TXT
SHA-256: f45277e205ff5aa8f0625c52b04614bbd9d8836c142e9b90235748b0a9921ec9 CP874.TXT
SHA-256: 83d73a3884a33784fc4a6b3711067ff3ea2c606b5d2e72cb326ad857d973363c KOI8-R.TXT
SHA-256: 854bad6ab67c3644c7b60758cff3d0f30eb54dc45a354c3e5ce470da4015f042 KOI8-U.TXT
