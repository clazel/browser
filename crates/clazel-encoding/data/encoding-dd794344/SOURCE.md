# WHATWG Encoding Standard, `encodings.json` and `indexes.json`

Upstream: https://github.com/whatwg/encoding/tree/dd7943441a861a60a073bffa55869d91cb6a8288
Commit: dd7943441a861a60a073bffa55869d91cb6a8288 (whatwg/encoding, 19 October 2026; the commit `src/lib.rs` transcribes)
License: Creative Commons Attribution 4.0 International, with portions incorporated into source code under the BSD 3-Clause License (`LICENSE`, copied from the same commit)

`encodings.json` is the standard's table of encodings and their labels
(§4.2 "Names and labels"), and `indexes.json` every index of §5 "Indexes";
the standard publishes both at https://encoding.spec.whatwg.org/ and they
are checked in at the root of whatwg/encoding. They are copied here byte for
byte from the commit above (`indexes.json` last changed upstream in
`2c3853e`, 4 October 2024):

- https://raw.githubusercontent.com/whatwg/encoding/dd7943441a861a60a073bffa55869d91cb6a8288/encodings.json
- https://raw.githubusercontent.com/whatwg/encoding/dd7943441a861a60a073bffa55869d91cb6a8288/indexes.json
- https://raw.githubusercontent.com/whatwg/encoding/dd7943441a861a60a073bffa55869d91cb6a8288/LICENSE

`cargo xtask check` hashes the files and fails if one differs from the
lines below, or if the directory holds anything else:

SHA-256: 078212b3697f60b81225b6671bd9da2604497abff0aa8e96e4d46605c02ac9e7 encodings.json
SHA-256: b7c8961095f0b4cae8f4a16a5011e7c84047a60c1277e28ee8df9e56074ee509 indexes.json

`xtask/src/encoding_indexes.rs` turns them into (`cargo xtask tables`):

- `crates/clazel-encoding/src/labels/data.rs`: the 40 encodings, their
  names, and 228 label rows;
- `crates/clazel-encoding/src/single_byte/data.rs`: the 27 single-byte
  indexes, 128 entries each.

The multi-byte indexes (`big5`, `euc-kr`, `gb18030`, `gb18030-ranges`,
`jis0208`, `jis0212`, `iso-2022-jp-katakana`) are vendored in the same file
and not yet generated: their decoders are Phase 4 item 4.4.
