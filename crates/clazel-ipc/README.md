# clazel-ipc

The wire format between the Clazel browser kernel and its renderer
processes: a strict profile of CBOR, length-prefixed frames, and a typed
message schema. Part of [Clazel](../../README.md), a web browser whose
parsers of untrusted input carry machine-checked proofs.

## What it is

- **CBOR profile** (`cbor`): RFC 8949 §3 (the initial byte, arguments, and
  major types 0, 2, 3 and 4, plus the simple values false and true) with the
  §4.2.1 core deterministic encoding requirements. Nothing else is accepted:
  no negative integers, maps, tags, floats, `null`, `undefined` or indefinite
  lengths. The decoder rejects every non-shortest form of an argument, so
  each value has exactly one encoding. Text strings must be valid UTF-8,
  checked with `clazel-encoding`. The input must be exactly one item;
  trailing bytes are rejected. An item is a `Vec<Tok>`, its tokens in wire
  order.
- **Frames** (`frame`): a 4-byte big-endian length (at most `MAX_FRAME`,
  1 MiB) and exactly one CBOR item. `payload_length` lets a transport refuse
  an oversized frame from its first four bytes.
- **Messages** (`message`): the schema is ours, not a standard's. An array
  whose first element is a tag, with renderer-to-kernel messages
  (`CookieGet`, `CookieSet`, `StorageGetItem`, `Navigate`, `Display` and so
  on) and kernel-to-renderer ones (`Commit`, `Body`, `BodyEnd`,
  `CookieValue`, `StorageValue`, `Error`). A committed document is `Commit`
  (URL, content type as a byte string, kind: 0 a document, 1 a user
  script), zero or more `Body` frames of at most `MAX_BODY_CHUNK` octets
  each, and `BodyEnd`. `Display` (title, text, links) is a renderer's text
  rendering; its links are the schema's one nested array. No message
  carries a claimed identity (origin, renderer id, tab id or sender URL),
  and renderer ids never reach a renderer.

Out of scope: any CBOR outside the profile, and the transport itself
(sockets, reading and writing); this crate only turns bytes into values and
back.

## Verification

Tier 2: the executable code is proven, in Verus, to equal an executable
specification transcribed from the standard, over all inputs. The current
numbers are in the
[status table](../../README.md#verification-status).

- **Proven:** `decode`, `encode`, the frame functions and the message
  functions meet their contracts. Decoding inverts encoding, and encoding
  inverts decoding wherever decoding succeeds, so the profile is canonical
  and no two byte strings decode to the same item (no parser differentials
  between kernel and renderer). The decoder never reserves more elements than
  there are bytes left, so a declared array length of 2^64 allocates
  nothing. The two schema rules are lemmas over a table of message fields;
  that table is a view of the schema, not the encoder, so the rules hold
  because `Message` has no identity field, and the mutation tests show the
  lemmas fail if the table changes. Every `Body` of at most
  `MAX_BODY_CHUNK` octets fits one frame (`lemma_body_fits_frame`).
- **Independent transcription:** `cbor/independent.rs` is written from
  RFC 7049 §2, Appendix C and §3.9 and proven equal to the spec on every
  input. The same agent wrote both, so it is weaker evidence than a second
  author's. The schema is ours, so it has no second transcription.
- **Mutations:** every deliberately broken spec is rejected by a checked
  certificate (`mutations.json`); counts are in the table.
- **Conformance:** RFC 8949 Appendix A vectors (those inside the profile
  decode and re-encode; the rest must be rejected), and a differential
  against `minicbor` on random items and on random and mutated bytes (where
  we reject, `minicbor` may accept only a non-shortest form). No difference
  was found. `tests/messages.rs` round-trips every message through the real
  code.
- **Modelling choices** (listed in `src/cbor/spec.rs`): an item is its
  pre-order token sequence, which is equivalent to the standard's tree and
  lets the decoder be a loop with no recursion depth to limit; failure is
  `None`. Each frame holds exactly one item.

## Trust

The proofs assume the Rust compiler, Verus and its solver, the `vstd`
library, and that the specs transcribe the standards correctly; testing
against the suites above is the check on that last point, not a proof. The
full list is in [docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false` for now); it also depends
on the workspace crate `clazel-encoding`.

```rust
use clazel_ipc::cbor::decode::decode;
use clazel_ipc::cbor::token::Tok;
use clazel_ipc::message::codec::{Msg, decode_framed, decode_renderer_message, encode_framed};

// A message in a frame: 4-byte length, then one CBOR item.
let msg = Msg::CookieSet { cookie_string: b"a=b; Path=/".to_vec() };
let frame = encode_framed(&msg).expect("under MAX_FRAME");
assert_eq!(decode_framed(&frame), Some(msg));

// A renderer may only send renderer-to-kernel messages.
let commit = Msg::Commit { url: b"https://a.test/".to_vec(), content_type: Vec::new(), kind: 1 };
let frame = encode_framed(&commit).expect("under MAX_FRAME");
assert!(decode_framed(&frame).is_some());
assert_eq!(decode_renderer_message(&frame[4..]), None);

// Every non-shortest form is rejected: 1 is 0x01, never 0x18 0x01.
assert_eq!(decode(&[0x01]), Some(vec![Tok::Uint(1)]));
assert_eq!(decode(&[0x18, 0x01]), None);
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
