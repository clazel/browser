# clazel-der

ASN.1 DER (the Distinguished Encoding Rules of ITU-T X.690): a cursor-style
decoder and an encoder for the types X.509 certificates and PKCS#1 signatures
use, formally verified with Verus. Part of [Clazel](../../README.md), a web
browser whose parsers of untrusted input carry machine-checked proofs. It is
the base of items 3.5b (X.509 and path validation) and 3.5c (RSA PKCS#1 v1.5).

## What it is

- **Decoder.** Every reader takes the input, a position and an `end`
  (`end <= input.len()`), reads the one value at the position and returns
  where it stopped: `read_tlv` (the tag and the contents range), then typed
  readers for BOOLEAN, INTEGER (its sign and magnitude octets), BIT STRING
  (its unused-bits count and octets), OCTET STRING, NULL, OBJECT IDENTIFIER
  (its arcs as `u64`), UTF8String, PrintableString, IA5String, UTCTime and
  GeneralizedTime (their octets: the character and date rules are X.509's),
  `expect_sequence` and `expect_set` (the inner range), `read_optional_context`
  and `read_optional_explicit` for context-specific components (implicit and
  explicit, §8.14), and `expect_end`. To descend into a constructed value, call
  the readers again on `[cstart, cend)`; to require the end of contents, call
  `expect_end`. Nothing is copied or reserved for a declared length: readers
  return ranges, and `read_oid` pushes only arcs it has read.
- **Encoder.** `encode_tlv`, `encode_length` (the shortest form),
  `encode_integer_unsigned`, `encode_oid`, `encode_sequence`, `encode_set`,
  `encode_octet_string`, `encode_null`, `encode_boolean`, `encode_bit_string`,
  `encode_octets` for the string types, `encode_context`, and
  `encode_digest_info` (`SEQUENCE { SEQUENCE { OID, NULL }, OCTET STRING }`,
  RFC 8017 §9.2).
- **Strict DER.** The decoder accepts only the DER encoding: definite length
  in the fewest octets (§10.1), BOOLEAN `00` or `FF` (§11.1), INTEGER with no
  redundant leading octet (§8.3.2), BIT STRING with 0 to 7 unused bits, all
  zero (§8.6.2, §11.2.1), strings in the primitive form (§10.2), OBJECT
  IDENTIFIER subidentifiers without `80` padding (§8.19.2), high tag numbers
  only from 31 and without a leading zero digit (§8.1.2.4).
- **Limits** (stated at the top of `src/spec.rs`, each only rejects what the
  standard accepts): tag numbers of 2^14 and above, long-form lengths of more
  than 8 octets, and subidentifiers of 2^64 and above. Not checked here, and
  left to X.509 (item 3.5b): the characters of the string types, the
  UTCTime and GeneralizedTime formats, the order of SET OF components
  (§11.6) and the omission of DEFAULT values (§11.5).

Out of scope: BER (indefinite lengths, constructed strings, non-minimal
lengths) is rejected, not decoded, and there is no schema or `derive` layer:
callers compose the readers.

## Verification

Tier 2 (raised on CI's full verification of its pull request). See the [status table](../../README.md#verification-status)
for current numbers. The executable code has Verus proofs against an
executable specification transcribed from X.690, including absence of panics,
overflow and out-of-bounds indexing.

- **Proven:** every reader and encoder meets its contract
  (`src/contract.rs`). About the spec itself, with lemmas:
  - *No over-read* (`lemmas_overread.rs`): every reader's result depends only
    on the bytes of the value it read, `[pos, cend)`; changing any byte after
    them, or at or after `end`, changes nothing.
  - *Round trip and canonicity* (`lemmas_tlv.rs`, `lemmas_typed.rs`,
    `lemmas_oid.rs`): reading what the encoder wrote gives back the value, and
    encoding what a reader read gives back the original bytes, for the
    identifier, the length, a whole value, and BOOLEAN, INTEGER (the
    canonicity lemma covers the non-negative integers; a negative one is
    proven only to be negative, and its minimality is proven through the
    independent transcription), BIT STRING, OCTET STRING and the string
    types, NULL, OBJECT IDENTIFIER, SEQUENCE, SET and context-specific tags.
    So no two byte strings are accepted as the same value.
  - *Shortest length:* `encode_length` is one octet below 128 and otherwise
    the fewest octets, and `read_length` accepts exactly its output
    (`lemma_encode_length_shortest`, `lemma_read_length_encode_length`,
    `lemma_encode_length_read_length`).
  - *Bounded reservation:* `read_oid` returns at most as many arcs as there
    are contents octets plus one, and an encoder's output is at most 12
    octets longer than the contents it was given, so a declared length of
    2^64 reserves nothing.
- **Independent transcription:** `src/independent.rs` is written from
  Kaliski, "A Layman's Guide to a Subset of ASN.1, BER, and DER" (RSA
  Laboratories, 1993), sections 2 to 5, a different author's text of the same
  rules, and is proven equal to the spec: the identifier, length and element
  framing on every input, INTEGER, BIT STRING and NULL contents on every
  input (the Guide's rule that the contents are the minimal two's complement
  spelling of their value, against X.690's rule on the first two octets),
  OBJECT IDENTIFIER contents whose first octet is below 128 (where the Guide's
  "first octet is 40 * value1 + value2" applies), the value of an INTEGER, and
  the typed readers for those types and for SEQUENCE and SET. The Guide has
  no BOOLEAN, UTF8String or GeneralizedTime, so those have no second
  transcription. The same agent wrote both transcriptions, so this is weaker
  evidence than a second author's.
- **Examples:** `src/examples.rs` evaluates, in Verus, the examples of
  X.690 §8.1.3, §8.2, §8.6, §8.8, §8.9, §8.14 and §8.19, Kaliski's examples
  (including his X.501 `Name`) and the `DigestInfo` prefix of RFC 8017, in both
  directions, with the non-DER forms printed beside them rejected.
- **Mutations:** every deliberately broken spec in `mutations.json`, one or
  more per rule, is rejected by a certificate Verus checks. The tag numbers of
  BOOLEAN, UTF8String and GeneralizedTime are not mutated: nothing but the
  examples and the conformance test pins them (the Guide does not have them).
- **Conformance** (`tests/conformance_der.rs`): hand-built cases as Rust
  literals (valid ones from X.690 and the Guide, and one for every rejection
  rule: indefinite length, a long-form length that fits the short form,
  leading zeros in a length, INTEGER `00 7F`, BOOLEAN `01`, BIT STRING with 8
  unused bits, an OID with `80` padding, a constructed OCTET STRING, truncated
  contents, trailing bytes, and more); and a differential test against
  RustCrypto's `der` 0.8.2 (default features off) on random valid values
  (`der` writes and we read, we write and `der` reads, and the bytes are
  equal) and on random and mutated bytes, where every disagreement must be in
  a listed category. The `x509-limbo` corpus is item 3.5b's.
- **Modelling choices** (listed in `src/spec.rs`): a reader is a cursor over
  `(input, pos, end)`; failure is `None`; the next position is the end of the
  contents; INTEGERs are read as sign and magnitude range, OIDs as arcs.

## Trust

The proofs assume the Rust compiler, Verus and its solver, the `vstd`
library, and that the specs transcribe the standards correctly; the
conformance tests and the independent transcription are the check on that
last point, not a proof. The full list is in
[docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false`).

```rust
use clazel_der::decode::{expect_end, expect_sequence, read_integer, read_oid, read_tlv};
use clazel_der::encode::{encode_oid, encode_sequence};

// SEQUENCE { OBJECT IDENTIFIER 1.2.840.113549, INTEGER 5 }
let mut body = encode_oid(&[1, 2, 840, 113549]);
body.extend_from_slice(&[0x02, 0x01, 0x05]);
let bytes = encode_sequence(&body);

let (start, end) = expect_sequence(&bytes, 0, bytes.len()).expect("a SEQUENCE");
let (arcs, next) = read_oid(&bytes, start, end).expect("an OID");
assert_eq!(arcs, [1, 2, 840, 113549]);
let (negative, mag_start, mag_end, next) = read_integer(&bytes, next, end).expect("an INTEGER");
assert!(!negative && bytes.get(mag_start..mag_end) == Some(&[5][..]));
assert!(expect_end(next, end));

// Every non-DER form is rejected: 38 is 0x26, never 0x81 0x26.
assert!(read_tlv(&[0x04, 0x81, 0x26], 0, 3).is_none());
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
