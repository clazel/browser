# clazel-dns

The DNS message format for the Clazel browser's resolver: building a query,
decoding a reply (with name compression), picking the addresses out of it,
the two-octet length of a message sent over TCP, and the `nameserver` lines
of `/etc/resolv.conf`. Part of [Clazel](../../README.md), a web browser whose
parsers of untrusted input carry machine-checked proofs.

## What it is

- **Messages** (RFC 1035 §4): the header (§4.1.1: ID, QR, OPCODE, AA, TC,
  RD, RA, Z, RCODE and the four counts), the question (§4.1.2), resource
  records (§4.1.3) and name compression (§4.1.4), with the size limits of
  §2.3.4 (labels 63 octets, names 255, UDP messages 512), case-insensitive
  names (§2.3.3, the octets the server sent are kept) and the TYPE and
  CLASS values of §3.2.2 and §3.2.4. A (§3.4.1), AAAA (RFC 3596 §2) and
  CNAME (§3.3.1) records in class IN are decoded; every other record keeps
  its RDATA as octets, and is never an error. `decode_message` decodes any
  message, `decode_udp` one of at most 512 octets.
- **Query** (`encode_query`): a standard query with RD set, one question, class
  IN, no compression. The name is a dotted ASCII string (what `clazel-url`
  gives after IDNA); `None` if it is not a name (empty, an empty label, a label
  over 63 octets, a name over 255, a byte of 128 or more).
- **Answers** (`answer_addresses`): accepts a reply only if its ID and
  question equal the query's (RFC 5452 §4 to §6), QR is set, OPCODE is 0,
  TC is clear and RCODE is 0 or 3. NXDOMAIN gives no addresses; otherwise it
  follows the CNAME chain of the *answer section* from the query name (RFC
  1034 §3.6.2) and returns the addresses at the end of it. The authority and
  additional sections are never used. A chain that leaves the answer section
  gives no addresses and the last target, for a new query (RFC 1034 §5.3.3
  step 3a). A reply with TC set is not an answer: the caller retries over
  TCP (RFC 7766 §8) with `tcp_frame` and `tcp_message_len` (§4.2.2).
- **`resolv.conf`** (`resolv::parse::nameservers`): the grammar is ours (no
  standard has one) and is stated at the top of `src/resolv/spec.rs`: a line
  whose first token is `nameserver` and whose second is an IPv4 address in
  strict dotted decimal or an IPv6 address (read by `clazel-url`'s proven IPv6
  parser) gives that address; every other line is ignored.

Out of scope: EDNS(0), DNSSEC, DNS over TLS or HTTPS, every RDATA format but A,
AAAA and CNAME, and the sockets (the network shell, phase-3.md item 3.8).

## Verification

Tier 2. The executable code has Verus proofs against a
specification transcribed from the standards. The current numbers are in the
[status table](../../README.md#verification-status).

- **Proven:** `decode_message`, `decode_udp`, `encode_query`,
  `dotted_to_wire`, `tcp_frame`, `tcp_message_len`, `answer_addresses` and
  `nameservers` meet their contracts. Decoding a query we encoded gives it
  back. Every name a decoded message holds has at most 255 octets and labels
  of at most 63. `answer_addresses` returns only addresses (and a redirect)
  that are in the answer section. The decoder never reserves more records than
  there are octets in the message, so a header that declares 65535 of every
  kind allocates nothing. Name decoding terminates because a pointer must lead
  to a name that lies wholly before it ("a prior occurrence", read as in
  `ERRATA.md`: RFC 1035's text, taken as "a lower offset", allows a loop).
- **Independent transcription:** `src/independent.rs` is written from RFC 883
  §4 (the predecessor, same message layout) and proven equal to the decoder on
  every message. The two texts are the same in substance, so it checks the
  form (bit operations, names read in the message cut off at the pointer,
  sections built by prepending) and not a second author's reading. RFC 883's 16-bit
  TTL and unnamed Z bits are where it differs, and the file lists them. The
  same agent wrote both.
- **Examples:** the RFC 1035 §4.1.4 compression example (F.ISI.ARPA,
  FOO.F.ISI.ARPA, ARPA, the root), every pointer error, every size limit, and
  the answer rules are evaluated by Verus (`src/examples.rs`).
- **Mutations:** every deliberately broken spec is rejected by a checked
  certificate (`mutations.json`, one or more per field and rule); counts are in
  the table.
- **Conformance** (`tests/conformance_dns.rs`): hand-built messages for every
  rule; real responses captured from a public resolver and an authoritative
  server (A, AAAA, a CNAME chain, NXDOMAIN, a truncated reply, MX, and a
  1176-octet TCP reply); and a differential test against `simple-dns` on
  random messages it writes (with and without compression), on queries we
  write that it reads, and on 60 000 random and mutated messages. Where the two
  parsers read the same octets the contents are equal. Where we reject and
  `simple-dns` accepts, or the other way round, the test names the rule: the
  "prior occurrence" rule, trailing octets, Z bits (RFC 4035's AD and CD),
  RDLENGTH 0 or longer than the data for A, AAAA and CNAME, or a type, class
  or question `simple-dns` does not know; no difference is left unexplained.
  The `resolv.conf` grammar is tested on hand-written files.
- **Modelling choices** (listed in `src/spec.rs` and `src/resolv/spec.rs`):
  names are held in their expanded wire form; Z is three bits and must be
  zero; octets after the last record are an error; a message is at most 65535
  octets; the chain is followed from the first CNAME at each name and only the
  final name's addresses are used.

## Trust

The proofs assume the Rust compiler, Verus and its solver, the `vstd`
library, and that the specs transcribe the standards correctly; the examples,
the independent transcription and the conformance tests are the check on that
last point, not a proof. The full list is in
[docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false` for now); it also depends
on the workspace crate `clazel-url`.

```rust
use clazel_dns::answer::answer_addresses;
use clazel_dns::decode::decode_udp;
use clazel_dns::encode::encode_query;
use clazel_dns::spec::Addr;

// The query a stub resolver sends for example.com, type A, with ID 0x1234.
let query = encode_query(0x1234, b"example.com", 1).expect("a valid name");
assert_eq!(query.len(), 29);

// A reply: header, the question, and one answer whose owner is a pointer
// to the question's name.
let reply: &[u8] = &[
    0x12, 0x34, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, // header
    7, b'e', b'x', b'a', b'm', b'p', b'l', b'e', 3, b'c', b'o', b'm', 0, 0, 1, 0, 1, // question
    0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 104, 20, 23, 154, // A 104.20.23.154
];
let message = decode_udp(reply).expect("a valid reply");
let answer = answer_addresses(0x1234, b"example.com", 1, &message).expect("an answer");
assert_eq!(answer.addresses, [Addr::V4(u32::from_be_bytes([104, 20, 23, 154]))]);
assert_eq!(answer.redirect, None);

// A reply with another ID is not an answer.
assert!(answer_addresses(0x4321, b"example.com", 1, &message).is_none());
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
