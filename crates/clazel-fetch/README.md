# clazel-fetch

The HTTP client of [Clazel](../../README.md): the decisions between a URL
and the bytes on the wire, formally verified with Verus.

## What it is (so far)

Phase 3 item 3.6, first part, module `request`:

- the request for an `http:` URL: `GET`, the origin-form target (RFC 9112
  §3.2.1: the URL's serialized path, `/` if empty, and its query; never
  the fragment), and the fields `Host` (RFC 9110 §7.2: the serialized host
  and the port if the URL has one), `Connection: close`, `Accept: */*` and
  `User-Agent: clazel`, serialized by `clazel-http`;
- where to connect: the serialized host and the port (80 by default);
- which responses are interim (RFC 9110 §15.2: 1xx except 101).

A URL with userinfo, a scheme other than `http`, or a non-ASCII code point
in what would be sent is refused. Not built yet: redirects, cookies and
`theorem_wire_cookies`, and the transducer form of the plan
([docs/phases/phase-3.md](../../docs/phases/phase-3.md)).

## Verification

Tier 0, target 2. Every executable function is proven in Verus to meet its
contract (`src/request/contract.rs`) against the spec
(`src/request/spec.rs`). There are no mutations, independent transcription
or conformance tests yet; the network shell's `fetch` tests
(`clazel-net`) exercise it end to end against local servers.
