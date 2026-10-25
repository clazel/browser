# clazel-fetch

The HTTP client of [Clazel](../../README.md): the decisions between a URL
and the bytes on the wire, formally verified with Verus.

## What it is (so far)

Phase 3 item 3.6 ([docs/phases/phase-3.md](../../docs/phases/phase-3.md)).

Module `request`:

- the request for an `http:` URL: `GET`, the origin-form target (RFC 9112
  §3.2.1: the URL's serialized path, `/` if empty, and its query; never
  the fragment), and the fields `Host` (RFC 9110 §7.2: the serialized host
  and the port if the URL has one), `Connection: close`, `Accept: */*` and
  `User-Agent: clazel`, serialized by `clazel-http`;
- where to connect: the serialized host and the port (80 by default);
- which responses are interim (RFC 9110 §15.2: 1xx except 101).

A URL with userinfo, a scheme other than `http`, or a non-ASCII code point
in what would be sent is refused.

Module `transducer`: the client state machine, a pure function the network
shell (`clazel-net`) drives. `start(url)` asks to `Connect`; `step(state,
input)` maps `Connected`, `Bytes`, `Closed` and `Error` to `Send`, `Close`,
`Done` and `Fail`. It skips interim responses, ends a close-delimited body
at `Closed` (RFC 9112 §6.3 step 8), fails on an invalid message, an
unsupported transfer coding or a response incomplete at close, and follows
redirects as Fetch §4.5 does for a navigation GET (301, 302, 303, 307 and
308 with one `Location`, resolved against the request URL; a non-HTTP(S)
target or a 21st redirect is a network error), one connection per request.
The HTTP and URL functions are parameters, joined to `clazel-http`'s
response parser and `clazel-url`'s basic URL parser in `transducer::real`.

Not built yet: TLS (`https:` is refused), cookies and
`theorem_wire_cookies`, the independent transcription, conformance tests.

## Verification

Tier 0, target 2. Every executable function is proven in Verus to meet its
contract (`src/request/contract.rs`, `src/transducer/contract.rs`) against
the spec. Proven of the transducer spec, for every HTTP and URL function
(`src/transducer/theorems.rs`): at most 21 connections and 21 requests per
fetch whatever the inputs; the redirect count stays at most 20; the URL
changes only to an HTTP(S) URL, one redirect at a time; every `Send` is the
request for the current URL; no action on bytes until the parser has
decided. That splitting the bytes differently changes nothing is proven
for every parser that is `prefix_stable`, and `clazel-http`'s is proven
`prefix_stable` (`src/transducer/real.rs`). The executable transducer
feeds each octet once into a `clazel-http` `ResponseParser`, so a fetch is
linear in the response's size.

Concrete cases are evaluated on the spec by Verus (`src/request/examples.rs`,
`src/transducer/examples.rs`; the transducer's with the real HTTP parser and
a stand-in URL function), and the mutations in `mutations.json` are each
killed by an example or a theorem with a certificate. The network shell's
`fetch` tests (`clazel-net`) run it end to end against local servers,
redirect chains and the 20-redirect limit included.
