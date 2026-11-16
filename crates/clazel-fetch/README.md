# clazel-fetch

The HTTP client of [Clazel](../../README.md): the decisions between a URL
and the bytes on the wire, formally verified with Verus.

## What it is (so far)

Phase 3 item 3.6 ([docs/phases/phase-3.md](../../docs/phases/phase-3.md)).

Module `request`:

- the request for an `http:` or `https:` URL (the same for both): `GET`, the origin-form target (RFC 9112
  §3.2.1: the URL's serialized path, `/` if empty, and its query; never
  the fragment), and the fields `Host` (RFC 9110 §7.2: the serialized host
  and the port if the URL has one), `Connection: close`, `Accept: */*` and
  `User-Agent: clazel`, and a `Cookie` field last when the cookie-string is
  not empty (Fetch §3.1.1), serialized by `clazel-http`;
- where to connect: the serialized host and the port (80 by default, 443
  for `https`), and whether the connection speaks TLS (for `https`, RFC
  9110 §4.2.2);
- which responses are interim (RFC 9110 §15.2: 1xx except 101).

A URL with userinfo, a scheme other than `http` or `https`, or a non-ASCII code point
in what would be sent is refused.

Module `transducer`: the client state machine, a pure function the network
shell (`clazel-net`) drives. `start(url, jar, now)` asks to `Connect`;
`step(state, input)` maps `Connected`, `Bytes`, `Closed` and `Error` to `Send`, `Close`,
`Done` and `Fail`. It skips interim responses, ends a close-delimited body
at `Closed` (RFC 9112 §6.3 step 8), fails on an invalid message, an
unsupported transfer coding or a response incomplete at close, and follows
redirects as Fetch §4.5 does for a navigation GET (301, 302, 303, 307 and
308 with one `Location`, resolved against the request URL; a non-HTTP(S)
target or a 21st redirect is a network error), one connection per request.
The HTTP and URL functions are parameters, joined to `clazel-http`'s
response parser and `clazel-url`'s basic URL parser in `transducer::real`.

Cookies: the jar (`clazel-cookie`'s model) is a field of the state and is
what the state holds when `Done` or `Fail` ends the fetch. When the
request is sent, its `Cookie` field is RFC 6265bis §5.8.3's retrieval for
the current URL, as a top-level navigation GET with no client (so
same-site, unless a redirect crossed sites: Fetch's redirect-taint, which
makes it cross-site, so `SameSite=Strict` cookies are withheld), and the
jar becomes the jar after the retrieval's step 5. Every `Set-Cookie` field
line of a final response is stored, one by one, by §5.7 as HTTP, before
the redirect is decided; a 1xx response never reaches the storage. The
`Secure` requirement is the connection's: `Connect.tls` is true exactly
for `https`, which is when the cookie functions see the request as secure,
so a `Secure` cookie is only ever sent over TLS. A redirect may go from
`https:` to `http:` (Fetch §4.5 allows it); that request is sent in the
clear without its `Secure` cookies. There is no HSTS and no upgrade of
`http:` to `https:`. HTML's "same site" compares schemes, so a redirect
between `http:` and `https:` on one host sets the redirect-taint.

The transducer does not see TLS: the shell gives it the plaintext and
reports any TLS failure as `Error` (`clazel-net`'s `fetch`, over
`TlsConnection`).

Not built yet: the `Cookie` field and
`Set-Cookie` of a fetch with a client (a subresource or a cross-site
initiator: the context is fixed), `SameSite=Lax-allowing-unsafe`, and a
conformance suite beyond the http-state corpus (see below).

Requests with a method and a body (item 6.16, built in part): the
transducer's state holds a `Req` (method, body with its content type,
the initiator's origin and the origin redirect-taint), `start_req` starts a
fetch of any request, and `start` is a `GET` with none of them, as before.
The bytes sent are the head, then the body octet for octet (RFC 9112 §6.2).
A body adds `Content-Type` and `Content-Length` (Fetch §4.6 steps 6 to 9);
a `POST` without a body adds `Content-Length: 0`; any method but `GET` and
`HEAD` adds `Origin` (Fetch "append a request `Origin` header"), which is
`null` for a request with no initiator, an opaque one, an https initiator
and a URL that is not https, or after a redirect that left the origin; the
`Cookie` field stays last. Only `GET` (with no body) and `POST` are built,
a body is at most 16 MiB; anything else ends the fetch with `NotFetched`
before connecting. HTTP-redirect fetch step 12 is
`rewrite_for_redirect`: 301 and 302 turn a `POST` into a `GET` without a
body, 303 does so for every method but `GET` and `HEAD`, 307 and 308 keep
method and body, so the next `Send` writes the body again. The cookie
context reads the method (a `POST` is not safe, RFC 9110 §9.2.1) and the
initiator as the site for cookies, so `SameSite=Lax` and `Strict` cookies
are not sent on a cross-site `POST` (`theorem_post_cookies`).
`theorem_redirect_method` states the rewriting for every step, and
`theorem_sends_have_valid_req` that a `Send` only follows a request this
client builds. **Not built:** the `clazel-ipc` `Submit` message, the
kernel's handling (and `theorem_body_from_requester`,
`theorem_body_sent_once`, `theorem_address_bar_integrity` restated), the
reload-and-back policy for a `POST` entry, `tests/fetch.rs` against an
in-process server, and the widening of `independent.rs` to methods with a
body (its correspondence still requires a plain `GET`).

## Verification

Tier 2 (raised on CI's full verification of its pull request). Every executable function is proven in Verus to meet its
contract (`src/request/contract.rs`, `src/transducer/contract.rs`) against
the spec. Proven of the transducer spec, for every HTTP and URL function
(`src/transducer/theorems.rs`): at most 21 connections and 21 requests per
fetch whatever the inputs; the redirect count stays at most 20; the URL
changes only to an HTTP(S) URL, one redirect at a time; every `Send` is the
request for the current URL with the cookie-string of the jar; no action
on bytes until the parser has decided; `theorem_wire_cookies`, that every
`Send` is the request for the current URL whose only jar-derived part is
its `Cookie` field, whose value is §5.8.3's retrieval; `theorem_jar_frame`,
that the jar after a step is the jar before, or the jar after the
retrieval's step 5 at `Connected`, or the jar of §5.7 storage of the final
response's own `Set-Cookie` lines (so `clazel-cookie`'s root lemmas are all
there is to know about the jar of a fetch); `theorem_tls_when_secure`, that
every `Connect` is the current request's connection, goes where
`connect_to` says, and speaks TLS exactly when the request is `https:`,
which is when the cookie functions see it as secure. That splitting the bytes differently changes nothing is proven
for every parser that is `prefix_stable`, and `clazel-http`'s is proven
`prefix_stable` (`src/transducer/real.rs`). The executable transducer
feeds each octet once into a `clazel-http` `ResponseParser`, so a fetch is
linear in the response's size.

Concrete cases are evaluated on the spec by Verus (`src/request/examples.rs`,
`src/transducer/examples.rs`; the transducer's with the real HTTP parser and
a stand-in URL function), and the mutations in `mutations.json` are each
killed by an example or a theorem with a certificate. The network shell's
`fetch` tests (`clazel-net`) run it end to end against local servers,
redirect chains and the 20-redirect limit included, and over TLS against a
rustls server (`clazel-net/tests/tls.rs`: a request and response, a
certificate for another name, a truncated close-delimited body, a `Secure`
cookie stored and sent).

`src/transducer/independent.rs` is a second transcription of the Fetch
Standard (HTTP-redirect fetch steps 3 to 8, 18 and 22, "location URL",
the `Cookie` header and `Set-Cookie` steps), written with the request as
its URL list (so the redirect count is the list's length and the
redirect-taint is computed from it), and a proof that, for a state and a
request in correspondence, the transducer's cookie-string, request bytes,
jar and decision on a final response are the independent ones. The class
is a navigation GET with no body, no cache, no CORS and credentials "include".
The step-level theorems (`theorem_independent_request`,
`theorem_independent_redirect`) are lifted to **whole runs** by induction
over the connections: `theorem_independent_run` says that for any URL, any
cookie jar and any hops a well-behaved shell delivers (each connection:
`Connected`, then the octets of one final response in one `Bytes`, which
the parser reads as that response), the transducer from `start(url)` sends
exactly the request bytes that Fetch's own loop sends (HTTP-redirect fetch,
then main fetch for the next URL, with the `Cookie` field of each hop from
the jar the hops before it left), leaves the cookie jar Fetch's loop leaves
(retrieval, then `Set-Cookie` storage, at every hop), and ends as it does
(the response HTTP-redirect fetch returns, a network error, or still
waiting). Fetch's loop is `indep_fetch`, a recursion over the URL list; the
transducer's is `tx_fetch`, the transducer driven through the hops with
`step` and the jar its operations leave. What it shares with `spec.rs` is
only what the standards themselves call (`clazel-cookie`'s algorithms, the
URL parser, the field functions, the request serializer). It does not
transcribe the connection: where to connect and whether to use TLS are
covered by the examples, the mutations and `theorem_tls_when_secure`, not
by a second transcription.

Conformance (`tests/conformance_http_state.rs`): the 222 rows of the
`http-state` parser corpus run through the whole client (the response's
bytes parsed, each `Set-Cookie` stored, the redirect followed, the next
request's `Cookie` field compared): 195 pass, 27 are expected failures
with reasons (RFC 6265 and draft 22 differ; the HTTP layer rejects a NUL
or CR), none fail. The Fetch Standard text was read from its commit snapshot
on the web; the repository holds no copy of it.

Conformance (`tests/conformance_post.rs`, item 6.16): random `GET` and
`POST` requests (no body, empty or with a body of up to 39 octets with CR,
LF, NUL and octets above 0x7F, three content types, no initiator or an opaque
one) through random redirect chains over all five redirect statuses and 200,
against a reference model written from Fetch's HTTP-redirect fetch step 12,
RFC 9110 §15.4 and Fetch §4.6, with rust-url resolving `Location`. The
client's bytes at every hop (head, empty line and body) and the final status
must equal the model's: 1378 of 1378 agree, 668 with a body, 97 chains in
which the `POST` and its body are sent again, 318 in which a redirect drops
them. The model shares the author's reading of the standards, so this is not
independent of them as the rust-url part is; the request side is also covered
by the Verus examples (`src/request/examples_body.rs`,
`src/transducer/examples_body.rs`) and 16 new mutations (12 with certificates, 4 killed incidentally: 85 in all, 81 certified, 0 survive).

Conformance (`tests/conformance_differential.rs`): 1500 random redirect
chains, each run by an independent reference built from rust-url (the
`url` crate, resolving `Location` against the request URL) and
`cookie_store` (RFC 6265, storing `Set-Cookie` and giving each request's
cookies), around a redirect loop written from Fetch §4.5, and by the
client through the transducer with the real HTTP, URL and cookie
functions. The two must send the same requests (target, `Host`, the
`Cookie` field as a multiset) and end the same way (final status, or a
failure). The chains use all five redirect statuses and 304, relative,
absolute, cross-site, empty, fragment, `mailto:` and `ftp:` `Location`s, a
missing and a doubled `Location`, up to two `Set-Cookie` lines a hop with
`Domain`, `Path`, `HttpOnly` and `Max-Age`, and endless redirect loops that
reach the limit of 20; the test counts the runs that follow a redirect,
send a cookie and reach the limit, so that agreement means something. No
WPT `fetch/` suite is vendored (the suites need a browser and a test
server), so there is none here yet.
