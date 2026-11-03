# clazel-net

The network shell for the Clazel browser: it resolves a host name and carries
bytes between a TCP socket and its caller. Part of [Clazel](../../README.md),
a web browser whose parsers of untrusted input carry machine-checked proofs.

This crate **carries bytes and decides nothing about them.** It does not parse
HTTP, does not build requests, and never touches the cookie jar. Every
decision about a byte is made by a proven function in another crate; this
crate owns the sockets, the clocks, the random query ID and the order in which
things are tried. `fetch` takes `http://` and `https://` URLs: when
`clazel-fetch`'s transducer asks for `Connect { tls: true }` it opens a
`TlsConnection` to the host it names, with Mozilla's roots as the trust
anchors (`fetch_jar_verified` takes others, for tests), and reports any TLS
failure, a truncation included, as `Error`. The kernel's network driver
(`Driver`) carries out `Connect { tls: true }` the same way, so `clazel
browse` opens `https:` pages: each TLS connection's thread owns its
`TlsConnection` and takes the request over a channel, since one TLS state
machine serves both directions. A connection the kernel closes sends
close_notify first: the thread seals it right after the request and the
driver writes it on `Close`. Random octets, for the TLS
client and the DNS query ID, come from the OS through
`clazel_sys::fill_random`, the one audited `unsafe` call per OS
(`docs/SYS-AUDITS.md`).

## What it is

- **`resolve(host)`**: IP literals (`127.0.0.1`, `::1`, `[::1]`) and
  `localhost` need no query. Anything else reads the `nameserver` lines of
  `/etc/resolv.conf` with `clazel_dns::resolv::parse::nameservers`, builds a
  query with `encode_query` (random ID from `clazel_sys::fill_random`), sends it over UDP
  port 53 with a 2 s timeout and one retry per nameserver, nameservers in
  order. A reply is decoded with `decode_udp` and accepted only by
  `answer_addresses`, which checks the ID and the question; anything else is
  ignored until the timeout. When the reply has TC set, the query is repeated
  over TCP with `tcp_frame` and `tcp_message_len`. A is asked first, AAAA only
  if A gave no address. A CNAME that `answer_addresses` reports as `redirect`
  is asked about again, at most 8 times.
- **`run(addrs, port, request, on_bytes)`**: connect to the addresses in order
  (10 s per attempt), send `request` in full, then give every chunk read (at
  most 16 KiB, never empty) to `on_bytes` until it returns `Flow::Stop` or the
  peer closes. It returns `Finish::Closed` or `Finish::Stopped`: the caller's
  parser needs to know about a close. `run_with` takes the `Timeouts`
  (connect, and idle per read or write; default 30 s).
- **`TlsConnection::open(addrs, port, timeouts, host, now, verifier)`**,
  then `send`, `read` and `close`, as `Connection`: TLS 1.3 over TCP. The
  driver's secret octets (X25519 scalar, ClientHello random, session id)
  come from `clazel_sys::fill_random`; if it fails, the result is
  `NetError::Random` and no socket is opened, so nothing built from unfilled
  octets is sent. `open_with_random` takes the caller's source instead, for
  reproducible tests. Every protocol decision is `clazel_crypto::client::Client`'s (the
  driver over `clazel-tls`'s machines, with the libcrux providers and a
  `ChainVerifier` holding the caller's trust anchors). The shell writes what
  the driver sends, hands it what arrives and the end of the stream, and keeps
  delivered plaintext until it is read. `read` returns `None` once both
  close_notify alerts have been seen; `close` sends ours and does not wait for
  the server's. A read or write that times out before the handshake completes
  is `Timeout(Stage::Handshake)`.
- **`NetError`**: `Resolve(ResolveError)`, `Connect(ErrorKind)`,
  `Io(ErrorKind)`, `Timeout(Stage)`, and `Tls(Failure)`: the RFC 8446 §6.2
  alert and its origin (sent by us, sent by the server, not sent, or the
  stream truncated before close_notify), displayed by name, e.g. `tls:
  bad_certificate (42), sent to the server`. A close_notify from the server
  during the handshake is `Tls` with alert 0 from the server. `Random(RandomError)`:
  the OS random source failed. No panics: the
  workspace lints that deny `unwrap`, `expect`, indexing and unchecked
  arithmetic apply.

## Choices that are ours

- A CNAME target is turned back into a dotted name for the next query by
  `clazel-dns`'s proven `wire_to_dotted` (a target that has no dotted
  spelling, such as a label holding a dot, is `BadAlias`). The shell has no
  transformation of untrusted bytes of its own.
- Addresses are tried in order, with no racing (no happy eyeballs).
- A peer that resets while the request is being written still has what it sent
  delivered; the write error is returned only if nothing arrived.
- The idle timeout is per read. A peer that sends one byte just inside each
  window is not stopped by the shell; the caller stops it with `Flow::Stop`.
- The host must be UTF-8 for the literal and `localhost` checks, and an IPv4
  literal must be the four-part form `std` accepts; the caller passes the
  host the URL parser produced.

## Verification

Tier 0: tests only, and the crate stays there because it does I/O. The tests
need no Internet: a fake UDP nameserver on 127.0.0.1 (an answer, AAAA after an
empty A, a CNAME, an endless CNAME chain, a wrong ID, a wrong question,
NXDOMAIN, a dead server before a live one), a TC reply that forces a TCP retry
over a split-write reply, and `TcpListener` servers for `run` (a large request
and reply, Stop on a connection that never closes, a silent server that must
hit the read timeout, a refused port). `tests/hostile.rs` runs `fetch_with`
against hostile `TcpListener` servers (bytes that are not HTTP, an endless
body, chunk sizes of 2^64 and 2^64-1, an over-long field line, 300 field
lines, an immediate close, a partial head, silence, a short Content-Length)
and requires an error, never a panic or a hang; one case, a chunked body that
never ends, is `#[ignore]`d because it does not return in 20 s today.
`tests/tls.rs` runs `TlsConnection` against an in-process rustls server (a
`test` dependency; TLS 1.3, ChaCha20-Poly1305, X25519) on a loopback socket,
with the test root of `clazel-crypto/tests/fixtures/tls` as the trust store
and, except where noted, a fixed test seed as the randomness: ECDSA and RSA handshakes with a
request, a response and close_notify both ways, a 100000-octet response read
until the server's close_notify, a server that closes during the handshake
(truncation), one that stalls (the handshake timeout), a certificate for
another name (bad_certificate, which rustls reads), and bytes that are not
TLS (a plaintext alert on the wire). The ECDSA and RSA handshakes run again
through `open`, with the OS source, and two connections through `open` send
different ClientHello randoms and session ids (two seeded ones send the same
ClientHello). A unit test in `src/tls.rs` checks that a failing source opens
no socket. The same file runs `fetch_jar_verified` over TLS (OS randomness):
an `https:` request and response, with the request an `http:` URL gets; a
certificate for another name (the fetch fails with bad_certificate and
sends no request); a close-delimited body whose stream ends without the
server's close_notify (a truncation, so the fetch fails); and a `Secure`
cookie set by an `https:` response and sent on the `https:` redirect.
`cargo test -p clazel-net`.
