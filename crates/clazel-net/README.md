# clazel-net

The network shell for the Clazel browser: it resolves a host name and carries
bytes between a TCP socket and its caller. Part of [Clazel](../../README.md),
a web browser whose parsers of untrusted input carry machine-checked proofs.

This crate **carries bytes and decides nothing about them.** It does not parse
HTTP, does not build requests, and never touches the cookie jar. Every
decision about a byte is made by a proven function in another crate; this
crate owns the sockets, the clocks, the random query ID and the order in which
things are tried. Only the `http://` half exists: TLS is parked (Phase 3
item 3.0).

## What it is

- **`resolve(host)`**: IP literals (`127.0.0.1`, `::1`, `[::1]`) and
  `localhost` need no query. Anything else reads the `nameserver` lines of
  `/etc/resolv.conf` with `clazel_dns::resolv::parse::nameservers`, builds a
  query with `encode_query` (random ID from `/dev/urandom`), sends it over UDP
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
- **`NetError`**: `Resolve(ResolveError)`, `Connect(ErrorKind)`,
  `Io(ErrorKind)`, `Timeout(Stage)`. No panics: the workspace lints that deny
  `unwrap`, `expect`, indexing and unchecked arithmetic apply.

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
`cargo test -p clazel-net`.
