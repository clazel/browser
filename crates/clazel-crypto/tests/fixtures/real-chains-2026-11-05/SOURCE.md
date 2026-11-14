# Real certificate chains, collected 2026-11-05

The chains servers sent on 2026-11-05 at about 16:23 UTC, for
`tests/conformance_real_chains.rs` (phase-3.md item 3.5g).

**Source.** The top 1,000 domains of the Tranco list JZPGY
(https://tranco-list.eu/list/JZPGY), as tried by
`crates/clazel-net/examples/tls_survey.rs`: the domain, or `www.<domain>`
where the apex gave no answer. The 821 hosts with a DNS record each got one
`openssl s_client -showcerts -connect <host>:443 -servername <host>` from
OpenSSL 3.0.13 with its default offer, so TLS 1.2 servers are here too. 760
sent a chain. Each is kept whole and in the order sent, whether or not it is
valid. Nothing was changed.

**Licence.** None was granted. Certificates are published by the servers that
send them and, for most, in Certificate Transparency logs. They are test data
here and are never trusted.

**Files.**
- `certs.der` (1412235 bytes): the 868 distinct certificates, concatenated in
  first-seen order, each once.
- `chains.tsv` (160407 bytes): rank, host, then the chain's SHA-256 fingerprints
  in hex, separated by spaces. A certificate's role is its position: the
  first is the leaf, and the test counts those in the root table.

SHA-256: 612a7f0f6204b0b5fc6c6e538b0914be564a7dd78d835e020281292b0f19efd4 certs.der
SHA-256: 1a1f3f11b95f88b69086e7682265a49d0822af63b25b8d2f0fe1332ef86b8ada chains.tsv
