# NSS root certificate store (`certdata.txt`), nss-dev/nss at one commit

Commit: 0a2b0c75fa036930d98331b721c0780693a3e17a (2026-10-20, "Bug 2084101 - Remove eMudhra emSign Root CA - G3 from NSS")
License: Mozilla Public License 2.0 (`LICENSE` is NSS's `COPYING`, copied from the same commit; `certdata.txt` carries the MPL-2.0 notice in its own header)

Each file is copied byte for byte from https://github.com/nss-dev/nss (the
NSS source, as mirrored from hg.mozilla.org/projects/nss) at the commit above:

- https://raw.githubusercontent.com/nss-dev/nss/0a2b0c75fa036930d98331b721c0780693a3e17a/lib/ckfw/builtins/certdata.txt (1356175 bytes)
- https://raw.githubusercontent.com/nss-dev/nss/0a2b0c75fa036930d98331b721c0780693a3e17a/COPYING (18100 bytes)

The commit is the latest one to touch `lib/ckfw/builtins/certdata.txt` as of
2026-10-26 (`gh api 'repos/nss-dev/nss/commits?path=lib/ckfw/builtins/certdata.txt'`).

`cargo xtask check` hashes `certdata.txt` and fails if it differs from the
line below, or if the directory holds anything else:

SHA-256: 3ec2b4d240dc12c747eaf450061db84af757c483bbda302f9e29ceb5d70be510 certdata.txt

`xtask/src/roots.rs` turns `certdata.txt` into
`crates/clazel-x509/src/roots/data.rs` (`cargo xtask tables`); the rules it
applies (which roots are kept, what is carried) are in
`crates/clazel-x509/README.md`.

## Updating

1. Pick the newest commit that touches `lib/ckfw/builtins/certdata.txt` in
   nss-dev/nss (or hg.mozilla.org/projects/nss). Download the file and
   `COPYING` from that commit into a new, empty directory
   `crates/clazel-x509/data/nss-<first 8 hex digits of the commit>/`; never
   run anything from them.
2. Rewrite this `SOURCE.md` (commit, date, subject, URLs, sizes, SHA-256).
3. Point `DATA_DIR` in `xtask/src/roots.rs` and the `include_str!` path in
   `crates/clazel-x509/tests/trust_store.rs` at the new directory, delete the
   old one, and update the pinned counts in the test.
4. Run `cargo xtask tables`, then `cargo test -p clazel-x509`, and commit the
   result. The generator stops on anything it does not understand (a new
   trust value, an unlinked object, a fingerprint that does not match).
