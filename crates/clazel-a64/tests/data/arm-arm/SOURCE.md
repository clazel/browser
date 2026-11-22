# Arm Architecture Reference Manual for A-profile architecture (DDI 0487), issue M.d, pinned and not vendored

Upstream: https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1
SHA-256: 80d589a4645feba6bdb9d77edfaf04d4394d5d5444a4c41f97cf4fdd20eee3d5 DDI0487M_d_a-profile_architecture_reference_manual.pdf
Size: 129014701 DDI0487M_d_a-profile_architecture_reference_manual.pdf
License: Arm copyright, proprietary notice, no licence to redistribute. See `LICENSE.md`.

The file is what Arm's own documentation service serves for DDI 0487 "latest"
on 2026-11-16: its API
(`https://documentation-service.arm.com/documentation/ddi0487/latest`) names
version label **M.d** (document quality "EAC", Arm's early-access label for a
release not yet final) and lists this PDF as the resource
`DDI0487M_d_a-profile_architecture_reference_manual.pdf`. The human-facing
page is https://developer.arm.com/documentation/ddi0487/latest, which
redirects to support.arm.com and is a script-driven page that a plain client
cannot read; the `static/` URL above is the one the API gave, fetched without
its `token` query parameter, and it returned the PDF (`%PDF-1.7`, 129,014,701
bytes, 129 MB).

This is the source of the independent A64 transcription of jit.md item J.4:
the instruction pages (Part C, "The A64 Instruction Set") give each
instruction's encoding and its pseudocode, and Part B gives the application
level model. Pinned Arm ARM issues change: when Arm publishes M.e or a final
M.d, the hash no longer matches and a person must repin after reading the
change list.

The PDF is not in this repository: it is far over the size budget (129 MB),
and Arm's documents carry a proprietary notice with no right to redistribute
(`LICENSE.md`). Nothing was checked against a mirror. The `static/` URL is
Arm's own host, but it is an opaque document id, and Arm may withdraw it when
it replaces the issue; if so, repin from the page above.

`xtask/src/testdata/isa.rs` writes `tests/generated/arm_arm.rs`, the table of
this pin.
