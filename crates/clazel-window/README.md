# clazel-window

The host's window for Clazel's Phase 5 browser: open one, read its events and
show pixels in it. Part of [Clazel](../../README.md), a web browser whose parsers
of untrusted input carry machine-checked proofs.

This is the first slice of [item 5.22a](../../docs/phases/phase-5.md), on Windows
only. It draws with GDI, which the plan keeps for the address bar's strip. It does
not yet have the child window or the DirectComposition surface that will show a
page, and `clazel browse` does not use it yet.

See it run, on Windows:

```bash
cargo run -p clazel-window --example pattern
```

Click to move the crosshair, use the wheel to shift the gradient, and resize the
window. Events are printed as they arrive.

Tier 0: tests only. Every foreign call is in `clazel-sys`, which is audited.
