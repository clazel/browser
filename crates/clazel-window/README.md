# clazel-window

The host's window for Clazel's Phase 5 browser: open one, read its events and
show pixels in it. Part of [Clazel](../../README.md), a web browser whose parsers
of untrusted input carry machine-checked proofs.

Two backends behind one `Window` (`open`, `size`, `next_event`, `draw`,
`set_title`, `dpi`) and one `Event`:

- **Windows**, the first slice of [item 5.22a](../../docs/phases/phase-5.md). It
  draws with GDI, which the plan keeps for the address bar's strip. It does not
  yet have the child window or the DirectComposition surface that will show a
  page.
- **macOS on Apple silicon**, [item 5.21](../../docs/phases/phase-5.md): AppKit
  through the Objective-C runtime, with no Rust callback. Its content view hosts
  two Core Animation layers: the page's, which shows an IOSurface and clips to
  its rectangle, and the strip's above it, where `draw` puts the host's own
  pixels. It adds `show_page`, `hide_page`, `activate` and `close`.

`clazel browse` does not use it yet (item 5.23).

See it run, on Windows or on an Apple silicon Mac:

```bash
cargo run -p clazel-window --example pattern
```

Click to move the crosshair, use the wheel to shift the gradient, and resize the
window. Events are printed as they arrive.

## How it decides, on macOS

The decisions are listed at the top of [`src/appkit.rs`](src/appkit.rs) and
[`src/nsevent.rs`](src/nsevent.rs). In short:

- Everything runs on the main thread, as AppKit requires, and events are polled
  with `nextEventMatchingMask:untilDate:inMode:dequeue:`. Nothing calls back
  into Rust, so size, scale and closing are polled, and a live resize or a drag
  of the title bar holds `next_event` until it ends (the layers stay anchored to
  the top left meanwhile).
- Key events stay with us; everything else is handed back to AppKit with
  `sendEvent:` so it can move, resize and close the window.
- Positions are pixels from the content area's top left; the wheel is in
  Windows' unit (120 a notch: one line of a mouse wheel, or 40 points of a
  trackpad), in the user's scrolling direction.
- A window opens without taking the keyboard and without a Dock icon;
  `activate` makes it an ordinary application in front.

## Tests

- `src/nsevent.rs`: what each event means, on recorded events (field values
  written from `<AppKit/NSEvent.h>` and the virtual key codes), and where layers
  go. They run on every target and under Miri.
- `tests/smoke_macos.rs`, its own `main` because AppKit needs the main thread:
  opens a small window that takes no focus, draws, shows a page surface, checks
  refusals, closes it and sees `Closed`, in about half a second on an M1 Pro. It
  skips, saying so on stderr, under Miri, off Apple silicon macOS, and without a
  window server session.
- `tests/smoke.rs`: the same on Windows.
- `clazel-sys`'s own tests cover every check made before a foreign call, under
  Miri.

## Not done

- **Reading the screen back.** No test checks the pixels on screen: not the
  strip's colours and orientation, nor that a page surface larger than its
  rectangle is cut there (5.22a's hostile-surface test). Both need the screen
  read back, which on macOS needs the Screen Recording permission.
- **Whether Core Animation shows an `'RGBA'` IOSurface** (the format
  `clazel-gpu`'s Metal backend makes) correctly is untested; `'BGRA'` is the
  format it is known to show.
- **The surface from another process**: a Mach port and
  `IOSurfaceLookupFromMachPort` (5.18, 5.21a), and the GPU process's sandbox.
- **Modifiers** are not reported on either platform; 5.23's shortcuts need them.
- **Intel Macs** are not supported, as in `clazel-gpu`.

Tier 0: tests only. Every foreign call is in `clazel-sys`, which is audited.
