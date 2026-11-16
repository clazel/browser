# clazel-image-shape

The decoder interface of [Clazel](../../README.md)'s Phase 6 (item 6.3,
`docs/phases/phase-6.md`): the one shape every image decoder implements (GIF,
PNG, JPEG, WebP, and 6.11a's SVG), in the style of WUFFS. No decoder, no
policy, **no dependencies**.

## What it holds

- `Decoder` (`src/lib.rs`): `decode_config(prefix)` (format, width, height,
  frame count if known, or `NeedMore`), `work_len(config)` (the work buffer's
  size, a function of the config the decoder states), `start(config)`,
  `step(state, chunk, buffers)` returning `NeedMore`, `FrameDone` or an
  error, and the invariant `inv(state, buffers)`. Nothing allocates: the
  caller owns the pixel and work buffers and sizes them from the config.
- `Buffers` (`src/buffers.rs`): the pixel buffer (straight RGBA8, row-major,
  4 bytes per pixel) and the work buffer, cut to exactly the lengths the
  config and the decoder imply.
- Size limits (`src/size.rs`, decision 6.0(j)): `MAX_SIDE` = 2^14,
  `MAX_PIXELS` = 2^26, and `rgba_len(width, height)`, checked.
- `premultiply`, `premultiply_in_place` (`src/premultiply.rs`): straight to
  premultiplied RGBA8, `round(c * a / 255)`.
- `decoder_step_harness!` (`src/harness.rs`): the Kani template, below.
- `src/toy.rs`: a toy decoder of the raw format `width, height, pixels`,
  implementing the interface (chunk boundaries inside a pixel, a work
  buffer, `inv`), tested at every chunk size and instantiating the template.

## Why a crate of its own

The plan said module `shape` of `clazel-image` (tier 0). `clazel-image`
dispatches to the decoders, which implement the shape: a cycle. And a tier 1
decoder resting on a tier 0 crate would rest on code with no harness. This
crate is the small part both need, and its target is tier 1.

## The harness template

A decoder crate writes, under `#[cfg(kani)]`:

```rust
clazel_image_shape::decoder_step_harness! {
    #[kani::proof]
    #[kani::unwind(18)]
    fn step_any for MyDecoder {
        max_chunk: 8, max_pixels: 16, max_work: 4,
        any_state: any_my_decoder,   // fn() -> Option<MyDecoder>
    }
}
```

and gets a harness that states, for any state satisfying `inv`, any buffer
contents and any chunk up to `max_chunk` bytes, with a pixel buffer up to
`max_pixels` and a work buffer up to `max_work`: one `step` does not panic,
overflow or index out of bounds; writes only inside the buffers (bytes of the
backing arrays past them are unchanged); keeps `inv` on `Ok` and on `Err`;
and obeys the contract (`consumed <= chunk.len()`, `NeedMore` consumes it
all). Three parameters are the instantiator's bounds, and a decoder whose
state is too large at its real sizes proves the step at small ones and says
so in its own README.

## Kani harnesses (`src/proofs.rs`)

| Harness | Bound |
|---------|-------|
| `size_any` | every `u32` pair: `rgba_len` and `pixel_count` are `Ok` exactly within 6.0(j)'s limits, equal `4wh`, and name the first limit broken |
| `premultiply_channel_any` | every channel and alpha: exact rounding, never saturates, at most `c` and `a`, identity at 255, zero at 0 |
| `premultiply_pixel_any` | any pixel keeps its alpha |
| `premultiply_in_place_any_3` | any 3 pixels |
| `premultiply_in_place_partial` | any 2 pixels and 3 trailing bytes (left alone) |
| `toy_step_any` | the template on the toy decoder: images up to 2 by 2, chunks up to 8 bytes |

Not covered: `premultiply_in_place` over a long slice (its loop is
`as_chunks_mut` over `premultiply`, both covered; the unit tests run longer
ones). The checker counts the textual `#[kani::proof]` attributes; the
template has none, each instantiation brings its own.

The tier stays 0 until CI's full verification has run these green.

## Decisions

- Crate of its own, no dependencies (above).
- Pixels are straight RGBA8; premultiplication is a separate, explicit step.
- `decode_config` is a function of a prefix, not a state: the caller keeps the
  bytes and decides how much to keep (policy).
- The stream is fed from its first byte after `decode_config`.
- `FrameDone` carries nothing; frame timing and disposal are added by the GIF,
  APNG and WebP items against 6.0(d).
- One shared `Error` enum, reasons as static strings.
- `inv` must hold after an error too (an errored decoder is `Spent`).
