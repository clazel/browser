//! The Kani harness template every tier 1 decoder instantiates.
//!
//! [`decoder_step_harness!`] expands, in the decoder's crate, to a function
//! that states, for **any** state satisfying [`Decoder::inv`], any contents
//! of the pixel and work buffers and any chunk of up to a stated length:
//!
//! 1. one [`Decoder::step`] does not panic, overflow or index out of
//!    bounds (Kani's built-in checks);
//! 2. it writes only inside the buffers: the bytes of the backing arrays
//!    beyond `buffers.pixels` and `buffers.work` are unchanged (the arrays
//!    are bigger than the buffers, so a stray write would show);
//! 3. it keeps `inv`, whether it returns `Ok` or `Err`;
//! 4. on `Ok`, `consumed <= chunk.len()`, and `Status::NeedMore` consumed
//!    the whole chunk (a caller loop makes progress).
//!
//! The macro expands in the instantiating crate, so that the crate (not this
//! one) names `kani`, and a decoder crate needs no dependency for it. Use it
//! under `#[cfg(kani)]`, in the decoder's `proofs.rs`. The attributes are
//! given at the call site, so each instantiation is a `#[kani::proof]` the
//! tier checker counts. See `src/toy.rs` of this crate for a complete
//! instantiation and its documentation of each parameter:
//!
//! ```ignore
//! clazel_image_shape::decoder_step_harness! {
//!     #[kani::proof]
//!     #[kani::unwind(18)]
//!     fn step_any for MyDecoder {
//!         max_chunk: 8,       // the longest chunk, in bytes
//!         max_pixels: 16,     // the longest pixel buffer the state may imply
//!         max_work: 4,        // the longest work buffer the state may imply
//!         any_state: any_my_decoder, // fn() -> Option<MyDecoder>, fields symbolic
//!     }
//! }
//! ```
//!
//! `any_state` returns `Some` of a state whose fields are `kani::any()`,
//! with no assumptions except those that bound its buffers by `max_pixels`
//! and `max_work`, or `None` where it cannot build one (for example when
//! `Config::new` refuses a symbolic size; the harness then proves nothing
//! for that case, which is right). The harness itself assumes `inv`, so the
//! invariant is the only thing that restricts the state. If `inv` is too weak for `step` to be
//! safe the harness fails, which is its purpose.
//!
//! What this does not state: that the output is *right* (a decoder's tests
//! and differential do that), and that every state `inv` admits is reachable
//! (it is only an over-approximation, so the harness is sound).
//!
//! [`Decoder::inv`]: crate::Decoder::inv
//! [`Decoder::step`]: crate::Decoder::step

/// Instantiates the step harness; see the [module](self) documentation.
#[macro_export]
macro_rules! decoder_step_harness {
    (
        $(#[$meta:meta])*
        fn $name:ident for $decoder:ty {
            max_chunk: $max_chunk:expr,
            max_pixels: $max_pixels:expr,
            max_work: $max_work:expr,
            any_state: $any_state:path $(,)?
        }
    ) => {
        $(#[$meta])*
        fn $name() {
            const CHUNK: usize = $max_chunk;
            const PIXELS: usize = $max_pixels;
            const WORK: usize = $max_work;

            let Some(mut state): Option<$decoder> = $any_state() else {
                return;
            };

            // The buffer sizes the state's config implies.
            let Ok(plen) = $crate::Decoder::config(&state).rgba_len() else {
                return;
            };
            let Ok(wlen) = <$decoder as $crate::Decoder>::work_len($crate::Decoder::config(&state))
            else {
                return;
            };
            kani::assume(plen <= PIXELS && wlen <= WORK);

            // Arrays bigger than the buffers' lengths, any contents; the
            // bytes past the cut are the canary for a stray write.
            let mut pixel_array: [u8; PIXELS] = kani::any();
            let mut work_array: [u8; WORK] = kani::any();
            let pixels_before = pixel_array;
            let work_before = work_array;

            let chunk_array: [u8; CHUNK] = kani::any();
            let chunk_len: usize = kani::any();
            kani::assume(chunk_len <= CHUNK);
            let Some(chunk) = chunk_array.get(..chunk_len) else {
                return;
            };

            {
                let (Some(pixels), Some(work)) =
                    (pixel_array.get_mut(..plen), work_array.get_mut(..wlen))
                else {
                    return;
                };
                let mut buffers = $crate::Buffers { pixels, work };

                // For any state satisfying the invariant.
                kani::assume($crate::Decoder::inv(&state, &buffers));

                let result = $crate::Decoder::step(&mut state, chunk, &mut buffers);

                // The invariant is kept on every outcome.
                assert!($crate::Decoder::inv(&state, &buffers));
                // The buffers keep their lengths.
                assert!(buffers.pixels.len() == plen && buffers.work.len() == wlen);
                // The step's contract.
                if let Ok(step) = result {
                    assert!(step.consumed <= chunk_len);
                    if step.status == $crate::Status::NeedMore {
                        assert!(step.consumed == chunk_len);
                    }
                }
            }

            // Nothing outside the buffers changed.
            assert!(pixel_array.get(plen..) == pixels_before.get(plen..));
            assert!(work_array.get(wlen..) == work_before.get(wlen..));
        }
    };
}
