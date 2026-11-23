//! The frame header of a key frame: RFC 6386 section 9 (and its syntax in
//! section 19.1 and 19.2), the part read from the first partition by the
//! boolean decoder.
//!
//! The 10 bytes before the first partition (the uncompressed data chunk,
//! section 9.1) are parsed by `vp8/mod.rs`, which owns the byte layout of
//! the frame.

use super::bool_decoder::BoolDecoder;
use super::tables::{COEFF_UPDATE_PROBS, DEFAULT_COEFF_PROBS};

/// The token probabilities: `Prob coeff_probs [4] [8] [3] [num_dct_tokens-1]`
/// (section 13.3).
pub(crate) type CoeffProbs = [[[[u8; 11]; 3]; 8]; 4];

/// The macroblock segments (section 9.3): at most four.
pub(crate) const MAX_SEGMENTS: usize = 4;

/// The fields of section 19.2's `Frame Header` that a key frame has, in
/// the section's names.
#[derive(Debug, Clone)]
pub(crate) struct FrameHeader {
    /// `segmentation_enabled` (section 9.3).
    pub(crate) segmentation_enabled: bool,
    /// `update_mb_segmentation_map`.
    pub(crate) update_mb_segmentation_map: bool,
    /// `update_segment_feature_data`.
    pub(crate) update_segment_feature_data: bool,
    /// `segment_feature_mode`: 1 is "absolute value", 0 "delta" (section
    /// 19.2; section 9.3's prose has them the other way: ERRATA.md).
    pub(crate) segment_feature_mode: bool,
    /// `quantizer_update_value` with its sign, for each segment.
    pub(crate) quantizer_update_value: [i32; MAX_SEGMENTS],
    /// `lf_update_value` with its sign, for each segment.
    pub(crate) lf_update_value: [i32; MAX_SEGMENTS],
    /// `segment_prob`: the probabilities of `mb_segment_tree`, 255 unless
    /// sent.
    pub(crate) segment_prob: [u8; 3],
    /// `filter_type`: 1 is the simple filter (section 9.4).
    pub(crate) filter_type: bool,
    /// `loop_filter_level`, 0 to 63.
    pub(crate) loop_filter_level: i32,
    /// `sharpness_level`, 0 to 7.
    pub(crate) sharpness_level: i32,
    /// `loop_filter_adj_enable`.
    pub(crate) loop_filter_adj_enable: bool,
    /// The deltas by reference frame (`ref_frame_delta`; index 0 is the
    /// intra frame, the only one a key frame has).
    pub(crate) ref_frame_delta: [i32; 4],
    /// The deltas by prediction mode (`mb_mode_delta`; index 0 is `B_PRED`).
    pub(crate) mb_mode_delta: [i32; 4],
    /// `log2_nbr_of_dct_partitions` (section 9.5).
    pub(crate) log2_nbr_of_dct_partitions: u32,
    /// `y_ac_qi`, the base index (section 9.6).
    pub(crate) y_ac_qi: i32,
    /// `y_dc_delta`, `y2_dc_delta`, `y2_ac_delta`, `uv_dc_delta`,
    /// `uv_ac_delta`, each 0 if not present.
    pub(crate) y_dc_delta: i32,
    /// See `y_dc_delta`.
    pub(crate) y2_dc_delta: i32,
    /// See `y_dc_delta`.
    pub(crate) y2_ac_delta: i32,
    /// See `y_dc_delta`.
    pub(crate) uv_dc_delta: i32,
    /// See `y_dc_delta`.
    pub(crate) uv_ac_delta: i32,
    /// `refresh_entropy_probs`: of no matter for one frame.
    pub(crate) refresh_entropy_probs: bool,
    /// The token probabilities after `token_prob_update()`.
    pub(crate) coeff_probs: CoeffProbs,
    /// `mb_no_skip_coeff` (section 9.11).
    pub(crate) mb_no_skip_coeff: bool,
    /// `prob_skip_false`, read only if `mb_no_skip_coeff` (0 otherwise).
    pub(crate) prob_skip_false: u8,
}

impl FrameHeader {
    /// Section 19.2's `Frame Header` for a key frame, read from the start of
    /// the first partition, in the order of its table.
    pub(crate) fn read(d: &mut BoolDecoder<'_>) -> FrameHeader {
        // "if (key_frame) { color_space L(1); clamping_type L(1) }" (section
        // 9.2): "1 - Reserved for future use", and "1 - ... no clamping is
        // necessary". Both are read and ignored (listed choice 2 of
        // `vp8/mod.rs`): the decoder always clamps.
        let _color_space = d.read_flag();
        let _clamping_type = d.read_flag();
        let mut h = FrameHeader {
            segmentation_enabled: false,
            update_mb_segmentation_map: false,
            update_segment_feature_data: false,
            // If a key frame turns segmentation on but sends no feature data the
            // values are 0 and the mode is "absolute": libwebp's initial state
            // (its `ResetSegmentHeader`), which `image-webp` keeps too; the
            // reference decoder's is "delta" (listed choice 12 of `lib.rs`).
            segment_feature_mode: true,
            quantizer_update_value: [0; MAX_SEGMENTS],
            lf_update_value: [0; MAX_SEGMENTS],
            segment_prob: [255; 3],
            filter_type: false,
            loop_filter_level: 0,
            sharpness_level: 0,
            loop_filter_adj_enable: false,
            ref_frame_delta: [0; 4],
            mb_mode_delta: [0; 4],
            log2_nbr_of_dct_partitions: 0,
            y_ac_qi: 0,
            y_dc_delta: 0,
            y2_dc_delta: 0,
            y2_ac_delta: 0,
            uv_dc_delta: 0,
            uv_ac_delta: 0,
            refresh_entropy_probs: false,
            // "replaced with their defaults at the beginning of every key
            // frame" (section 9.9)
            coeff_probs: DEFAULT_COEFF_PROBS,
            mb_no_skip_coeff: false,
            prob_skip_false: 0,
        };
        // segmentation_enabled L(1); if set, update_segmentation()
        h.segmentation_enabled = d.read_flag();
        if h.segmentation_enabled {
            h.update_segmentation(d);
        }
        // filter_type L(1), loop_filter_level L(6), sharpness_level L(3)
        h.filter_type = d.read_flag();
        h.loop_filter_level = i32::try_from(d.read_literal(6)).unwrap_or(0);
        h.sharpness_level = i32::try_from(d.read_literal(3)).unwrap_or(0);
        h.mb_lf_adjustments(d);
        // log2_nbr_of_dct_partitions L(2)
        h.log2_nbr_of_dct_partitions = d.read_literal(2);
        h.quant_indices(d);
        // key frame: refresh_entropy_probs L(1)
        h.refresh_entropy_probs = d.read_flag();
        h.token_prob_update(d);
        // mb_no_skip_coeff L(1); if set, prob_skip_false L(8)
        h.mb_no_skip_coeff = d.read_flag();
        if h.mb_no_skip_coeff {
            h.prob_skip_false = u8::try_from(d.read_literal(8)).unwrap_or(0);
        }
        h
    }

    /// `update_segmentation()`.
    fn update_segmentation(&mut self, d: &mut BoolDecoder<'_>) {
        self.update_mb_segmentation_map = d.read_flag();
        self.update_segment_feature_data = d.read_flag();
        if self.update_segment_feature_data {
            self.segment_feature_mode = d.read_flag();
            // quantizer_update (flag, L(7), sign) for each of 4 segments
            for v in &mut self.quantizer_update_value {
                *v = d.read_maybe_signed(7);
            }
            // loop_filter_update (flag, L(6), sign) for each of 4 segments
            for v in &mut self.lf_update_value {
                *v = d.read_maybe_signed(6);
            }
        }
        if self.update_mb_segmentation_map {
            // "F? P(8) : 255" (section 9.3, item 5)
            for p in &mut self.segment_prob {
                *p = if d.read_flag() {
                    u8::try_from(d.read_literal(8)).unwrap_or(255)
                } else {
                    255
                };
            }
        }
    }

    /// `mb_lf_adjustments()`.
    fn mb_lf_adjustments(&mut self, d: &mut BoolDecoder<'_>) {
        self.loop_filter_adj_enable = d.read_flag();
        if self.loop_filter_adj_enable && d.read_flag() {
            // mode_ref_lf_delta_update: 4 ref_frame deltas, then 4 mb_mode
            // deltas, each (flag, L(6), sign)
            for v in &mut self.ref_frame_delta {
                *v = d.read_maybe_signed(6);
            }
            for v in &mut self.mb_mode_delta {
                *v = d.read_maybe_signed(6);
            }
        }
    }

    /// `quant_indices()` (section 9.6): `y_ac_qi` L(7), then five optional
    /// deltas (flag, L(4), sign).
    fn quant_indices(&mut self, d: &mut BoolDecoder<'_>) {
        self.y_ac_qi = i32::try_from(d.read_literal(7)).unwrap_or(0);
        self.y_dc_delta = d.read_maybe_signed(4);
        self.y2_dc_delta = d.read_maybe_signed(4);
        self.y2_ac_delta = d.read_maybe_signed(4);
        self.uv_dc_delta = d.read_maybe_signed(4);
        self.uv_ac_delta = d.read_maybe_signed(4);
    }

    /// `token_prob_update()` (sections 9.9 and 13.4): for each of the 1,056
    /// probabilities, a flag read with its update probability, and if set an
    /// 8-bit replacement. (Section 19.2's table writes the flag as `L(1)`;
    /// section 13.4 and the reference decoder read it with
    /// `coeff_update_probs`: ERRATA.md.)
    fn token_prob_update(&mut self, d: &mut BoolDecoder<'_>) {
        for (probs_i, update_i) in self.coeff_probs.iter_mut().zip(&COEFF_UPDATE_PROBS) {
            for (probs_j, update_j) in probs_i.iter_mut().zip(update_i) {
                for (probs_k, update_k) in probs_j.iter_mut().zip(update_j) {
                    for (p, &u) in probs_k.iter_mut().zip(update_k) {
                        if d.read_bool(u) {
                            *p = u8::try_from(d.read_literal(8)).unwrap_or(0);
                        }
                    }
                }
            }
        }
    }
}
