//! Kani harnesses (Tier 1) of the decoder's state machine, a child module of
//! `decoder` so that it can build any state. Compiled only under
//! `cargo kani`; the harnesses of the leaf functions are in `proofs.rs`.
//!
//! The step function itself is not one harness (the model checker does not
//! finish the whole of it, as with `clazel-gif`); each function it is made
//! of is, over any state with the invariant [`Jpeg::state_inv`]:
//!
//! - [`control_byte_any`]: one byte of the marker syntax that does not end
//!   a segment (the markers, the lengths, the bytes of a segment's body not
//!   the last).
//! - [`end_segment_any`]: the last byte of a segment other than SOF and SOS.
//! - [`finish_frame_any`], [`finish_scan_header_any`]: the frame header and
//!   the scan header, over any bytes.
//! - [`dqt_byte_any`], [`dht_byte_any`]: one byte of a table definition,
//!   Huffman tables built from at most 2 codes of each length.
//! - [`marker_code_any`]: a marker code in any phase.
//! - [`entropy_marker_any`]: a byte after `0xFF` in the entropy-coded data
//!   (restart markers, the end of the scan).
//! - [`block_bit_any`]: one bit of the entropy-coded data through the whole
//!   pipeline, block decoder, inverse DCT, store and advance.
//!
//! By induction over bytes (argued in the README, not machine-checked), a
//! byte of entropy-coded data is at most 8 such bits.

use super::*;

/// A state of the decoder for an 8 by 8 image with a work buffer of
/// `WORK` bytes, in phase `phase`, every other field symbolic or
/// concrete as each harness needs.
const WORK: usize = 256;

fn base() -> Option<Jpeg> {
    let config = Config::new(Format::Jpeg, 8, 8, FRAMES).ok()?;
    let mut j = Jpeg::start(&config).ok()?;
    // The harness's work buffer is 256 bytes, not the 6,084 `work_len`
    // would be: the model checker follows every access into the array.
    j.work_len = WORK;
    Some(j)
}

fn any_comp() -> Comp {
    Comp {
        id: kani::any(),
        h: kani::any(),
        v: kani::any(),
        tq: kani::any(),
        width: kani::any(),
        height: kani::any(),
        blocks_w: kani::any(),
        blocks_h: kani::any(),
        off: kani::any(),
        q: kani::any(),
        dc_sel: kani::any(),
        ac_sel: kani::any(),
        pred: kani::any(),
        done: kani::any(),
    }
}

/// The part of the state that does not depend on the phase: the segment
/// being read, the tables being read, the frame, with every field symbolic.
fn any_state() -> Option<Jpeg> {
    let mut j = base()?;
    j.marker = kani::any();
    j.len_hi = kani::any();
    j.seg_total = kani::any();
    j.seg_pos = kani::any();
    j.hold = kani::any();
    j.dq_stage = kani::any();
    j.dq_wide = kani::any();
    j.dq_tq = kani::any();
    j.dq_k = kani::any();
    j.dq_hi = if kani::any() { Some(kani::any()) } else { None };
    j.ht_stage = kani::any();
    j.ht_class = kani::any();
    j.ht_i = kani::any();
    j.ht_counts = kani::any();
    j.ht_syms = kani::any();
    j.ht_total = kani::any();
    j.restart_interval = kani::any();
    j.jfif = kani::any();
    j.adobe = if kani::any() { Some(kani::any()) } else { None };
    j.orientation = kani::any();
    j.seen_orientation = kani::any();
    j.qt = kani::any();
    j.qt_def = kani::any();
    j.frame_set = kani::any();
    j.width = kani::any();
    j.height = kani::any();
    j.ncomp = kani::any();
    j.hmax = kani::any();
    j.vmax = kani::any();
    j.mcus_x = kani::any();
    j.mcus_y = kani::any();
    j.comps = [any_comp(), any_comp(), any_comp(), any_comp()];
    j.planes_len = kani::any();
    j.bits = BitReader::with(kani::any(), kani::any());
    j.ff = kani::any();
    j.scan = Scan {
        n: kani::any(),
        comp: kani::any(),
        interleaved: kani::any(),
        per_mcu: kani::any(),
        mcus_x: kani::any(),
        mcus_y: kani::any(),
        mx: kani::any(),
        my: kani::any(),
        bi: kani::any(),
        in_interval: kani::any(),
        next_rst: kani::any(),
        state: match kani::any::<u8>() % 3 {
            0 => ScanState::Decoding,
            1 => ScanState::AwaitRestart,
            _ => ScanState::Complete,
        },
    };
    j.block = Block::any_block(match kani::any::<u8>() % 4 {
        0 => crate::block::Stage::DcCode,
        1 => crate::block::Stage::DcBits,
        2 => crate::block::Stage::AcCode,
        _ => crate::block::Stage::AcBits,
    });
    // Huffman tables: each slot is empty or the same small built table
    // (the construction is `huffman_build_any`'s).
    let table = {
        let mut counts = [0u8; 16];
        counts[0] = 2;
        Table::build(&counts, &[0, 1], false).ok()
    };
    for i in 0..4 {
        j.dc[i] = if kani::any() { table } else { None };
        j.ac[i] = if kani::any() { table } else { None };
    }
    Some(j)
}

/// The same, in a phase chosen among `phases`.
fn any_in(phases: &[Phase]) -> Option<Jpeg> {
    let mut j = any_state()?;
    let which: usize = kani::any();
    kani::assume(which < phases.len());
    j.phase = *phases.get(which)?;
    Some(j)
}

fn bounded_ht(j: &Jpeg) {
    // The Huffman tables being read hold at most 2 codes of each length.
    kani::assume(j.ht_counts.iter().all(|&c| c <= 2));
    kani::assume(j.ht_counts.iter().map(|&c| u32::from(c)).sum::<u32>() <= 6);
}

/// One byte of the marker syntax that does not finish a segment.
#[kani::proof]
#[kani::unwind(6)]
fn control_byte_any() {
    let Some(mut j) = any_in(&[
        Phase::Soi0,
        Phase::Soi1,
        Phase::Marker0,
        Phase::Marker1,
        Phase::Len0,
        Phase::Len1,
        Phase::Segment,
    ]) else {
        return;
    };
    kani::assume(j.state_inv());
    let b: u8 = kani::any();
    // Not a byte that finishes a segment (`end_segment_any`,
    // `finish_frame_any` and `finish_scan_header_any` are those), and no
    // table is being read in a way that completes one here (`dqt_byte_any`
    // and `dht_byte_any`).
    if j.phase == Phase::Len1 {
        kani::assume(u16::from_be_bytes([j.len_hi, b]) > 2);
    }
    if j.phase == Phase::Segment {
        kani::assume(j.seg_pos.saturating_add(1) < j.seg_total);
        kani::assume(!matches!(j.marker, 0xDB | 0xC4));
    }
    bounded_ht(&j);
    if j.control_byte(b).is_ok() {
        assert!(j.state_inv());
    }
}

/// The last byte of a segment that is neither SOF nor SOS nor a table.
#[kani::proof]
fn end_segment_any() {
    let Some(mut j) = any_in(&[Phase::Segment, Phase::Len1]) else {
        return;
    };
    kani::assume(j.state_inv());
    kani::assume(!matches!(j.marker, 0xC0 | 0xC1 | 0xDA));
    if j.end_segment().is_ok() {
        assert!(j.state_inv());
    }
}

/// The frame header, over any bytes.
#[kani::proof]
#[kani::unwind(6)]
fn finish_frame_any() {
    let Some(mut j) = any_in(&[Phase::Segment]) else {
        return;
    };
    kani::assume(j.state_inv());
    kani::assume(!j.frame_set);
    if j.finish_frame().is_ok() {
        assert!(j.state_inv());
        assert!(j.frame_set);
    }
}

/// The scan header, over any bytes and any frame with the invariant.
#[kani::proof]
#[kani::unwind(6)]
fn finish_scan_header_any() {
    let Some(mut j) = any_in(&[Phase::Segment]) else {
        return;
    };
    kani::assume(j.state_inv());
    kani::assume(j.frame_set);
    if j.finish_scan_header().is_ok() {
        assert!(j.phase == Phase::Entropy);
        assert!(j.state_inv());
    }
}

/// One byte of a DQT body.
#[kani::proof]
fn dqt_byte_any() {
    let Some(mut j) = any_in(&[Phase::Segment]) else {
        return;
    };
    kani::assume(j.state_inv());
    let b: u8 = kani::any();
    if j.dqt_byte(b).is_ok() {
        assert!(j.state_inv());
    }
}

/// One byte of a DHT body, completing a table or not.
#[kani::proof]
#[kani::solver(kissat)]
#[kani::unwind(19)]
fn dht_byte_any() {
    let Some(mut j) = any_in(&[Phase::Segment]) else {
        return;
    };
    kani::assume(j.state_inv());
    bounded_ht(&j);
    let b: u8 = kani::any();
    if j.dht_byte(b).is_ok() {
        assert!(j.state_inv());
    }
}

/// A marker code, in any phase.
#[kani::proof]
fn marker_code_any() {
    let Some(mut j) = any_in(&[Phase::Marker1, Phase::Entropy, Phase::Marker0]) else {
        return;
    };
    kani::assume(j.state_inv());
    let m: u8 = kani::any();
    if j.marker_code(m).is_ok() {
        assert!(j.state_inv());
    }
}

/// A byte after `0xFF` in the entropy-coded data: a restart marker, the end
/// of the scan, a fill byte.
#[kani::proof]
fn entropy_marker_any() {
    let Some(mut j) = any_in(&[Phase::Entropy]) else {
        return;
    };
    kani::assume(j.state_inv());
    j.ff = true;
    let b: u8 = kani::any();
    kani::assume(b != 0x00);
    let mut work = [0u8; WORK];
    if j.entropy_byte(b, &mut work).is_ok() {
        assert!(j.state_inv());
    }
}

/// One bit of entropy-coded data through block decoding, the inverse DCT,
/// the store into the plane and the move to the next block.
#[kani::proof]
#[kani::solver(kissat)]
#[kani::unwind(10)]
fn block_bit_any() {
    let Some(mut j) = any_in(&[Phase::Entropy]) else {
        return;
    };
    kani::assume(j.state_inv());
    kani::assume(j.scan.state == ScanState::Decoding);
    let bit: u8 = kani::any();
    kani::assume(bit <= 1);
    let mut work: [u8; WORK] = kani::any();
    if j.block_bit(bit, &mut work).is_ok() {
        assert!(j.state_inv());
    }
}
