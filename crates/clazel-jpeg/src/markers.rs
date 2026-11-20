//! The marker codes of T.81 Annex B (Table B.1) and what this decoder does
//! with each. Both `decode_config` and the step function classify a marker
//! with [`kind`], so they cannot disagree about which markers are legal.

/// What a marker code means to this decoder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
    /// `TEM` (0x01) and `RSTn` (0xD0 to 0xD7) outside entropy-coded data:
    /// no segment follows; ignored (libjpeg-turbo does the same).
    Standalone,
    /// SOI, 0xD8.
    Soi,
    /// EOI, 0xD9.
    Eoi,
    /// SOF0 (baseline) and SOF1 (extended sequential, Huffman): decoded
    /// when the precision is 8 bits.
    Frame,
    /// SOS, 0xDA.
    Scan,
    /// A segment with a length that is read for its content: DHT, DQT, DRI
    /// and APP0, APP1, APP14.
    Read,
    /// A segment with a length whose content is skipped: the other APPn,
    /// COM, and JPGn.
    Skip,
    /// A valid marker of a coding process this decoder does not have.
    Unsupported(&'static str),
    /// Not a marker a decoder should meet (reserved, or an escape).
    Invalid,
}

/// Classifies marker code `m` (the byte after `0xFF`).
pub(crate) fn kind(m: u8) -> Kind {
    match m {
        0x01 | 0xD0..=0xD7 => Kind::Standalone,
        0xD8 => Kind::Soi,
        0xD9 => Kind::Eoi,
        0xC0 | 0xC1 => Kind::Frame,
        0xC2 => Kind::Unsupported("progressive JPEG (SOF2) is item 6.6, not built yet"),
        0xC3 | 0xC7 | 0xCB | 0xCF => Kind::Unsupported("lossless JPEG"),
        0xC5 | 0xC6 | 0xCD | 0xCE => Kind::Unsupported("hierarchical JPEG"),
        0xC9 | 0xCA | 0xCC => Kind::Unsupported("arithmetic-coded JPEG"),
        0xC8 => Kind::Unsupported("JPEG extensions (JPG)"),
        0xDC..=0xDF if m != 0xDD => Kind::Unsupported("DNL, DHP or EXP segments"),
        0xDA => Kind::Scan,
        0xC4 | 0xDB | 0xDD | 0xE0 | 0xE1 | 0xEE => Kind::Read,
        0xE2..=0xED | 0xEF | 0xF0..=0xFE => Kind::Skip,
        _ => Kind::Invalid,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_code_is_classified() {
        for m in 0..=255u8 {
            let k = kind(m);
            // The markers the introduction of the standard lists.
            match m {
                0xC0 | 0xC1 => assert_eq!(k, Kind::Frame),
                0xC4 | 0xDB | 0xDD => assert_eq!(k, Kind::Read),
                0xD0..=0xD7 => assert_eq!(k, Kind::Standalone),
                0xD8 => assert_eq!(k, Kind::Soi),
                0xD9 => assert_eq!(k, Kind::Eoi),
                0xDA => assert_eq!(k, Kind::Scan),
                0xE0 | 0xE1 | 0xEE => assert_eq!(k, Kind::Read),
                0xE2..=0xED | 0xEF | 0xFE => assert_eq!(k, Kind::Skip),
                0xC2 => assert!(matches!(k, Kind::Unsupported(w) if w.contains("progressive"))),
                0x00 | 0xFF | 0x02..=0xBF => assert_eq!(k, Kind::Invalid),
                _ => {}
            }
        }
    }
}
