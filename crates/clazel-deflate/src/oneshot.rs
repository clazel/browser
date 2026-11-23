//! Decoding a whole stream held in memory: the resumable decoder driven to
//! the end, which is what `spec::inflate` and `spec::zlib_decompress` say.

use super::spec::Error;
use super::stream::{Format, Inflater, Status, WINDOW_LEN};

/// The output and the number of input bytes the stream occupies.
pub type Decoded = (Vec<u8>, usize);

fn run(format: Format, input: &[u8], limit: u64) -> Result<Decoded, Error> {
    let mut inflater = Inflater::new(format, limit);
    let mut window = vec![0u8; WINDOW_LEN];
    let mut out: Vec<u8> = Vec::new();
    let mut chunk = vec![0u8; 16384];
    let mut used = 0usize;
    loop {
        let rest = input.get(used..).unwrap_or(&[]);
        let step = inflater.step(rest, &mut chunk, &mut window);
        used = used.saturating_add(step.consumed);
        out.extend_from_slice(chunk.get(..step.produced).unwrap_or(&[]));
        match step.status {
            Status::Done => return Ok((out, used)),
            Status::Failed(e) => return Err(e),
            Status::NeedOutput => {}
            Status::NeedInput | Status::BadWindow => {
                // All of the input was given; the stream is not complete.
                return match inflater.end_of_input() {
                    Err(e) => Err(e),
                    Ok(()) => Err(Error::Truncated),
                };
            }
        }
    }
}

/// Decode a raw DEFLATE stream: [`spec::inflate`](super::spec::inflate).
pub fn inflate(input: &[u8], limit: u64) -> Result<Decoded, Error> {
    run(Format::Raw, input, limit)
}

/// Decode a zlib stream: [`spec::zlib_decompress`](super::spec::zlib_decompress).
pub fn zlib_decompress(input: &[u8], limit: u64) -> Result<Decoded, Error> {
    run(Format::Zlib, input, limit)
}
