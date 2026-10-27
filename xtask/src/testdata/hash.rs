//! The hashes the ECDSA conformance converters need: the digest of a vendored
//! message, as lower-case hex.

use sha1::Sha1;
use sha2::{Digest, Sha224, Sha256, Sha384, Sha512};

/// Lower-case hex of `bytes`.
pub fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The octets of an even-length hex string.
pub fn from_hex(s: &str) -> Result<Vec<u8>, String> {
    if !s.len().is_multiple_of(2) || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!("not even-length hex: {s:?}"));
    }
    s.as_bytes()
        .chunks(2)
        .map(|p| {
            let text = std::str::from_utf8(p).map_err(|e| e.to_string())?;
            u8::from_str_radix(text, 16).map_err(|e| format!("{text:?}: {e}"))
        })
        .collect()
}

/// The digest of `msg` under the hash named `sha` (`SHA-1`, `SHA-224`,
/// `SHA-256`, `SHA-384` or `SHA-512`), as the octets of FIPS 180-4's output.
pub fn digest(sha: &str, msg: &[u8]) -> Result<Vec<u8>, String> {
    Ok(match sha {
        "SHA-1" => Sha1::digest(msg).to_vec(),
        "SHA-224" => Sha224::digest(msg).to_vec(),
        "SHA-256" => Sha256::digest(msg).to_vec(),
        "SHA-384" => Sha384::digest(msg).to_vec(),
        "SHA-512" => Sha512::digest(msg).to_vec(),
        other => return Err(format!("unknown hash {other:?}")),
    })
}

#[cfg(test)]
mod tests {
    use super::{digest, from_hex, to_hex};

    #[test]
    fn known_answers() {
        // FIPS 180 example messages: "abc".
        let cases = [
            ("SHA-1", "a9993e364706816aba3e25717850c26c9cd0d89d"),
            (
                "SHA-224",
                "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7",
            ),
            (
                "SHA-256",
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                "SHA-384",
                "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7",
            ),
            (
                "SHA-512",
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f",
            ),
        ];
        for (sha, want) in cases {
            let got = digest(sha, b"abc").map(|d| to_hex(&d));
            assert_eq!(got.as_deref(), Ok(want), "{sha}");
        }
        assert!(digest("MD5", b"").is_err());
    }

    #[test]
    fn hex_round_trip() {
        assert_eq!(
            from_hex("00ff10").map(|b| to_hex(&b)),
            Ok("00ff10".to_owned())
        );
        assert!(from_hex("abc").is_err());
        assert!(from_hex("zz").is_err());
    }
}
