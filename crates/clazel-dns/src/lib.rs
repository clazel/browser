//! DNS message format, formally verified with Verus.
//!
//! Spec: RFC 1035 "Domain Names - Implementation and Specification"
//! (November 1987, <https://www.rfc-editor.org/rfc/rfc1035>) §2.3, §3, §4;
//! RFC 1034 §3.6.2 and §5.3.3; RFC 3596 (AAAA); RFC 5452 §4 to §6 for
//! accepting a reply. Tier: see `[package.metadata.clazel]` in `Cargo.toml`
//! and `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a transcription of the standards, as spec functions.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`resolv`]: the `nameserver` lines of `/etc/resolv.conf` (a grammar of
//!   our own).
//! - [`adapters`]: the DNS servers in the buffer Windows' `GetAdaptersAddresses`
//!   fills (C structures of the Windows SDK, not a standard).
//! - [`answer`], [`decode`], [`encode`] and [`types`]: the executable
//!   functions and the types they return.
//! - [`lemmas`], [`examples`] and [`independent`]: facts proven about the
//!   spec, its examples evaluated by Verus, and a second transcription from
//!   RFC 883 proven equal to the decoder.
//!
//! ```
//! use clazel_dns::answer::answer_addresses;
//! use clazel_dns::decode::decode_udp;
//! use clazel_dns::encode::encode_query;
//! use clazel_dns::spec::Addr;
//!
//! // The query a stub resolver sends for example.com, type A, with ID 0x1234.
//! let query = encode_query(0x1234, b"example.com", 1).expect("a valid name");
//! assert_eq!(query.len(), 29);
//!
//! // A reply: header, the question, and one answer whose owner is a pointer
//! // to the question's name.
//! let reply: &[u8] = &[
//!     0x12, 0x34, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, // header
//!     7, b'e', b'x', b'a', b'm', b'p', b'l', b'e', 3, b'c', b'o', b'm', 0, 0, 1, 0, 1, // question
//!     0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 104, 20, 23, 154, // A 104.20.23.154
//! ];
//! let message = decode_udp(reply).expect("a valid reply");
//! let answer = answer_addresses(0x1234, b"example.com", 1, &message).expect("an answer");
//! assert_eq!(answer.addresses, [Addr::V4(u32::from_be_bytes([104, 20, 23, 154]))]);
//! assert_eq!(answer.redirect, None);
//!
//! // A reply with another ID is not an answer.
//! assert!(answer_addresses(0x4321, b"example.com", 1, &message).is_none());
//! ```

pub mod adapters;
pub mod answer;
pub mod contract;
pub mod decode;
pub mod encode;
pub mod examples;
pub mod independent;
pub mod lemmas;
pub mod resolv;
pub mod spec;
pub mod types;
