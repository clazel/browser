//! Frames and messages through the proven code: every variant round-trips,
//! frames respect the limit, and random bytes never decode to two different
//! encodings (the canonicity the proofs establish, checked on the real
//! binary).

use clazel_ipc::frame::codec::{decode_frame, encode_frame, payload_length};
use clazel_ipc::frame::spec::MAX_FRAME;
use clazel_ipc::message::codec::{
    MAX_BODY_CHUNK, Msg, decode_framed, decode_message, decode_renderer_message, encode_framed,
    encode_message,
};

fn all() -> Vec<Msg> {
    let t = |s: &str| s.as_bytes().to_vec();
    vec![
        Msg::CookieGet,
        Msg::CookieSet {
            cookie_string: t("a=b; Path=/"),
        },
        Msg::StorageGetItem { key: t("k") },
        Msg::StorageSetItem {
            key: t("k"),
            value: t("v\u{10151}"),
        },
        Msg::StorageRemoveItem { key: t("") },
        Msg::StorageClear,
        Msg::StorageKey { index: u64::MAX },
        Msg::StorageLength,
        Msg::Navigate {
            url: t("https://a.test/"),
        },
        Msg::Display {
            title: t("A title"),
            text: t("Some text\nand more"),
            links: vec![t("https://a.test/x"), t("https://b.test/")],
        },
        Msg::Display {
            title: Vec::new(),
            text: Vec::new(),
            links: Vec::new(),
        },
        Msg::Commit {
            url: t("https://a.test/"),
            content_type: t("text/html; charset=utf-8"),
            kind: 0,
        },
        Msg::Commit {
            url: t("https://a.test/"),
            content_type: vec![0xFF, 0x00],
            kind: 1,
        },
        Msg::Body {
            bytes: vec![0x00, 0xFF, 0x3C],
        },
        Msg::BodyEnd,
        Msg::CookieValue {
            cookie_string: t("a=b"),
        },
        Msg::StorageValue { value: None },
        Msg::StorageValue {
            value: Some(t("v")),
        },
        Msg::StorageLengthValue { length: 3 },
        Msg::Error { code: 7 },
    ]
}

#[test]
fn every_message_round_trips_through_a_frame() {
    for m in all() {
        let bytes = encode_message(&m);
        assert_eq!(decode_message(&bytes), Some(m_clone(&m)), "{m:?}");
        let frame = encode_framed(&m).unwrap_or_default();
        assert!(!frame.is_empty());
        assert_eq!(decode_framed(&frame), Some(m_clone(&m)));
        assert_eq!(decode_frame(&frame).as_deref(), Some(bytes.as_slice()));
    }
}

fn m_clone(m: &Msg) -> Msg {
    decode_message(&encode_message(m)).unwrap_or(Msg::CookieGet)
}

#[test]
fn the_kernel_decoder_takes_only_renderer_messages() {
    for m in all() {
        let bytes = encode_message(&m);
        let from_renderer = matches!(
            m,
            Msg::CookieGet
                | Msg::CookieSet { .. }
                | Msg::StorageGetItem { .. }
                | Msg::StorageSetItem { .. }
                | Msg::StorageRemoveItem { .. }
                | Msg::StorageClear
                | Msg::StorageKey { .. }
                | Msg::StorageLength
                | Msg::Navigate { .. }
                | Msg::Display { .. }
        );
        assert_eq!(
            decode_renderer_message(&bytes).is_some(),
            from_renderer,
            "{m:?}"
        );
    }
}

#[test]
fn frames_respect_the_limit() {
    let ok = vec![0u8; MAX_FRAME];
    let frame = encode_frame(&ok).unwrap_or_default();
    assert_eq!(frame.len(), MAX_FRAME + 4);
    assert_eq!(decode_frame(&frame).map(|p| p.len()), Some(MAX_FRAME));
    assert!(encode_frame(&vec![0u8; MAX_FRAME + 1]).is_none());
    assert_eq!(payload_length(&[0, 0x10, 0, 0]), Some(MAX_FRAME));
    assert_eq!(payload_length(&[0, 0x10, 0, 1]), None);
    assert_eq!(payload_length(&[0xFF, 0xFF, 0xFF, 0xFF]), None);
    // A huge declared length with no payload is rejected at once.
    assert!(decode_frame(&[0xFF, 0xFF, 0xFF, 0xFF]).is_none());
}

#[test]
fn a_largest_body_fits_one_frame() {
    let m = Msg::Body {
        bytes: vec![0xA5; MAX_BODY_CHUNK],
    };
    let frame = encode_framed(&m).unwrap_or_default();
    assert_eq!(frame.len(), MAX_FRAME + 4);
    assert_eq!(decode_framed(&frame), Some(m_clone(&m)));
    let over = Msg::Body {
        bytes: vec![0xA5; MAX_BODY_CHUNK + 1],
    };
    assert!(encode_framed(&over).is_none());
}

#[test]
fn random_bytes_decode_to_one_encoding() {
    let mut x: u64 = 0x2545_F491_4F6C_DD1D;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let all_bytes: Vec<Vec<u8>> = all().iter().map(encode_message).collect();
    let mut decoded = 0usize;
    let rounds = if cfg!(miri) { 200 } else { 50_000usize };
    for i in 0..rounds {
        let mut b = all_bytes
            .get(usize::try_from(next() % 21).unwrap_or(0))
            .cloned()
            .unwrap_or_default();
        for _ in 0..=(next() % 3) {
            let len = b.len();
            if len == 0 {
                break;
            }
            let at = usize::try_from(next()).unwrap_or(0) % len;
            if let Some(v) = b.get_mut(at) {
                *v = u8::try_from(next() % 256).unwrap_or(0);
            }
        }
        if let Some(m) = decode_message(&b) {
            decoded = decoded.saturating_add(1);
            assert_eq!(encode_message(&m), b, "case {i}: {b:02X?}");
        }
    }
    // Over 100 in the full run, and in the same proportion under Miri.
    assert!(
        decoded > rounds / 500,
        "only {decoded} mutated messages still decoded"
    );
}
