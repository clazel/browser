//! The encoder and the reply parser against exchanges written out by hand from
//! Appendix B of the protocol document: each request's bytes are listed field by
//! field, and each event is built at the offsets the appendix gives. No exchange
//! recorded from a server is stored here; the check against a real server is the
//! smoke test (`tests/smoke_x11.rs`), which opens a window on one.

use super::*;

/// A setup reply with one format (depth 24, 32 bits per pixel) and one screen
/// with one depth holding `visuals`, the root visual being `root_visual`.
fn setup_bytes(
    lsb_first: bool,
    (depth, bpp): (u8, u8),
    root_visual: u32,
    visuals: &[(u32, u8, (u32, u32, u32))],
) -> Vec<u8> {
    let vendor = b"clazel test"; // 11 bytes, padded to 12
    let mut b = vec![1, 0];
    b.extend_from_slice(&11u16.to_le_bytes());
    b.extend_from_slice(&0u16.to_le_bytes());
    b.extend_from_slice(&0u16.to_le_bytes()); // length, filled below
    b.extend_from_slice(&12_101_012u32.to_le_bytes()); // release-number
    b.extend_from_slice(&0x0040_0000u32.to_le_bytes()); // resource-id-base
    b.extend_from_slice(&0x001F_FFFFu32.to_le_bytes()); // resource-id-mask
    b.extend_from_slice(&256u32.to_le_bytes()); // motion-buffer-size
    b.extend_from_slice(&11u16.to_le_bytes()); // vendor length
    b.extend_from_slice(&65_535u16.to_le_bytes()); // maximum-request-length
    b.extend_from_slice(&[1, 1]); // screens, formats
    b.extend_from_slice(&[u8::from(!lsb_first), 0, 32, 32, 8, 255]);
    b.extend_from_slice(&[0; 4]);
    b.extend_from_slice(vendor);
    b.push(0);
    b.extend_from_slice(&[depth, bpp, 32, 0, 0, 0, 0, 0]); // FORMAT
    // SCREEN
    b.extend_from_slice(&0x0000_0123u32.to_le_bytes()); // root
    b.extend_from_slice(&0x20u32.to_le_bytes()); // default-colormap
    b.extend_from_slice(&0x00FF_FFFFu32.to_le_bytes()); // white-pixel
    b.extend_from_slice(&0u32.to_le_bytes()); // black-pixel
    b.extend_from_slice(&0u32.to_le_bytes()); // current-input-masks
    b.extend_from_slice(&[0; 12]); // sizes and installed maps
    b.extend_from_slice(&root_visual.to_le_bytes());
    b.extend_from_slice(&[0, 0, depth, 1]); // backing-stores, save-unders, root-depth, depths
    // DEPTH
    b.extend_from_slice(&[depth, 0]);
    b.extend_from_slice(&u16::try_from(visuals.len()).unwrap_or(0).to_le_bytes());
    b.extend_from_slice(&[0; 4]);
    for (id, class, (r, g, bl)) in visuals {
        b.extend_from_slice(&id.to_le_bytes());
        b.extend_from_slice(&[*class, 8]);
        b.extend_from_slice(&256u16.to_le_bytes());
        b.extend_from_slice(&r.to_le_bytes());
        b.extend_from_slice(&g.to_le_bytes());
        b.extend_from_slice(&bl.to_le_bytes());
        b.extend_from_slice(&[0; 4]);
    }
    let units = u16::try_from(b.len().saturating_sub(8) / 4).unwrap_or(0);
    if let Some(length) = b.get_mut(6..8) {
        length.copy_from_slice(&units.to_le_bytes());
    }
    b
}

const RGB: (u32, u32, u32) = (0x00FF_0000, 0x0000_FF00, 0x0000_00FF);

#[test]
fn display_names_are_local_or_refused() {
    assert_eq!(display_number(":0"), Some(0));
    assert_eq!(display_number(":99.0"), Some(99));
    assert_eq!(display_number("unix:1"), Some(1));
    assert_eq!(display_number("example.org:0"), None);
    assert_eq!(display_number("localhost:10.0"), None);
    assert_eq!(display_number(":"), None);
    assert_eq!(display_number(":x"), None);
    assert_eq!(display_number(":-1"), None);
    assert_eq!(display_number("0"), None);
    assert_eq!(display_number(""), None);
    assert_eq!(socket_path(7), "/tmp/.X11-unix/X7");
}

fn auth_entry(family: u16, address: &[u8], number: &[u8], name: &[u8], data: &[u8]) -> Vec<u8> {
    let mut b = family.to_be_bytes().to_vec();
    for field in [address, number, name, data] {
        b.extend_from_slice(&u16::try_from(field.len()).unwrap_or(0).to_be_bytes());
        b.extend_from_slice(field);
    }
    b
}

#[test]
fn the_authority_file_is_big_endian_counted_strings() {
    let mut file = auth_entry(FAMILY_LOCAL, b"box", b"0", b"MIT-MAGIC-COOKIE-1", &[1; 16]);
    file.extend(auth_entry(
        FAMILY_LOCAL,
        b"box",
        b"1",
        b"MIT-MAGIC-COOKIE-1",
        &[2; 16],
    ));
    file.extend(auth_entry(
        FAMILY_LOCAL,
        b"other",
        b"2",
        b"MIT-MAGIC-COOKIE-1",
        &[3; 16],
    ));
    file.extend(auth_entry(
        FAMILY_WILD,
        b"",
        b"",
        b"XDM-AUTHORIZATION-1",
        &[4; 16],
    ));
    file.extend(auth_entry(
        FAMILY_WILD,
        b"",
        b"3",
        b"MIT-MAGIC-COOKIE-1",
        &[5; 16],
    ));
    let entries = parse_xauthority(&file);
    assert_eq!(entries.len(), 5);
    assert_eq!(
        entries.first().map(|e| e.address.as_slice()),
        Some(&b"box"[..])
    );
    assert_eq!(cookie_for(&entries, b"box", 0), Some(&[1u8; 16][..]));
    assert_eq!(cookie_for(&entries, b"box", 1), Some(&[2u8; 16][..]));
    // Another host's entry for the display is used when this host has none.
    assert_eq!(cookie_for(&entries, b"box", 2), Some(&[3u8; 16][..]));
    // A wild entry matches any host; another protocol's entry is never used.
    assert_eq!(cookie_for(&entries, b"box", 3), Some(&[5u8; 16][..]));
    assert_eq!(cookie_for(&entries, b"box", 4), None);
    // A file cut inside an entry gives the entries before the cut.
    for cut in 0..file.len() {
        let got = parse_xauthority(file.get(..cut).unwrap_or(&[]));
        assert!(got.len() <= 4, "cut at {cut}");
        assert_eq!(got.as_slice(), entries.get(..got.len()).unwrap_or(&[]));
    }
    assert!(parse_xauthority(&[]).is_empty());
}

#[test]
fn the_setup_request_is_appendix_bs() {
    let none = setup_request(b"", b"");
    assert_eq!(none, Some(vec![0x6C, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0]));
    let with = setup_request(MIT_MAGIC_COOKIE, &[7; 16]).unwrap_or_default();
    // 12 bytes, the 18-byte name padded to 20, the 16-byte cookie.
    assert_eq!(with.len(), 12 + 20 + 16);
    assert_eq!(with.get(6..10), Some(&[18, 0, 16, 0][..]));
    assert_eq!(with.get(12..30), Some(MIT_MAGIC_COOKIE));
    assert_eq!(with.get(30..32), Some(&[0, 0][..]));
    assert_eq!(with.get(32..), Some(&[7u8; 16][..]));
}

#[test]
fn a_setup_reply_gives_the_root_and_its_visual() {
    let visuals = [(0x21, 4, RGB), (0x22, 5, RGB)];
    let bytes = setup_bytes(true, (24, 32), 0x22, &visuals);
    assert_eq!(setup_rest_len(&bytes), Some(bytes.len().saturating_sub(8)));
    let parsed = parse_setup(&bytes);
    assert!(matches!(parsed, Some(SetupReply::Success(_))), "{parsed:?}");
    let Some(SetupReply::Success(s)) = parsed else {
        return;
    };
    assert_eq!(s.root, 0x123);
    assert_eq!((s.id_base, s.id_mask), (0x0040_0000, 0x001F_FFFF));
    assert_eq!(s.max_request_units, 65_535);
    assert_eq!(s.max_request_bytes(), 262_140);
    assert_eq!((s.min_keycode, s.max_keycode), (8, 255));
    assert_eq!((s.root_depth, s.bits_per_pixel), (24, 32));
    assert_eq!((s.visual_class, s.masks), (5, RGB));
    assert_eq!(s.white_pixel, 0x00FF_FFFF);
    assert_eq!(s.usable(), Ok(()));
    assert_eq!(s.resource_id(0), Some(0x0040_0000));
    assert_eq!(s.resource_id(5), Some(0x0040_0005));
    assert_eq!(s.resource_id(0x001F_FFFF), Some(0x005F_FFFF));
    assert_eq!(s.resource_id(0x0020_0000), None);
    // Every cut of the reply is refused, not read past (but for the root
    // visual's last 4 bytes, which are unused and not read).
    for cut in 0..bytes.len().saturating_sub(4) {
        assert_eq!(
            parse_setup(bytes.get(..cut).unwrap_or(&[])),
            None,
            "cut at {cut}"
        );
    }
}

#[test]
fn servers_this_client_cannot_draw_on_are_refused() {
    let parse = |b: &[u8]| match parse_setup(b) {
        Some(SetupReply::Success(s)) => Some(s.usable().is_ok()),
        _ => None,
    };
    let ok = [(0x21, 4, RGB)];
    assert_eq!(parse(&setup_bytes(true, (24, 32), 0x21, &ok)), Some(true));
    assert_eq!(parse(&setup_bytes(false, (24, 32), 0x21, &ok)), Some(false));
    assert_eq!(parse(&setup_bytes(true, (16, 16), 0x21, &ok)), Some(false));
    assert_eq!(parse(&setup_bytes(true, (24, 24), 0x21, &ok)), Some(false));
    let bgr = [(0x21, 4, (0xFF, 0xFF00, 0x00FF_0000))];
    assert_eq!(parse(&setup_bytes(true, (24, 32), 0x21, &bgr)), Some(false));
    let pseudo = [(0x21, 3, RGB)];
    assert_eq!(
        parse(&setup_bytes(true, (24, 32), 0x21, &pseudo)),
        Some(false)
    );
    // A root visual that no depth lists is not a reply this client can use.
    assert_eq!(parse(&setup_bytes(true, (24, 32), 0x99, &ok)), None);
}

#[test]
fn a_refusal_carries_the_servers_reason() {
    // Failed: status 0, a 6-byte reason, versions, 2 units of data.
    let mut failed = vec![0, 6, 11, 0, 0, 0, 2, 0];
    failed.extend_from_slice(b"No way\0\0");
    assert_eq!(setup_rest_len(&failed), Some(8));
    assert_eq!(
        parse_setup(&failed),
        Some(SetupReply::Refused("No way".to_owned()))
    );
    // Authenticate: status 2, the reason NUL-padded.
    let mut auth = vec![2, 0, 0, 0, 0, 0, 1, 0];
    auth.extend_from_slice(b"more");
    assert_eq!(
        parse_setup(&auth),
        Some(SetupReply::Refused("more".to_owned()))
    );
}

#[test]
fn requests_are_appendix_bs_bytes() {
    let mut out = Vec::new();
    let g = Geometry {
        x: -2,
        y: 3,
        width: 640,
        height: 480,
    };
    assert_eq!(
        create_window(&mut out, 0x0040_0001, 0x123, g, 0x00FF_FFFF, 0x0002_8005),
        Some(())
    );
    #[rustfmt::skip]
    let want: Vec<u8> = vec![
        1, 0, 11, 0,            // CreateWindow, depth CopyFromParent, 11 units
        1, 0, 0x40, 0,          // wid
        0x23, 1, 0, 0,          // parent
        0xFE, 0xFF, 3, 0,       // x, y
        0x80, 2, 0xE0, 1,       // width, height
        0, 0, 0, 0,             // border-width, class
        0, 0, 0, 0,             // visual
        0x12, 8, 0, 0,          // value-mask
        0xFF, 0xFF, 0xFF, 0,    // background-pixel
        1, 0, 0, 0,             // bit-gravity
        5, 0x80, 2, 0,          // event-mask
    ];
    assert_eq!(out, want);

    out.clear();
    assert_eq!(map_window(&mut out, 0x0040_0001), Some(()));
    assert_eq!(out, [8, 0, 2, 0, 1, 0, 0x40, 0]);
    out.clear();
    assert_eq!(unmap_window(&mut out, 7), Some(()));
    assert_eq!(out, [10, 0, 2, 0, 7, 0, 0, 0]);
    out.clear();
    assert_eq!(destroy_window(&mut out, 7), Some(()));
    assert_eq!(out, [4, 0, 2, 0, 7, 0, 0, 0]);

    out.clear();
    assert_eq!(configure_window(&mut out, 9, g), Some(()));
    #[rustfmt::skip]
    let want: Vec<u8> = vec![
        12, 0, 7, 0,  9, 0, 0, 0,  0x0F, 0, 0, 0,
        0xFE, 0xFF, 0xFF, 0xFF,  3, 0, 0, 0,  0x80, 2, 0, 0,  0xE0, 1, 0, 0,
    ];
    assert_eq!(out, want);

    out.clear();
    assert_eq!(intern_atom(&mut out, b"WM_PROTOCOLS"), Some(()));
    let mut want = vec![16, 0, 5, 0, 12, 0, 0, 0];
    want.extend_from_slice(b"WM_PROTOCOLS");
    assert_eq!(out, want);
    out.clear();
    assert_eq!(intern_atom(&mut out, b"ATOMS"), Some(()));
    assert_eq!(out.len(), 16);
    assert_eq!(out.get(2..4), Some(&[4, 0][..]));
    assert_eq!(out.get(13..), Some(&[0, 0, 0][..]));

    out.clear();
    assert_eq!(
        change_property_bytes(&mut out, 9, ATOM_WM_NAME, ATOM_STRING, b"Clazel"),
        Some(())
    );
    #[rustfmt::skip]
    let want: Vec<u8> = vec![
        18, 0, 8, 0,  9, 0, 0, 0,  39, 0, 0, 0,  31, 0, 0, 0,
        8, 0, 0, 0,  6, 0, 0, 0,  b'C', b'l', b'a', b'z', b'e', b'l', 0, 0,
    ];
    assert_eq!(out, want);

    out.clear();
    assert_eq!(
        change_property_atoms(&mut out, 9, 0x150, &[0x151]),
        Some(())
    );
    #[rustfmt::skip]
    let want: Vec<u8> = vec![
        18, 0, 7, 0,  9, 0, 0, 0,  0x50, 1, 0, 0,  4, 0, 0, 0,
        32, 0, 0, 0,  1, 0, 0, 0,  0x51, 1, 0, 0,
    ];
    assert_eq!(out, want);

    out.clear();
    assert_eq!(create_gc(&mut out, 0x0040_0002, 9), Some(()));
    assert_eq!(out, [55, 0, 4, 0, 2, 0, 0x40, 0, 9, 0, 0, 0, 0, 0, 0, 0]);

    out.clear();
    assert_eq!(get_keyboard_mapping(&mut out, 8, 248), Some(()));
    assert_eq!(out, [101, 0, 2, 0, 8, 248, 0, 0]);
}

#[test]
fn put_image_sends_a_tile_of_the_image() {
    // A 3 by 2 image; the tile is its right 2 columns, both rows.
    let pixels = [0x0011_2233, 1, 2, 3, 4, 5];
    let tile = Tile {
        x: 1,
        y: 0,
        width: 2,
        height: 2,
    };
    let mut out = Vec::new();
    assert_eq!(
        put_image(&mut out, (9, 10, 24), &pixels, 3, tile, (100, -5)),
        Some(())
    );
    #[rustfmt::skip]
    let want: Vec<u8> = vec![
        72, 2, 10, 0,           // PutImage, ZPixmap, 6 + 4 units
        9, 0, 0, 0,  10, 0, 0, 0,
        2, 0, 2, 0,             // width, height
        101, 0, 0xFB, 0xFF,     // dst-x 100 + 1, dst-y -5
        0, 24, 0, 0,            // left-pad, depth
        1, 0, 0, 0,  2, 0, 0, 0,  4, 0, 0, 0,  5, 0, 0, 0,
    ];
    assert_eq!(out, want);
    // The first pixel is its four little-endian bytes: blue first.
    let first = Tile {
        x: 0,
        y: 0,
        width: 1,
        height: 1,
    };
    out.clear();
    assert_eq!(
        put_image(&mut out, (9, 10, 24), &pixels, 3, first, (0, 0)),
        Some(())
    );
    assert_eq!(out.get(24..), Some(&[0x33, 0x22, 0x11, 0][..]));
    // A tile outside the image is refused.
    let outside = Tile {
        x: 2,
        y: 0,
        width: 2,
        height: 2,
    };
    out.clear();
    assert_eq!(
        put_image(&mut out, (9, 10, 24), &pixels, 3, outside, (0, 0)),
        None
    );
}

#[test]
fn tiles_cover_the_image_once_and_fit_the_request() {
    for (w, h, max) in [
        (1024u32, 768u32, 262_140usize),
        (1024, 768, 16_384),
        (8192, 3, 16_384),
        (1, 1, 28),
        (5, 7, 24 + 4 * 3),
        (300, 2, 262_140),
    ] {
        let ts = tiles(w, h, max);
        let area = usize::try_from(u64::from(w).saturating_mul(u64::from(h))).unwrap_or(0);
        let mut seen = vec![0u8; area];
        for t in &ts {
            let bytes = u64::from(t.width)
                .saturating_mul(u64::from(t.height))
                .saturating_mul(4)
                .saturating_add(24);
            assert!(
                usize::try_from(bytes).is_ok_and(|b| b <= max),
                "{w} {h} {max}"
            );
            assert!(t.width > 0 && t.height > 0);
            for y in t.y..t.y.saturating_add(t.height) {
                for x in t.x..t.x.saturating_add(t.width) {
                    let at = u64::from(y)
                        .saturating_mul(u64::from(w))
                        .saturating_add(u64::from(x));
                    let slot = usize::try_from(at).ok().and_then(|i| seen.get_mut(i));
                    assert!(slot.is_some(), "a tile outside the image");
                    if let Some(n) = slot {
                        *n = n.saturating_add(1);
                    }
                }
            }
        }
        assert!(seen.iter().all(|n| *n == 1), "{w} by {h} at {max}");
    }
    // 1024 by 768 at the usual limit: 63 rows a request, 13 requests.
    assert_eq!(tiles(1024, 768, 262_140).len(), 13);
    assert!(tiles(0, 5, 1000).is_empty());
    assert!(tiles(5, 5, 24).is_empty());
}

fn event(code: u8, detail: u8, fill: &[(usize, &[u8])]) -> [u8; 32] {
    let mut e = [0u8; 32];
    for (at, bytes) in [(0usize, &[code, detail][..])].iter().chain(fill) {
        for (slot, b) in e.iter_mut().skip(*at).zip(*bytes) {
            *slot = *b;
        }
    }
    e
}

#[test]
fn events_are_read_where_appendix_b_puts_them() {
    let key = event(2, 46, &[(28, &[5, 0])]);
    assert_eq!(
        parse_event(&key),
        Some(Raw::Key {
            keycode: 46,
            state: 5
        })
    );
    let button = event(
        4,
        1,
        &[(12, &[9, 0, 0, 0]), (24, &[0x2C, 1]), (26, &[0xFF, 0xFF])],
    );
    assert_eq!(
        parse_event(&button),
        Some(Raw::Button {
            button: 1,
            x: 300,
            y: -1,
            window: 9
        })
    );
    let expose = event(12, 0, &[(4, &[9, 0, 0, 0]), (16, &[2, 0])]);
    assert_eq!(
        parse_event(&expose),
        Some(Raw::Expose {
            window: 9,
            last: false
        })
    );
    let configure = event(22, 0, &[(8, &[9, 0, 0, 0]), (20, &[0, 4]), (22, &[0, 3])]);
    assert_eq!(
        parse_event(&configure),
        Some(Raw::Configure {
            window: 9,
            width: 1024,
            height: 768
        })
    );
    let destroyed = event(17, 0, &[(8, &[9, 0, 0, 0])]);
    assert_eq!(parse_event(&destroyed), Some(Raw::Destroyed { window: 9 }));
    let client = event(
        33,
        32,
        &[
            (4, &[9, 0, 0, 0]),
            (8, &[0x50, 1, 0, 0]),
            (12, &[0x51, 1, 0, 0]),
        ],
    );
    assert_eq!(
        parse_event(&client),
        Some(Raw::Client {
            window: 9,
            kind: 0x150,
            first: 0x151
        })
    );
    // A ClientMessage of another format, and one sent by another client.
    assert_eq!(parse_event(&event(33, 8, &[])), None);
    let mut sent = client;
    if let Some(code) = sent.first_mut() {
        *code |= 0x80;
    }
    assert!(matches!(parse_event(&sent), Some(Raw::Client { .. })));
    assert_eq!(
        parse_event(&event(34, 0, &[(4, &[1])])),
        Some(Raw::KeyboardMapping)
    );
    assert_eq!(parse_event(&event(34, 0, &[(4, &[2])])), None);
    assert_eq!(
        parse_event(&event(0, 3, &[(2, &[7, 0])])),
        Some(Raw::Error {
            code: 3,
            sequence: 7
        })
    );
    // KeyRelease, MapNotify and an unknown code mean nothing here.
    for code in [3, 19, 100] {
        assert_eq!(parse_event(&event(code, 0, &[])), None);
    }
    assert_eq!(parse_event(&[2; 31]), None);
}

#[test]
fn a_reply_says_how_long_it_is() {
    assert_eq!(message_len(&event(2, 0, &[])), Some(32));
    assert_eq!(message_len(&event(0, 0, &[])), Some(32));
    assert_eq!(message_len(&event(1, 0, &[(4, &[3, 0, 0, 0])])), Some(44));
    assert_eq!(message_len(&event(35, 0, &[(4, &[1, 0, 0, 0])])), Some(36));
    assert_eq!(message_len(&[]), None);
    let atom = event(1, 0, &[(8, &[0x50, 1, 0, 0])]);
    assert_eq!(atom_of(&atom), Some(0x150));
    assert_eq!(atom_of(&event(1, 0, &[])), None);
}

/// A US layout's rows for the keycodes used below, as `xmodmap -pk` prints them
/// from Xvfb: keycode 38 is `a A`, 46 `l L`, 10 `1 exclam`, 36 `Return`, 65
/// `space`, 34 `bracketleft braceleft`, 90 `KP_Insert KP_0`.
fn us_keymap() -> Keymap {
    let mut keysyms = vec![0u32; (91 - 8) * 2];
    let mut set = |keycode: usize, plain: u32, shifted: u32| {
        let at = keycode.saturating_sub(8).saturating_mul(2);
        for (slot, sym) in keysyms.iter_mut().skip(at).zip([plain, shifted]) {
            *slot = sym;
        }
    };
    set(38, 0x61, 0x41);
    set(46, 0x6C, 0x4C);
    set(10, 0x31, 0x21);
    set(36, 0xFF0D, 0);
    set(65, 0x20, 0);
    set(34, 0x5B, 0x7B);
    set(90, 0xFF9E, 0xFFB0);
    set(24, 0x0100_044F, 0); // Cyrillic ya, as a Unicode keysym, with no second
    Keymap {
        first: 8,
        per_keycode: 2,
        keysyms,
    }
}

#[test]
fn keys_type_what_shift_and_lock_say() {
    let map = us_keymap();
    assert_eq!(key_symbols(&map, 38, 0), (0x61, Some('a')));
    assert_eq!(key_symbols(&map, 38, SHIFT), (0x61, Some('A')));
    assert_eq!(key_symbols(&map, 38, LOCK), (0x61, Some('A')));
    assert_eq!(key_symbols(&map, 10, SHIFT), (0x31, Some('!')));
    // Lock does not shift a digit.
    assert_eq!(key_symbols(&map, 10, LOCK), (0x31, Some('1')));
    assert_eq!(key_symbols(&map, 46, CONTROL), (0x6C, Some('l')));
    assert_eq!(key_symbols(&map, 36, 0), (0xFF0D, None));
    assert_eq!(key_symbols(&map, 65, SHIFT), (0x20, Some(' ')));
    assert_eq!(key_symbols(&map, 34, 0), (0x5B, Some('[')));
    assert_eq!(key_symbols(&map, 90, SHIFT), (0xFF9E, Some('0')));
    // One keysym and Shift: its upper case.
    assert_eq!(key_symbols(&map, 24, SHIFT), (0x0100_044F, Some('Я')));
    // A keycode outside the map, and a column past it.
    assert_eq!(key_symbols(&map, 7, 0), (0, None));
    assert_eq!(key_symbols(&map, 200, 0), (0, None));
    assert_eq!(map.keysym(38, 2), 0);
}

#[test]
fn a_keyboard_mapping_reply_is_its_keysyms() {
    let mut reply = event(1, 2, &[(4, &[2, 0, 0, 0])]).to_vec();
    reply.extend_from_slice(&0x61u32.to_le_bytes());
    reply.extend_from_slice(&0x41u32.to_le_bytes());
    let map = parse_keyboard_mapping(&reply, 38).unwrap_or_default();
    assert_eq!(map.per_keycode, 2);
    assert_eq!((map.keysym(38, 0), map.keysym(38, 1)), (0x61, 0x41));
    assert_eq!(parse_keyboard_mapping(&[1, 2], 8), None);
}

#[test]
fn keysyms_are_characters_where_appendix_a_says() {
    assert_eq!(keysym_char(0x41), Some('A'));
    assert_eq!(keysym_char(0xE9), Some('é'));
    assert_eq!(keysym_char(0x0100_20AC), Some('€'));
    assert_eq!(keysym_char(0xFFAA), Some('*'));
    assert_eq!(keysym_char(0xFFB9), Some('9'));
    assert_eq!(keysym_char(0xFF0D), None); // Return
    assert_eq!(keysym_char(0x06C1), None); // Cyrillic_a, a legacy keysym
    assert_eq!(keysym_char(0x7F), None);
    assert_eq!(keysym_char(0x0100_D800), None); // a surrogate
}

#[test]
fn titles_are_cut_and_made_latin_1() {
    assert_eq!(latin1("Café — ok"), b"Caf\xE9 ? ok");
    assert_eq!(utf8("Café"), "Café".as_bytes());
    let long = "é".repeat(MAX_TITLE);
    assert_eq!(utf8(&long).len(), MAX_TITLE);
    assert!(std::str::from_utf8(utf8(&long)).is_ok());
    let odd = format!("a{long}");
    assert_eq!(utf8(&odd).len(), MAX_TITLE - 1);
    assert_eq!(latin1(&long).len(), MAX_TITLE);
}
