//! The X11 core protocol as the Linux window speaks it (phase-5.md item 5.22):
//! the bytes of each request it sends, and what the server's bytes mean, as
//! pure functions that every target can test. The socket is `crate::x11`'s.
//!
//! # Source
//!
//! *X Window System Protocol*, X Version 11, Release 7 (the X.Org Foundation's
//! `x11protocol`, version 1.0 of the document, as shipped with X11R7.7).
//! Section numbers are the document's: §8 "Connection Setup", §9 "Requests",
//! §11 "Events", Appendix B "Protocol Encoding" (the byte layouts every
//! function here cites), and Appendix A "KEYSYM Encoding". The authorization
//! file's format is not part of the protocol: it is `Xau(3)`'s (libXau,
//! "Xau library: X authority database routines"), cited where it is read.
//!
//! # Modelling choices (ours, each listed)
//!
//! - **Little-endian client.** The setup request says `l` (0x6C), so every
//!   multi-byte value is least significant byte first, in both directions.
//! - **Core protocol only.** No extension is queried or used, so no extension
//!   event, error or generic event is expected; one that arrived would still be
//!   framed correctly ([`message_len`]).
//! - **One visual shape.** The window copies the root window's depth and visual,
//!   and pixels are sent only if that visual is TrueColor or DirectColor with
//!   masks `0xFF0000`, `0x00FF00`, `0x0000FF`, the depth is 24 or 32 with 32 bits
//!   per pixel, and the image byte order is least significant first: then a
//!   pixel `0x00RRGGBB` is its four little-endian bytes. Every X server on
//!   today's hardware offers this; another is refused, saying so ([`Setup::usable`]).
//! - **`PutImage` is split** into tiles that fit the server's maximum request
//!   length ([`tiles`]); BIG-REQUESTS is not used.
//! - **Keysyms to characters** ([`keysym_char`]): Latin-1 keysyms are their own
//!   code points, `0x01000000 + c` is the Unicode character `c`, and the keypad
//!   digits and operators are their ASCII characters. The older per-script
//!   keysym ranges (Latin-2, Greek, Cyrillic and so on, Appendix A) are not
//!   translated, so a layout that still reports those types nothing for them.
//! - **Shift and Lock** ([`key_symbols`]): the second keysym of a keycode with
//!   Shift; with none there, or with Lock, the first keysym's upper case if it
//!   is a letter. Groups (Mode_switch) and NumLock are not read.
//! - **Local displays only**: `DISPLAY` must name a Unix socket (`:0`, `:1.0`,
//!   `unix:0`); a host name means TCP, which this client does not speak.

/// A request's opcode (Appendix B, "Requests").
mod opcode {
    pub const CREATE_WINDOW: u8 = 1;
    pub const DESTROY_WINDOW: u8 = 4;
    pub const MAP_WINDOW: u8 = 8;
    pub const UNMAP_WINDOW: u8 = 10;
    pub const CONFIGURE_WINDOW: u8 = 12;
    pub const INTERN_ATOM: u8 = 16;
    pub const CHANGE_PROPERTY: u8 = 18;
    pub const CREATE_GC: u8 = 55;
    pub const PUT_IMAGE: u8 = 72;
    pub const GET_KEYBOARD_MAPPING: u8 = 101;
}

/// The predefined atom `ATOM` (Appendix B, "Predefined Atoms").
pub const ATOM_ATOM: u32 = 4;
/// The predefined atom `STRING`.
pub const ATOM_STRING: u32 = 31;
/// The predefined atom `WM_NAME`.
pub const ATOM_WM_NAME: u32 = 39;
/// The predefined atom `WM_CLASS`.
pub const ATOM_WM_CLASS: u32 = 67;

/// Event masks (§11, Appendix B "SETofEVENT").
pub const KEY_PRESS_MASK: u32 = 0x0000_0001;
/// `ButtonPress`.
pub const BUTTON_PRESS_MASK: u32 = 0x0000_0004;
/// `Exposure`.
pub const EXPOSURE_MASK: u32 = 0x0000_8000;
/// `StructureNotify`.
pub const STRUCTURE_NOTIFY_MASK: u32 = 0x0002_0000;

/// Modifier bits of an event's `state` (Appendix B, "SETofKEYBUTMASK").
pub const SHIFT: u16 = 0x0001;
/// `Lock`.
pub const LOCK: u16 = 0x0002;
/// `Control`.
pub const CONTROL: u16 = 0x0004;

/// The longest title sent, in bytes of UTF-8.
pub const MAX_TITLE: usize = 4096;

fn u16_at(b: &[u8], at: usize) -> Option<u16> {
    let s = b.get(at..at.checked_add(2)?)?;
    Some(u16::from_le_bytes(s.try_into().ok()?))
}

fn u32_at(b: &[u8], at: usize) -> Option<u32> {
    let s = b.get(at..at.checked_add(4)?)?;
    Some(u32::from_le_bytes(s.try_into().ok()?))
}

fn i16_at(b: &[u8], at: usize) -> Option<i16> {
    u16_at(b, at).map(u16::cast_signed)
}

/// `n` rounded up to a multiple of 4 (Appendix B: "pad(E) = (4 - (E mod 4)) mod 4").
fn padded(n: usize) -> Option<usize> {
    n.checked_add(3).map(|m| m & !3)
}

/// Append `bytes` and zero padding to a multiple of 4.
fn push_padded(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(bytes);
    let pad = padded(bytes.len()).map_or(0, |p| p.saturating_sub(bytes.len()));
    out.extend(std::iter::repeat_n(0u8, pad));
}

/// A request's 4-byte header: opcode, one data byte, and the request's length in
/// 4-byte units (`None` if it does not fit 16 bits).
fn header(out: &mut Vec<u8>, opcode: u8, data: u8, bytes: usize) -> Option<()> {
    let units = u16::try_from(bytes.checked_div(4)?).ok()?;
    out.push(opcode);
    out.push(data);
    out.extend_from_slice(&units.to_le_bytes());
    Some(())
}

/// Which display `DISPLAY` names, if it is a local one: its number.
///
/// `[unix]:<number>[.<screen>]` (X(7), "Display Names"); the screen is ignored
/// (the first screen is used). A host name is refused.
pub fn display_number(display: &str) -> Option<u32> {
    let (host, rest) = display.rsplit_once(':')?;
    if !(host.is_empty() || host == "unix") {
        return None;
    }
    let number = rest.split_once('.').map_or(rest, |(n, _)| n);
    if number.is_empty() || !number.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    number.parse().ok()
}

/// The Unix socket of display `number` (X(7): `/tmp/.X11-unix/X<number>`).
pub fn socket_path(number: u32) -> String {
    format!("/tmp/.X11-unix/X{number}")
}

/// One entry of an authorization file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthEntry {
    /// The address family: 256 is `FamilyLocal`, 65535 `FamilyWild` (`Xauth.h`).
    pub family: u16,
    /// The address: for `FamilyLocal`, the host's name.
    pub address: Vec<u8>,
    /// The display number, in ASCII digits; empty matches every display.
    pub number: Vec<u8>,
    /// The authorization's name, such as `MIT-MAGIC-COOKIE-1`.
    pub name: Vec<u8>,
    /// Its data.
    pub data: Vec<u8>,
}

/// `FamilyLocal` (`<X11/Xauth.h>`).
pub const FAMILY_LOCAL: u16 = 256;
/// `FamilyWild`.
pub const FAMILY_WILD: u16 = 65535;
/// The one authorization this client offers.
pub const MIT_MAGIC_COOKIE: &[u8] = b"MIT-MAGIC-COOKIE-1";

/// Xau(3), "XauReadAuth": an authorization file is entries of a 2-byte family and
/// four counted strings (address, number, name, data), each a 2-byte length then
/// that many bytes, **most significant byte first** whatever the machine. A file
/// that ends inside an entry yields the entries before it.
pub fn parse_xauthority(bytes: &[u8]) -> Vec<AuthEntry> {
    fn be16(b: &[u8], at: usize) -> Option<u16> {
        let s = b.get(at..at.checked_add(2)?)?;
        Some(u16::from_be_bytes(s.try_into().ok()?))
    }
    fn counted(b: &[u8], at: &mut usize) -> Option<Vec<u8>> {
        let n = usize::from(be16(b, *at)?);
        let start = at.checked_add(2)?;
        let end = start.checked_add(n)?;
        let s = b.get(start..end)?.to_vec();
        *at = end;
        Some(s)
    }
    let mut entries = Vec::new();
    let mut at = 0usize;
    while at < bytes.len() {
        let entry = (|| {
            let family = be16(bytes, at)?;
            let mut next = at.checked_add(2)?;
            let address = counted(bytes, &mut next)?;
            let number = counted(bytes, &mut next)?;
            let name = counted(bytes, &mut next)?;
            let data = counted(bytes, &mut next)?;
            Some((
                AuthEntry {
                    family,
                    address,
                    number,
                    name,
                    data,
                },
                next,
            ))
        })();
        match entry {
            Some((e, next)) => {
                entries.push(e);
                at = next;
            }
            None => break,
        }
    }
    entries
}

/// The cookie for display `number` on host `hostname`: the first
/// `MIT-MAGIC-COOKIE-1` entry that is local to this host (or wild) and for this
/// display (or every display); failing that, the first local one for this
/// display under any host name, since a container or a renamed machine keeps the
/// file its session wrote. `None` means no authorization is sent.
pub fn cookie_for<'a>(entries: &'a [AuthEntry], hostname: &[u8], number: u32) -> Option<&'a [u8]> {
    let digits = number.to_string();
    let for_display = |e: &&AuthEntry| {
        e.name == MIT_MAGIC_COOKIE && (e.number.is_empty() || e.number == digits.as_bytes())
    };
    let exact = entries
        .iter()
        .filter(for_display)
        .find(|e| e.family == FAMILY_WILD || (e.family == FAMILY_LOCAL && e.address == hostname));
    let any_local = entries
        .iter()
        .filter(for_display)
        .find(|e| e.family == FAMILY_LOCAL);
    exact.or(any_local).map(|e| e.data.as_slice())
}

/// §8 and Appendix B "Connection Setup": the client's first bytes, offering
/// `name` and `data` as its authorization (both empty for none).
pub fn setup_request(name: &[u8], data: &[u8]) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    out.push(0x6C); // byte-order: least significant byte first
    out.push(0);
    out.extend_from_slice(&11u16.to_le_bytes()); // protocol-major-version
    out.extend_from_slice(&0u16.to_le_bytes()); // protocol-minor-version
    out.extend_from_slice(&u16::try_from(name.len()).ok()?.to_le_bytes());
    out.extend_from_slice(&u16::try_from(data.len()).ok()?.to_le_bytes());
    out.extend_from_slice(&[0, 0]);
    push_padded(&mut out, name);
    push_padded(&mut out, data);
    Some(out)
}

/// How many more bytes follow the first 8 of the server's setup reply (Appendix
/// B "Connection Setup": bytes 6 and 7 are the length of the rest in 4-byte
/// units, for every status).
pub fn setup_rest_len(first8: &[u8]) -> Option<usize> {
    usize::from(u16_at(first8, 6)?).checked_mul(4)
}

/// What the server said to the setup request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SetupReply {
    /// Status 1: the connection is open.
    Success(Setup),
    /// Status 0 (failed) or 2 (further authentication, which this client does
    /// not do), with the server's reason.
    Refused(String),
}

/// What the client keeps of a successful setup.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Setup {
    /// `resource-id-base`.
    pub id_base: u32,
    /// `resource-id-mask`.
    pub id_mask: u32,
    /// `maximum-request-length`, in 4-byte units.
    pub max_request_units: u16,
    /// `min-keycode`.
    pub min_keycode: u8,
    /// `max-keycode`.
    pub max_keycode: u8,
    /// `image-byte-order` is `LSBFirst`.
    pub lsb_first: bool,
    /// The first screen's root window.
    pub root: u32,
    /// The first screen's `white-pixel`.
    pub white_pixel: u32,
    /// The first screen's `root-depth`.
    pub root_depth: u8,
    /// The bits per pixel of the pixmap format for `root_depth`.
    pub bits_per_pixel: u8,
    /// The root visual's class (4 is TrueColor, 5 DirectColor).
    pub visual_class: u8,
    /// The root visual's red, green and blue masks.
    pub masks: (u32, u32, u32),
}

impl Setup {
    /// Whether `0x00RRGGBB` pixels can be sent as they are (see the module
    /// documentation), or what the server lacks.
    pub fn usable(&self) -> Result<(), &'static str> {
        if !self.lsb_first {
            return Err("an X server whose image byte order is least significant first");
        }
        if !(self.root_depth == 24 || self.root_depth == 32) || self.bits_per_pixel != 32 {
            return Err("a root window of depth 24 or 32 with 32 bits per pixel");
        }
        if !(self.visual_class == 4 || self.visual_class == 5)
            || self.masks != (0x00FF_0000, 0x0000_FF00, 0x0000_00FF)
        {
            return Err("a TrueColor root visual with 8-bit red, green and blue");
        }
        if self.id_mask == 0 {
            return Err("an X server that gives resource ids");
        }
        Ok(())
    }

    /// The `n`th resource id this client may use (§8: an id is the base with
    /// some of the mask's bits set; the mask's bits are contiguous), or `None`
    /// when they are used up.
    pub fn resource_id(&self, n: u32) -> Option<u32> {
        let shift = self.id_mask.trailing_zeros();
        let bits = n.checked_shl(shift)?;
        if bits & !self.id_mask != 0 || bits.checked_shr(shift)? != n {
            return None;
        }
        Some(self.id_base | bits)
    }

    /// The most bytes one request may have.
    pub fn max_request_bytes(&self) -> usize {
        usize::from(self.max_request_units).saturating_mul(4)
    }
}

/// Appendix B "Connection Setup": the whole reply (its first 8 bytes and the
/// rest). `None` if it is cut short or names no screen, format or visual that
/// the rest refers to.
pub fn parse_setup(reply: &[u8]) -> Option<SetupReply> {
    let status = *reply.first()?;
    if status != 1 {
        // Failed: byte 1 is the reason's length and it starts at 8.
        // Authenticate: the reason fills the rest, padded with NULs.
        let n = if status == 0 {
            usize::from(*reply.get(1)?)
        } else {
            reply.len().saturating_sub(8)
        };
        let reason = reply.get(8..8usize.checked_add(n)?.min(reply.len()))?;
        let text = String::from_utf8_lossy(reason)
            .trim_end_matches('\0')
            .to_owned();
        return Some(SetupReply::Refused(text));
    }
    let id_base = u32_at(reply, 12)?;
    let id_mask = u32_at(reply, 16)?;
    let vendor_len = usize::from(u16_at(reply, 24)?);
    let max_request_units = u16_at(reply, 26)?;
    let screens = *reply.get(28)?;
    let formats = usize::from(*reply.get(29)?);
    let lsb_first = *reply.get(30)? == 0;
    let min_keycode = *reply.get(34)?;
    let max_keycode = *reply.get(35)?;
    let formats_at = 40usize.checked_add(padded(vendor_len)?)?;
    let screen_at = formats_at.checked_add(formats.checked_mul(8)?)?;
    if screens == 0 {
        return None;
    }
    // SCREEN.
    let root = u32_at(reply, screen_at)?;
    let white_pixel = u32_at(reply, screen_at.checked_add(8)?)?;
    let root_visual = u32_at(reply, screen_at.checked_add(32)?)?;
    let root_depth = *reply.get(screen_at.checked_add(38)?)?;
    let depths = *reply.get(screen_at.checked_add(39)?)?;
    // FORMAT: depth, bits-per-pixel, scanline-pad, 5 unused.
    let bits_per_pixel = (0..formats).find_map(|i| {
        let at = formats_at.checked_add(i.checked_mul(8)?)?;
        (*reply.get(at)? == root_depth)
            .then(|| reply.get(at.checked_add(1)?).copied())
            .flatten()
    })?;
    // DEPTHs, each: depth, unused, a count of VISUALTYPEs, 4 unused, then that
    // many VISUALTYPEs of 24 bytes.
    let mut at = screen_at.checked_add(40)?;
    let mut visual = None;
    for _ in 0..depths {
        let count = usize::from(u16_at(reply, at.checked_add(2)?)?);
        let mut v = at.checked_add(8)?;
        for _ in 0..count {
            if u32_at(reply, v)? == root_visual {
                visual = Some((
                    *reply.get(v.checked_add(4)?)?,
                    (
                        u32_at(reply, v.checked_add(8)?)?,
                        u32_at(reply, v.checked_add(12)?)?,
                        u32_at(reply, v.checked_add(16)?)?,
                    ),
                ));
            }
            v = v.checked_add(24)?;
        }
        at = v;
    }
    let (visual_class, masks) = visual?;
    Some(SetupReply::Success(Setup {
        id_base,
        id_mask,
        max_request_units,
        min_keycode,
        max_keycode,
        lsb_first,
        root,
        white_pixel,
        root_depth,
        bits_per_pixel,
        visual_class,
        masks,
    }))
}

/// A rectangle of a window: its top left corner in its parent, and its size.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Geometry {
    /// From the parent's left edge.
    pub x: i16,
    /// From the parent's top edge.
    pub y: i16,
    /// Its width, at least 1.
    pub width: u16,
    /// Its height, at least 1.
    pub height: u16,
}

/// Appendix B "CreateWindow": an `InputOutput` child of `parent` with the
/// parent's depth and visual (`CopyFromParent`), no border, a background pixel,
/// the `NorthWest` bit gravity (so what is drawn stays where it is when the
/// window grows), and `events` selected.
pub fn create_window(
    out: &mut Vec<u8>,
    window: u32,
    parent: u32,
    g: Geometry,
    background: u32,
    events: u32,
) -> Option<()> {
    // value-mask: background-pixel (0x2), bit-gravity (0x10), event-mask (0x800),
    // their values in that order.
    header(out, opcode::CREATE_WINDOW, 0, 32 + 12)?;
    out.extend_from_slice(&window.to_le_bytes());
    out.extend_from_slice(&parent.to_le_bytes());
    out.extend_from_slice(&g.x.to_le_bytes());
    out.extend_from_slice(&g.y.to_le_bytes());
    out.extend_from_slice(&g.width.to_le_bytes());
    out.extend_from_slice(&g.height.to_le_bytes());
    out.extend_from_slice(&0u16.to_le_bytes()); // border-width
    out.extend_from_slice(&0u16.to_le_bytes()); // class: CopyFromParent
    out.extend_from_slice(&0u32.to_le_bytes()); // visual: CopyFromParent
    out.extend_from_slice(&0x0000_0812u32.to_le_bytes());
    out.extend_from_slice(&background.to_le_bytes());
    out.extend_from_slice(&1u32.to_le_bytes()); // bit-gravity: NorthWest
    out.extend_from_slice(&events.to_le_bytes());
    Some(())
}

/// A request that is its header and one window (Appendix B "MapWindow",
/// "UnmapWindow", "DestroyWindow").
fn window_request(out: &mut Vec<u8>, opcode: u8, window: u32) -> Option<()> {
    header(out, opcode, 0, 8)?;
    out.extend_from_slice(&window.to_le_bytes());
    Some(())
}

/// Appendix B "MapWindow".
pub fn map_window(out: &mut Vec<u8>, window: u32) -> Option<()> {
    window_request(out, opcode::MAP_WINDOW, window)
}

/// Appendix B "UnmapWindow".
pub fn unmap_window(out: &mut Vec<u8>, window: u32) -> Option<()> {
    window_request(out, opcode::UNMAP_WINDOW, window)
}

/// Appendix B "DestroyWindow".
pub fn destroy_window(out: &mut Vec<u8>, window: u32) -> Option<()> {
    window_request(out, opcode::DESTROY_WINDOW, window)
}

/// Appendix B "ConfigureWindow": move and resize `window` (value-mask x, y,
/// width, height).
pub fn configure_window(out: &mut Vec<u8>, window: u32, g: Geometry) -> Option<()> {
    header(out, opcode::CONFIGURE_WINDOW, 0, 12 + 16)?;
    out.extend_from_slice(&window.to_le_bytes());
    out.extend_from_slice(&0x000Fu16.to_le_bytes());
    out.extend_from_slice(&[0, 0]);
    // Each value is 4 bytes; x and y are INT16 in the low bytes.
    out.extend_from_slice(&i32::from(g.x).to_le_bytes());
    out.extend_from_slice(&i32::from(g.y).to_le_bytes());
    out.extend_from_slice(&u32::from(g.width).to_le_bytes());
    out.extend_from_slice(&u32::from(g.height).to_le_bytes());
    Some(())
}

/// Appendix B "InternAtom", `only-if-exists` false.
pub fn intern_atom(out: &mut Vec<u8>, name: &[u8]) -> Option<()> {
    header(
        out,
        opcode::INTERN_ATOM,
        0,
        8usize.checked_add(padded(name.len())?)?,
    )?;
    out.extend_from_slice(&u16::try_from(name.len()).ok()?.to_le_bytes());
    out.extend_from_slice(&[0, 0]);
    push_padded(out, name);
    Some(())
}

/// The atom of an `InternAtom` reply (Appendix B): bytes 8 to 11.
pub fn atom_of(reply: &[u8]) -> Option<u32> {
    u32_at(reply, 8).filter(|a| *a != 0)
}

/// Appendix B "ChangeProperty", mode `Replace`, format 8: `data` as bytes of
/// type `kind`.
pub fn change_property_bytes(
    out: &mut Vec<u8>,
    window: u32,
    property: u32,
    kind: u32,
    data: &[u8],
) -> Option<()> {
    header(
        out,
        opcode::CHANGE_PROPERTY,
        0,
        24usize.checked_add(padded(data.len())?)?,
    )?;
    out.extend_from_slice(&window.to_le_bytes());
    out.extend_from_slice(&property.to_le_bytes());
    out.extend_from_slice(&kind.to_le_bytes());
    out.extend_from_slice(&[8, 0, 0, 0]);
    out.extend_from_slice(&u32::try_from(data.len()).ok()?.to_le_bytes());
    push_padded(out, data);
    Some(())
}

/// Appendix B "ChangeProperty", mode `Replace`, format 32: `atoms` as a list of
/// type `ATOM`.
pub fn change_property_atoms(
    out: &mut Vec<u8>,
    window: u32,
    property: u32,
    atoms: &[u32],
) -> Option<()> {
    header(
        out,
        opcode::CHANGE_PROPERTY,
        0,
        24usize.checked_add(atoms.len().checked_mul(4)?)?,
    )?;
    out.extend_from_slice(&window.to_le_bytes());
    out.extend_from_slice(&property.to_le_bytes());
    out.extend_from_slice(&ATOM_ATOM.to_le_bytes());
    out.extend_from_slice(&[32, 0, 0, 0]);
    out.extend_from_slice(&u32::try_from(atoms.len()).ok()?.to_le_bytes());
    for a in atoms {
        out.extend_from_slice(&a.to_le_bytes());
    }
    Some(())
}

/// Appendix B "CreateGC" with no value: the defaults (function `Copy`, all
/// planes), which is what `PutImage` in `ZPixmap` format needs.
pub fn create_gc(out: &mut Vec<u8>, gc: u32, drawable: u32) -> Option<()> {
    header(out, opcode::CREATE_GC, 0, 16)?;
    out.extend_from_slice(&gc.to_le_bytes());
    out.extend_from_slice(&drawable.to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes());
    Some(())
}

/// Appendix B "GetKeyboardMapping" for `count` keycodes from `first`.
pub fn get_keyboard_mapping(out: &mut Vec<u8>, first: u8, count: u8) -> Option<()> {
    header(out, opcode::GET_KEYBOARD_MAPPING, 0, 8)?;
    out.extend_from_slice(&[first, count, 0, 0]);
    Some(())
}

/// The keysyms of every keycode from the server's `min-keycode`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Keymap {
    /// The first keycode.
    pub first: u8,
    /// Keysyms for each keycode.
    pub per_keycode: u8,
    /// `per_keycode` keysyms for each keycode in order; 0 is `NoSymbol`.
    pub keysyms: Vec<u32>,
}

/// Appendix B "GetKeyboardMapping", the reply: byte 1 is keysyms-per-keycode and
/// the keysyms follow the 32-byte header, 4 bytes each.
pub fn parse_keyboard_mapping(reply: &[u8], first: u8) -> Option<Keymap> {
    let per_keycode = *reply.get(1)?;
    let (chunks, _) = reply.get(32..)?.as_chunks::<4>();
    Some(Keymap {
        first,
        per_keycode,
        keysyms: chunks.iter().map(|c| u32::from_le_bytes(*c)).collect(),
    })
}

impl Keymap {
    /// The keysym in column `column` of `keycode` (0 if there is none).
    pub fn keysym(&self, keycode: u8, column: usize) -> u32 {
        let per = usize::from(self.per_keycode);
        if column >= per {
            return 0;
        }
        keycode
            .checked_sub(self.first)
            .and_then(|k| usize::from(k).checked_mul(per)?.checked_add(column))
            .and_then(|i| self.keysyms.get(i).copied())
            .unwrap_or(0)
    }
}

/// Appendix A "KEYSYM Encoding": the character a keysym types, if this client
/// translates it (see the module documentation).
pub fn keysym_char(keysym: u32) -> Option<char> {
    match keysym {
        0x20..=0x7E | 0xA0..=0xFF => char::from_u32(keysym),
        0x0100_0000..=0x0110_FFFF => char::from_u32(keysym.checked_sub(0x0100_0000)?),
        // KP_Multiply to KP_9: their ASCII characters at the same low byte.
        0xFFAA..=0xFFB9 => char::from_u32(keysym.checked_sub(0xFF80)?),
        _ => None,
    }
}

/// What a key press means: the key (the keycode's first keysym, which names it
/// whatever the modifiers) and the character it types under `state`, if any.
/// §5 "Keyboards" gives the Shift and Lock rule this follows.
pub fn key_symbols(map: &Keymap, keycode: u8, state: u16) -> (u32, Option<char>) {
    let plain = map.keysym(keycode, 0);
    let shifted = map.keysym(keycode, 1);
    let upper = |c: char| {
        let mut up = c.to_uppercase();
        match (up.next(), up.next()) {
            (Some(u), None) => u,
            _ => c,
        }
    };
    let typed = if state & SHIFT != 0 {
        if shifted != 0 {
            keysym_char(shifted)
        } else {
            keysym_char(plain).map(upper)
        }
    } else if state & LOCK != 0 {
        keysym_char(plain).map(upper)
    } else {
        keysym_char(plain)
    };
    (plain, typed)
}

/// A tile of an image: columns `x .. x + width` of rows `y .. y + height`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tile {
    /// Its first column.
    pub x: u32,
    /// Its first row.
    pub y: u32,
    /// Its width.
    pub width: u32,
    /// Its height.
    pub height: u32,
}

/// The bytes of a `PutImage` request before its pixels.
pub const PUT_IMAGE_HEADER: usize = 24;

/// Tiles covering a `width` by `height` image of 4 bytes a pixel, each small
/// enough that its `PutImage` request is at most `max_bytes` (which must leave
/// room for one pixel): as many whole rows as fit, or, when one row does not
/// fit, as many columns of one row as fit.
pub fn tiles(width: u32, height: u32, max_bytes: usize) -> Vec<Tile> {
    let room = max_bytes.saturating_sub(PUT_IMAGE_HEADER) / 4;
    let room = u32::try_from(room).unwrap_or(u32::MAX);
    // A tile's sides are 16 bits in the request.
    let side = u32::from(u16::MAX);
    let mut out = Vec::new();
    if width == 0 || height == 0 || room == 0 {
        return out;
    }
    let cols = width.min(room).min(side);
    let rows = room.checked_div(cols).unwrap_or(1).clamp(1, side);
    let mut y = 0u32;
    while y < height {
        let h = rows.min(height.saturating_sub(y));
        let mut x = 0u32;
        while x < width {
            let w = cols.min(width.saturating_sub(x));
            out.push(Tile {
                x,
                y,
                width: w,
                height: h,
            });
            x = x.saturating_add(w);
        }
        y = y.saturating_add(h);
    }
    out
}

/// Appendix B "PutImage", format `ZPixmap` (2), left-pad 0: the pixels of `tile`
/// out of an image `width` pixels wide whose rows are packed in `pixels`
/// (`0x00RRGGBB` each), drawn so that the image's top left is at `(dst_x, dst_y)`
/// of `drawable`. `None` if the tile lies outside the image or a number does not
/// fit its field.
pub fn put_image(
    out: &mut Vec<u8>,
    (drawable, gc, depth): (u32, u32, u8),
    pixels: &[u32],
    width: u32,
    tile: Tile,
    (dst_x, dst_y): (i16, i16),
) -> Option<()> {
    let w = usize::try_from(tile.width).ok()?;
    let h = usize::try_from(tile.height).ok()?;
    let data = w.checked_mul(h)?.checked_mul(4)?;
    header(
        out,
        opcode::PUT_IMAGE,
        2,
        PUT_IMAGE_HEADER.checked_add(data)?,
    )?;
    out.extend_from_slice(&drawable.to_le_bytes());
    out.extend_from_slice(&gc.to_le_bytes());
    out.extend_from_slice(&u16::try_from(tile.width).ok()?.to_le_bytes());
    out.extend_from_slice(&u16::try_from(tile.height).ok()?.to_le_bytes());
    let x = i32::from(dst_x).checked_add(i32::try_from(tile.x).ok()?)?;
    let y = i32::from(dst_y).checked_add(i32::try_from(tile.y).ok()?)?;
    out.extend_from_slice(&i16::try_from(x).ok()?.to_le_bytes());
    out.extend_from_slice(&i16::try_from(y).ok()?.to_le_bytes());
    out.extend_from_slice(&[0, depth, 0, 0]);
    let stride = usize::try_from(width).ok()?;
    let first_col = usize::try_from(tile.x).ok()?;
    let first_row = usize::try_from(tile.y).ok()?;
    for row in first_row..first_row.checked_add(h)? {
        let start = row.checked_mul(stride)?.checked_add(first_col)?;
        for p in pixels.get(start..start.checked_add(w)?)? {
            out.extend_from_slice(&p.to_le_bytes());
        }
    }
    Some(())
}

/// How long the message starting with `first32` is: 32 bytes, plus, for a reply
/// (byte 0 is 1) or a generic event (35), four times the length at bytes 4 to 7
/// (Appendix B, "Replies" and the generic event's encoding).
pub fn message_len(first32: &[u8]) -> Option<usize> {
    let code = *first32.first()? & 0x7F;
    if code == 1 || code == 35 {
        let extra = usize::try_from(u32_at(first32, 4)?).ok()?.checked_mul(4)?;
        32usize.checked_add(extra)
    } else {
        Some(32)
    }
}

/// What a 32-byte event means to the window (§11 and Appendix B "Events").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Raw {
    /// `KeyPress`: the keycode and the modifier state.
    Key {
        /// The keycode.
        keycode: u8,
        /// `SETofKEYBUTMASK`.
        state: u16,
    },
    /// `ButtonPress`: the button, and where in the event window.
    Button {
        /// 1 is the left button; 4 and 5 are the wheel, away and towards.
        button: u8,
        /// From the event window's left edge.
        x: i16,
        /// From its top edge.
        y: i16,
        /// The window the event was reported to.
        window: u32,
    },
    /// `Expose` on `window`; `last` when no more follow for it (count 0).
    Expose {
        /// The window.
        window: u32,
        /// Whether its count is 0.
        last: bool,
    },
    /// `ConfigureNotify`: `window` is now this size.
    Configure {
        /// The window.
        window: u32,
        /// Its width.
        width: u16,
        /// Its height.
        height: u16,
    },
    /// `DestroyNotify` for `window`.
    Destroyed {
        /// The window.
        window: u32,
    },
    /// `ClientMessage` of format 32 on `window`: its type and first datum.
    Client {
        /// The window.
        window: u32,
        /// The message's type.
        kind: u32,
        /// The first of its five 32-bit values.
        first: u32,
    },
    /// `MappingNotify` for the keyboard: the key map must be read again.
    KeyboardMapping,
    /// An error: its code and the sequence number of the failed request.
    Error {
        /// The error's code (Appendix B "Errors").
        code: u8,
        /// The low 16 bits of the request's sequence number.
        sequence: u16,
    },
}

/// What the 32 bytes of `event` mean; `None` for an event this client does not
/// act on, or fewer than 32 bytes. The top bit of byte 0 (sent by another client
/// with `SendEvent`) is ignored.
pub fn parse_event(event: &[u8]) -> Option<Raw> {
    if event.len() < 32 {
        return None;
    }
    match *event.first()? & 0x7F {
        0 => Some(Raw::Error {
            code: *event.get(1)?,
            sequence: u16_at(event, 2)?,
        }),
        2 => Some(Raw::Key {
            keycode: *event.get(1)?,
            state: u16_at(event, 28)?,
        }),
        4 => Some(Raw::Button {
            button: *event.get(1)?,
            window: u32_at(event, 12)?,
            x: i16_at(event, 24)?,
            y: i16_at(event, 26)?,
        }),
        12 => Some(Raw::Expose {
            window: u32_at(event, 4)?,
            last: u16_at(event, 16)? == 0,
        }),
        17 => Some(Raw::Destroyed {
            window: u32_at(event, 8)?,
        }),
        22 => Some(Raw::Configure {
            window: u32_at(event, 8)?,
            width: u16_at(event, 20)?,
            height: u16_at(event, 22)?,
        }),
        33 if *event.get(1)? == 32 => Some(Raw::Client {
            window: u32_at(event, 4)?,
            kind: u32_at(event, 8)?,
            first: u32_at(event, 12)?,
        }),
        // request: 1 is Keyboard (0 Modifier, 2 Pointer).
        34 if *event.get(4)? == 1 => Some(Raw::KeyboardMapping),
        _ => None,
    }
}

/// `title` as the bytes of a `STRING` property (ISO Latin-1, ICCCM §2.7.1): a
/// character outside Latin-1 becomes `?`. Cut at [`MAX_TITLE`] characters.
pub fn latin1(title: &str) -> Vec<u8> {
    title
        .chars()
        .take(MAX_TITLE)
        .map(|c| u8::try_from(u32::from(c)).unwrap_or(b'?'))
        .collect()
}

/// `title` as UTF-8 of at most [`MAX_TITLE`] bytes, cut between characters.
pub fn utf8(title: &str) -> &[u8] {
    let mut end = title.len().min(MAX_TITLE);
    while !title.is_char_boundary(end) {
        end = end.saturating_sub(1);
    }
    title.get(..end).unwrap_or("").as_bytes()
}

#[cfg(test)]
mod tests;
