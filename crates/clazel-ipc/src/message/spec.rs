//! Executable-style specification of the IPC message schema (phase-2.md item
//! 2.3). The schema is ours: this file is the definition.
//!
//! A message is a CBOR array (`crate::cbor`) whose first element is an
//! unsigned integer tag and whose other elements are the message's fields,
//! in order. Fields are text strings, byte strings, unsigned integers,
//! booleans, or (one field, `Display`'s links) an array of text strings.
//! Messages go between the kernel and a renderer, or (Phase 5 item 5.18)
//! between the kernel and the GPU process paired with a renderer.
//!
//! | Tag | Direction | Message | Fields |
//! |-----|-----------|---------|--------|
//! | 1 | renderer to kernel | `CookieGet` | |
//! | 2 | renderer to kernel | `CookieSet` | cookie string (text) |
//! | 3 | renderer to kernel | `StorageGetItem` | key (text) |
//! | 4 | renderer to kernel | `StorageSetItem` | key (text), value (text) |
//! | 5 | renderer to kernel | `StorageRemoveItem` | key (text) |
//! | 6 | renderer to kernel | `StorageClear` | |
//! | 7 | renderer to kernel | `StorageKey` | index (unsigned) |
//! | 8 | renderer to kernel | `StorageLength` | |
//! | 9 | renderer to kernel | `Navigate` | url (text) |
//! | 10 | renderer to kernel | `Display` | title (text), text (text), links (array of text) |
//! | 11 | renderer to kernel | `Title` | title (text) |
//! | 12 | renderer to kernel | `Submit` | url (text), method (text), content type (bytes), body (bytes) |
//! | 13 | renderer to kernel | `FetchSub` | request (unsigned), destination (unsigned: 0 style, 1 image), url (text) |
//! | 14 | renderer to kernel | `FetchStyle` | request (unsigned), url (text) |
//! | 15 | GPU process to kernel | `FrameReady` | buffer (unsigned), width (unsigned), height (unsigned) |
//! | 18 | GPU process to kernel | `GpuReady` | software (bool) |
//! | 19 | GPU process to kernel | `GpuRefused` | |
//! | 101 | kernel to renderer | `Commit` | url (text), content type (bytes), kind (unsigned) |
//! | 102 | kernel to renderer | `CookieValue` | cookie string (text) |
//! | 103 | kernel to renderer | `StorageValue` | present (bool), then value (text) only if present |
//! | 104 | kernel to renderer | `StorageLengthValue` | length (unsigned) |
//! | 105 | kernel to renderer | `Error` | code (unsigned) |
//! | 106 | kernel to renderer | `Body` | bytes (bytes, at most [`max_body_chunk`]) |
//! | 107 | kernel to renderer | `BodyEnd` | |
//! | 108 | kernel to renderer | `Viewport` | width (unsigned), height (unsigned), scale (unsigned) |
//! | 109 | kernel to renderer | `Input` | kind (unsigned), x (unsigned), y (unsigned), negative (bool), delta (unsigned), key (unsigned) |
//! | 110 | kernel to renderer | `StyleResponse` | request (unsigned), content type (bytes) |
//! | 111 | kernel to renderer | `StyleBody` | request (unsigned), bytes (bytes, at most [`max_style_chunk`]) |
//! | 112 | kernel to renderer | `StyleEnd` | request (unsigned) |
//! | 113 | kernel to renderer | `StyleFailed` | request (unsigned) |
//! | 115 | kernel to renderer | `SubResponse` | request (unsigned), content type (bytes) |
//! | 116 | kernel to renderer | `SubBody` | request (unsigned), bytes (bytes, at most [`max_sub_chunk`]) |
//! | 117 | kernel to renderer | `SubEnd` | request (unsigned) |
//! | 118 | kernel to renderer | `SubFailed` | request (unsigned) |
//! | 114 | kernel to GPU process | `GpuViewport` | width (unsigned), height (unsigned), scale (unsigned) |
//!
//! `StorageLengthValue` is not in the plan's list, which has no reply for
//! `StorageLength`; the schema needs one.
//!
//! Phase 4 (phase-4.md item 4.12) changed `Commit` and added `Body`,
//! `BodyEnd` and `Display`. A committed document is `Commit`, zero or more
//! `Body` frames and `BodyEnd`, and its body is the concatenation of the
//! `Body` frames' bytes, in order. `Commit`'s content type is the response's
//! combined `Content-Type` field value, or empty; its kind is 0 for a
//! document and 1 for a user script (the Phase 2 script path). `Display` is
//! the renderer's text rendering of its document: a title, the text, and
//! the absolute URLs of its links.
//!
//! Phase 5 (phase-5.md item 5.18, as decided under 5.0 on 2026-11-09) added
//! `Title`, `FrameReady`, `GpuReady`, `GpuRefused`, `Viewport`, `Input` and
//! `GpuViewport`, beside `Display`, which stays unchanged until item 5.26
//! deletes it (its tag, 10, is then never reused; no tag is ever reused).
//! `Title` is the committed document's title, which the kernel keeps and
//! labels each `Paint` with. `FrameReady` says the GPU process has drawn a
//! frame of `width` by `height` device pixels into the shared buffer
//! `buffer` of the ring the host allocated (the kernel sees the buffer's id,
//! never its pixels). `GpuReady` and `GpuRefused` are item 5.17c's (whether
//! the driver was accepted, and whether it is the software one); the schema
//! has them now so that their tags are fixed, and the kernel gives them no
//! meaning before 5.17c. `Viewport` and `GpuViewport` carry the size of the
//! tab's content area in device pixels and its scale (1 or 2, device pixels
//! per CSS pixel). `Input` is one event of the user's on the content area:
//! its kind (0 a click, 1 a scroll, 2 a key), its position, a scroll delta
//! as a sign and a magnitude (the profile has no negative integers), and a
//! key code.
//!
//! Phase 5 item 5.19 added the style sheet fetch: a committed renderer's
//! `FetchStyle` asks the kernel to fetch `url` (resolved against its
//! committed URL) under `request`, an id the renderer chose; the kernel
//! answers with `StyleResponse` (the response's combined `Content-Type`
//! field value, or empty), zero or more `StyleBody` and `StyleEnd`, or with
//! `StyleFailed`, each naming that `request`. The request id is the
//! renderer's own number for its fetch, not an identity: it names nobody.
//!
//! Phase 6 item 6.17 added the sub-resource fetch of decision 6.0(e) B:
//! `FetchSub { request, destination, url }` asks the kernel to fetch `url`
//! (resolved against the renderer's committed URL) as a "no-cors" request of
//! the given destination ([`destination_style`] 0, [`destination_image`] 1;
//! Phase 7 adds more), and the kernel answers with `SubResponse` (the
//! response's combined `Content-Type` field value, or empty), zero or more
//! `SubBody` and `SubEnd`, or with `SubFailed`, each naming that `request`,
//! as `FetchStyle`'s family does. A destination the kernel does not know is
//! answered with `SubFailed`; the schema does not narrow it. `FetchStyle`
//! and the `Style*` messages stay, unchanged, until the renderer sends
//! `FetchSub` for sheets (item 6.18), when their tags are never used again.
//! A response that Opaque Response Blocking refuses is `SubFailed` (a network
//! error), never an empty `SubResponse`.
//!
//! Phase 6 item 6.16 added `Submit`, a navigation with a method and a body
//! (a form submission, HTML §4.10.22.3 step 22 "navigate"), beside `Navigate`,
//! whose tag, 9, stays the `GET`-only form. `method` is `GET` or `POST`; for
//! `GET` the content type and the body are empty (a `GET` has no body), for
//! `POST` they are the body's `Content-Type` and octets (an empty body is
//! allowed). The schema does not narrow them (the kernel refuses the rest, as
//! it refuses a `Commit` kind it does not know). **The body's bound is the
//! frame's**, not the plan's proposed 16 MiB: a `Submit` is one frame, a frame
//! is at most [`crate::frame::spec::MAX_FRAME`] (1 MiB) octets, and
//! [`max_submit_body`] is the largest body that fits one with a URL, method and
//! content type of at most [`max_submit_head`] octets together
//! (`lemmas::lemma_submit_fits_frame`); a larger one is not sent
//! (`encode_framed` gives `None`). Raising the bound means chunking the body
//! over several frames or raising `MAX_FRAME`, which every receiver's memory
//! bound depends on; neither is done (listed in phase-6.md). A decoded
//! `Submit` is at most a frame, so `clazel-fetch`'s 16 MiB bound is never
//! the tighter one.
//!
//! Two rules are part of the schema's spec ([`message_fields`], and
//! `lemmas::lemma_no_identity_fields`):
//! - **No message carries a claimed identity.** No origin, renderer id, tab
//!   id or sender URL appears in any message. The kernel learns the sender
//!   from the socket. (`Navigate`'s `url` is the address to go to, not the
//!   sender's; `Display` names no tab, origin or URL of its own: its title
//!   and text are what the page says, and its links are where it points.)
//! - **Renderer ids never reach a renderer.** They are assigned in order, so
//!   showing one would let a renderer count another's spawns.
//!
//! Modelling choices:
//! - Text is the bytes of its UTF-8 encoding (`Seq<u8>`), as in a CBOR text
//!   string token; a message is well formed ([`message_ok`]) when its
//!   token sequence is one data item of the profile, i.e. text is valid
//!   UTF-8.
//! - An absent storage value is `present = false` with no value, because
//!   the profile has no null.
//! - `Commit`'s kind is any unsigned integer on the wire; 0 and 1 are the
//!   kinds the kernel sends, and a renderer refuses any other. (The schema
//!   does not narrow it, so that every message is still exactly its tokens.)
//! - `Display`'s links are a nested array: the message's array has four
//!   elements (the tag, the title, the text and the links), and its last
//!   element is an array of text strings, whose tokens follow it
//!   ([`display_tokens`]). It is the only nested field in the schema.
//! - `Input`'s fields are all present in every kind: a click has a zero
//!   delta and key, a scroll a zero key, a key a zero position and delta.
//!   One shape keeps the message exactly its tokens, as `Commit`'s kind
//!   does, and the schema does not narrow `kind`, `scale` or `key`: the
//!   receiver refuses a value it does not know.
//! - The scroll delta is `negative` and `delta`, since the profile has no
//!   major type 1 (`crate::cbor::spec`); `negative` with `delta` 0 is a
//!   second form of zero, which the receiver reads as zero.
//! - A message's direction is a predicate ([`is_from_renderer`],
//!   [`is_from_gpu`]); the kernel decodes a renderer's frames with
//!   [`decode_renderer_message`] and a GPU process's with
//!   [`decode_gpu_message`], so each process can send only its own kind.
//!   `GpuViewport` is the only kernel-to-GPU message.
//! - "Failure" is `None`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The CBOR profile's token, as this schema uses it.
pub type Token = crate::cbor::spec::Token;

/// [`crate::cbor::spec::decode`].
pub open spec fn decode(b: Seq<u8>) -> Option<Seq<Token>> {
    crate::cbor::spec::decode(b)
}

/// [`crate::cbor::spec::encode`].
pub open spec fn encode(t: Seq<Token>) -> Seq<u8> {
    crate::cbor::spec::encode(t)
}

/// [`crate::cbor::spec::is_item`].
pub open spec fn is_item(t: Seq<Token>) -> bool {
    crate::cbor::spec::is_item(t)
}

/// A message, in either direction.
pub enum Message {
    /// Renderer to kernel: read `document.cookie`.
    CookieGet,
    /// Renderer to kernel: write `document.cookie`.
    CookieSet {
        /// The cookie string.
        cookie_string: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.getItem(key)`.
    StorageGetItem {
        /// The key.
        key: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.setItem(key, value)`.
    StorageSetItem {
        /// The key.
        key: Seq<u8>,
        /// The value.
        value: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.removeItem(key)`.
    StorageRemoveItem {
        /// The key.
        key: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.clear()`.
    StorageClear,
    /// Renderer to kernel: `localStorage.key(index)`.
    StorageKey {
        /// The index.
        index: u64,
    },
    /// Renderer to kernel: `localStorage.length`.
    StorageLength,
    /// Renderer to kernel: navigate to a URL.
    Navigate {
        /// The URL to go to (not the sender's).
        url: Seq<u8>,
    },
    /// Renderer to kernel (item 6.16): navigate with a method and a body.
    Submit {
        /// The URL to go to (not the sender's).
        url: Seq<u8>,
        /// The method: `GET` or `POST`.
        method: Seq<u8>,
        /// The body's `Content-Type` field value (empty for `GET`).
        content_type: Seq<u8>,
        /// The body's octets (empty for `GET`).
        body: Seq<u8>,
    },
    /// Renderer to kernel: show this text rendering of the committed
    /// document (phase-4.md item 4.12).
    Display {
        /// The document's title.
        title: Seq<u8>,
        /// The document's text, laid out.
        text: Seq<u8>,
        /// The absolute URLs of its links, in order.
        links: Seq<Seq<u8>>,
    },
    /// Renderer to kernel: the committed document's title (item 5.18).
    Title {
        /// The title.
        title: Seq<u8>,
    },
    /// GPU process to kernel: a frame is drawn into a buffer of the ring.
    FrameReady {
        /// The buffer's id in the ring the host allocated.
        buffer: u64,
        /// The frame's width, in device pixels.
        width: u64,
        /// The frame's height, in device pixels.
        height: u64,
    },
    /// GPU process to kernel: the driver is accepted (item 5.17c).
    GpuReady {
        /// Whether it is the software driver.
        software: bool,
    },
    /// GPU process to kernel: the driver is refused (item 5.17c).
    GpuRefused,
    /// Renderer to kernel: fetch a style sheet (item 5.19).
    FetchStyle {
        /// The renderer's id for this fetch.
        request: u64,
        /// The sheet's URL, as the document wrote it.
        url: Seq<u8>,
    },
    /// Kernel to renderer: the sheet's response arrived (item 5.19).
    StyleResponse {
        /// The renderer's id for the fetch.
        request: u64,
        /// The response's combined `Content-Type` field value, or empty.
        content_type: Seq<u8>,
    },
    /// Kernel to renderer: the next part of the sheet's body.
    StyleBody {
        /// The renderer's id for the fetch.
        request: u64,
        /// The octets.
        bytes: Seq<u8>,
    },
    /// Kernel to renderer: the sheet's body is complete.
    StyleEnd {
        /// The renderer's id for the fetch.
        request: u64,
    },
    /// Kernel to renderer: the fetch failed (or was refused).
    StyleFailed {
        /// The renderer's id for the fetch.
        request: u64,
    },
    /// Renderer to kernel: fetch a sub-resource of a destination (item 6.17).
    FetchSub {
        /// The renderer's id for this fetch.
        request: u64,
        /// The request's destination: [`destination_style`] or
        /// [`destination_image`].
        destination: u64,
        /// The resource's URL, as the document wrote it.
        url: Seq<u8>,
    },
    /// Kernel to renderer: the sub-resource's response arrived (item 6.17).
    SubResponse {
        /// The renderer's id for the fetch.
        request: u64,
        /// The response's combined `Content-Type` field value, or empty.
        content_type: Seq<u8>,
    },
    /// Kernel to renderer: the next part of the sub-resource's body.
    SubBody {
        /// The renderer's id for the fetch.
        request: u64,
        /// The octets.
        bytes: Seq<u8>,
    },
    /// Kernel to renderer: the sub-resource's body is complete.
    SubEnd {
        /// The renderer's id for the fetch.
        request: u64,
    },
    /// Kernel to renderer: the fetch failed, was refused, or was blocked.
    SubFailed {
        /// The renderer's id for the fetch.
        request: u64,
    },
    /// Kernel to renderer: a document is committed; its body follows in
    /// `Body` frames, then `BodyEnd`.
    Commit {
        /// The committed URL.
        url: Seq<u8>,
        /// The response's combined `Content-Type` field value, or empty.
        content_type: Seq<u8>,
        /// 0 a document, 1 a user script.
        kind: u64,
    },
    /// Kernel to renderer: the value of `document.cookie`.
    CookieValue {
        /// The cookie string.
        cookie_string: Seq<u8>,
    },
    /// Kernel to renderer: a storage value, if there is one.
    StorageValue {
        /// The value, or `None` if there is none.
        value: Option<Seq<u8>>,
    },
    /// Kernel to renderer: `localStorage.length`.
    StorageLengthValue {
        /// The length.
        length: u64,
    },
    /// Kernel to renderer: a request failed.
    Error {
        /// The error code.
        code: u64,
    },
    /// Kernel to renderer: the next part of the committed document's body.
    Body {
        /// The octets.
        bytes: Seq<u8>,
    },
    /// Kernel to renderer: the committed document's body is complete.
    BodyEnd,
    /// Kernel to renderer: the tab's content area.
    Viewport {
        /// Its width, in device pixels.
        width: u64,
        /// Its height, in device pixels.
        height: u64,
        /// Device pixels per CSS pixel (1 or 2).
        scale: u64,
    },
    /// Kernel to renderer: one event of the user's on the content area.
    Input {
        /// 0 a click, 1 a scroll, 2 a key.
        kind: u64,
        /// The position's x, in device pixels from the content area's left.
        x: u64,
        /// The position's y, in device pixels from the content area's top.
        y: u64,
        /// Whether the scroll delta is negative (up or left).
        negative: bool,
        /// The scroll delta's magnitude, in device pixels.
        delta: u64,
        /// The key's code.
        key: u64,
    },
    /// Kernel to GPU process: the tab's content area.
    GpuViewport {
        /// Its width, in device pixels.
        width: u64,
        /// Its height, in device pixels.
        height: u64,
        /// Device pixels per CSS pixel (1 or 2).
        scale: u64,
    },
}

/// The most octets one `Body` carries: `MAX_FRAME` minus the rest of its
/// payload, which is the array's head (1 octet), the tag 106 (2 octets) and
/// the byte string's head (at most 5 octets below 2^32), so that every `Body`
/// of at most this many octets fits one frame
/// (`lemmas::lemma_body_fits_frame`).
pub open spec fn max_body_chunk() -> nat {
    (crate::frame::spec::MAX_FRAME - 8) as nat
}

/// The most octets a `Submit`'s URL, method and content type may have
/// together, for [`max_submit_body`] to hold (item 6.16).
pub open spec fn max_submit_head() -> nat {
    8192
}

/// The most octets a `Submit`'s body may have so that, with a URL, method and
/// content type of at most [`max_submit_head`] octets together, the message
/// fits one frame: `MAX_FRAME` minus that head, the array's head (1 octet),
/// the tag (2 octets) and the four fields' heads (at most 5 octets each below
/// 2^32), with room to spare (`lemmas::lemma_submit_fits_frame`).
pub open spec fn max_submit_body() -> nat {
    (crate::frame::spec::MAX_FRAME - 8192 - 64) as nat
}

/// The most octets one `StyleBody` carries: `MAX_FRAME` minus the rest of
/// its payload, which is the array's head (1 octet), the tag 111 (2
/// octets), the request id (at most 9 octets) and the byte string's head
/// (at most 5 octets below 2^32), so that every `StyleBody` of at most this
/// many octets fits one frame (item 5.19).
pub open spec fn max_style_chunk() -> nat {
    (crate::frame::spec::MAX_FRAME - 17) as nat
}

/// The most octets one `SubBody` carries: as [`max_style_chunk`] (the tag 116
/// is two octets like 111), so that every `SubBody` of at most this many
/// octets fits one frame (item 6.17).
pub open spec fn max_sub_chunk() -> nat {
    (crate::frame::spec::MAX_FRAME - 17) as nat
}

/// `FetchSub`'s destination "style".
pub open spec fn destination_style() -> u64 {
    0
}

/// `FetchSub`'s destination "image".
pub open spec fn destination_image() -> u64 {
    1
}

/// Whether `m` is sent by a renderer to the kernel.
pub open spec fn is_from_renderer(m: Message) -> bool {
    match m {
        Message::FetchSub { .. }
        | Message::CookieGet
        | Message::CookieSet { .. }
        | Message::StorageGetItem { .. }
        | Message::StorageSetItem { .. }
        | Message::StorageRemoveItem { .. }
        | Message::StorageClear
        | Message::StorageKey { .. }
        | Message::StorageLength
        | Message::Navigate { .. }
        | Message::Submit { .. }
        | Message::Display { .. }
        | Message::Title { .. }
        | Message::FetchStyle { .. } => true,
        _ => false,
    }
}

/// Whether `m` is sent by a GPU process to the kernel (item 5.18).
pub open spec fn is_from_gpu(m: Message) -> bool {
    match m {
        Message::FrameReady { .. } | Message::GpuReady { .. } | Message::GpuRefused => true,
        _ => false,
    }
}

/// The kind of each field of a message.
pub enum Field {
    /// A cookie string.
    CookieString,
    /// A storage key.
    Key,
    /// A storage value.
    Value,
    /// A URL to navigate to or commit.
    Url,
    /// A request method.
    Method,
    /// A storage index.
    Index,
    /// Whether a storage value is present.
    Present,
    /// A storage length.
    Length,
    /// An error code.
    Code,
    /// A document's content type.
    ContentType,
    /// A document's kind (a document or a user script).
    Kind,
    /// Some octets of a document's body.
    BodyBytes,
    /// A document's title.
    Title,
    /// A document's text.
    Text,
    /// The URLs a document links to.
    Links,
    /// A buffer's id in the ring the host allocated.
    Buffer,
    /// A width in device pixels.
    Width,
    /// A height in device pixels.
    Height,
    /// Device pixels per CSS pixel.
    Scale,
    /// Whether the GPU driver is the software one.
    Software,
    /// The kind of a user's input event.
    InputKind,
    /// An x position in device pixels.
    X,
    /// A y position in device pixels.
    Y,
    /// Whether a scroll delta is negative.
    Negative,
    /// A scroll delta's magnitude.
    Delta,
    /// A key code.
    KeyCode,
    /// The renderer's own id for a style sheet fetch (item 5.19).
    Request,
    /// A sub-resource fetch's destination (item 6.17).
    Destination,
    /// A claimed origin. No message has one.
    Origin,
    /// A renderer id. No message has one.
    RendererId,
    /// A tab id. No message has one.
    TabId,
    /// The URL of the sender. No message has one.
    SenderUrl,
}

/// The fields a message carries, in order. The two schema rules say none of
/// them is an identity ([`is_identity`]).
pub open spec fn message_fields(m: Message) -> Seq<Field> {
    match m {
        Message::CookieGet => seq![],
        Message::CookieSet { .. } => seq![Field::CookieString],
        Message::StorageGetItem { .. } => seq![Field::Key],
        Message::StorageSetItem { .. } => seq![Field::Key, Field::Value],
        Message::StorageRemoveItem { .. } => seq![Field::Key],
        Message::StorageClear => seq![],
        Message::StorageKey { .. } => seq![Field::Index],
        Message::StorageLength => seq![],
        Message::Navigate { .. } => seq![Field::Url],
        Message::Submit { .. } => seq![Field::Url, Field::Method, Field::ContentType, Field::BodyBytes],
        Message::Display { .. } => seq![Field::Title, Field::Text, Field::Links],
        Message::Commit { .. } => seq![Field::Url, Field::ContentType, Field::Kind],
        Message::CookieValue { .. } => seq![Field::CookieString],
        Message::StorageValue { value } => match value {
            None => seq![Field::Present],
            Some(_) => seq![Field::Present, Field::Value],
        },
        Message::StorageLengthValue { .. } => seq![Field::Length],
        Message::Error { .. } => seq![Field::Code],
        Message::Body { .. } => seq![Field::BodyBytes],
        Message::BodyEnd => seq![],
        Message::Title { .. } => seq![Field::Title],
        Message::FrameReady { .. } => seq![Field::Buffer, Field::Width, Field::Height],
        Message::GpuReady { .. } => seq![Field::Software],
        Message::GpuRefused => seq![],
        Message::Viewport { .. } => seq![Field::Width, Field::Height, Field::Scale],
        Message::Input { .. } => seq![Field::InputKind, Field::X, Field::Y, Field::Negative, Field::Delta, Field::KeyCode],
        Message::GpuViewport { .. } => seq![Field::Width, Field::Height, Field::Scale],
        Message::FetchStyle { .. } => seq![Field::Request, Field::Url],
        Message::StyleResponse { .. } => seq![Field::Request, Field::ContentType],
        Message::StyleBody { .. } => seq![Field::Request, Field::BodyBytes],
        Message::StyleEnd { .. } => seq![Field::Request],
        Message::StyleFailed { .. } => seq![Field::Request],
        Message::FetchSub { .. } => seq![Field::Request, Field::Destination, Field::Url],
        Message::SubResponse { .. } => seq![Field::Request, Field::ContentType],
        Message::SubBody { .. } => seq![Field::Request, Field::BodyBytes],
        Message::SubEnd { .. } => seq![Field::Request],
        Message::SubFailed { .. } => seq![Field::Request],
    }
}

/// The number of tokens of a message beyond one per field: the elements of
/// `Display`'s links, which follow the links' array token.
pub open spec fn nested_len(m: Message) -> nat {
    match m {
        Message::Display { links, .. } => links.len(),
        _ => 0,
    }
}

/// A field that names who is speaking or which renderer: forbidden.
pub open spec fn is_identity(f: Field) -> bool {
    match f {
        Field::Origin | Field::RendererId | Field::TabId | Field::SenderUrl => true,
        _ => false,
    }
}

/// The tokens of a list of text strings, in order.
pub open spec fn text_tokens(ls: Seq<Seq<u8>>) -> Seq<Token> {
    ls.map_values(|l: Seq<u8>| Token::Text(l))
}

/// The tokens of `Display`: the array of the tag, the title, the text and
/// the links, the links being an array whose text strings follow it.
pub open spec fn display_tokens(title: Seq<u8>, text: Seq<u8>, links: Seq<Seq<u8>>) -> Seq<Token> {
    seq![Token::Array(4), Token::Uint(10), Token::Text(title), Token::Text(text), Token::Array(links.len() as u64)] + text_tokens(links)
}

/// The tokens of a message: an array of the tag and the fields.
pub open spec fn message_tokens(m: Message) -> Seq<Token> {
    match m {
        Message::CookieGet => seq![Token::Array(1), Token::Uint(1)],
        Message::CookieSet { cookie_string } => seq![Token::Array(2), Token::Uint(2), Token::Text(cookie_string)],
        Message::StorageGetItem { key } => seq![Token::Array(2), Token::Uint(3), Token::Text(key)],
        Message::StorageSetItem { key, value } => seq![Token::Array(3), Token::Uint(4), Token::Text(key), Token::Text(value)],
        Message::StorageRemoveItem { key } => seq![Token::Array(2), Token::Uint(5), Token::Text(key)],
        Message::StorageClear => seq![Token::Array(1), Token::Uint(6)],
        Message::StorageKey { index } => seq![Token::Array(2), Token::Uint(7), Token::Uint(index)],
        Message::StorageLength => seq![Token::Array(1), Token::Uint(8)],
        Message::Navigate { url } => seq![Token::Array(2), Token::Uint(9), Token::Text(url)],
        Message::Submit { url, method, content_type, body } => seq![Token::Array(5), Token::Uint(12), Token::Text(url), Token::Text(method), Token::Bytes(content_type), Token::Bytes(body)],
        Message::Display { title, text, links } => display_tokens(title, text, links),
        Message::Commit { url, content_type, kind } => seq![Token::Array(4), Token::Uint(101), Token::Text(url), Token::Bytes(content_type), Token::Uint(kind)],
        Message::CookieValue { cookie_string } => seq![Token::Array(2), Token::Uint(102), Token::Text(cookie_string)],
        Message::StorageValue { value } => match value {
            None => seq![Token::Array(2), Token::Uint(103), Token::Bool(false)],
            Some(v) => seq![Token::Array(3), Token::Uint(103), Token::Bool(true), Token::Text(v)],
        },
        Message::StorageLengthValue { length } => seq![Token::Array(2), Token::Uint(104), Token::Uint(length)],
        Message::Error { code } => seq![Token::Array(2), Token::Uint(105), Token::Uint(code)],
        Message::Body { bytes } => seq![Token::Array(2), Token::Uint(106), Token::Bytes(bytes)],
        Message::BodyEnd => seq![Token::Array(1), Token::Uint(107)],
        Message::Title { title } => seq![Token::Array(2), Token::Uint(11), Token::Text(title)],
        Message::FrameReady { buffer, width, height } => seq![Token::Array(4), Token::Uint(15), Token::Uint(buffer), Token::Uint(width), Token::Uint(height)],
        Message::GpuReady { software } => seq![Token::Array(2), Token::Uint(18), Token::Bool(software)],
        Message::GpuRefused => seq![Token::Array(1), Token::Uint(19)],
        Message::Viewport { width, height, scale } => seq![Token::Array(4), Token::Uint(108), Token::Uint(width), Token::Uint(height), Token::Uint(scale)],
        Message::Input { kind, x, y, negative, delta, key } => seq![
            Token::Array(7),
            Token::Uint(109),
            Token::Uint(kind),
            Token::Uint(x),
            Token::Uint(y),
            Token::Bool(negative),
            Token::Uint(delta),
            Token::Uint(key),
        ],
        Message::GpuViewport { width, height, scale } => seq![Token::Array(4), Token::Uint(114), Token::Uint(width), Token::Uint(height), Token::Uint(scale)],
        Message::FetchStyle { request, url } => seq![Token::Array(3), Token::Uint(14), Token::Uint(request), Token::Text(url)],
        Message::StyleResponse { request, content_type } => seq![Token::Array(3), Token::Uint(110), Token::Uint(request), Token::Bytes(content_type)],
        Message::StyleBody { request, bytes } => seq![Token::Array(3), Token::Uint(111), Token::Uint(request), Token::Bytes(bytes)],
        Message::StyleEnd { request } => seq![Token::Array(2), Token::Uint(112), Token::Uint(request)],
        Message::StyleFailed { request } => seq![Token::Array(2), Token::Uint(113), Token::Uint(request)],
        Message::FetchSub { request, destination, url } => seq![Token::Array(4), Token::Uint(13), Token::Uint(request), Token::Uint(destination), Token::Text(url)],
        Message::SubResponse { request, content_type } => seq![Token::Array(3), Token::Uint(115), Token::Uint(request), Token::Bytes(content_type)],
        Message::SubBody { request, bytes } => seq![Token::Array(3), Token::Uint(116), Token::Uint(request), Token::Bytes(bytes)],
        Message::SubEnd { request } => seq![Token::Array(2), Token::Uint(117), Token::Uint(request)],
        Message::SubFailed { request } => seq![Token::Array(2), Token::Uint(118), Token::Uint(request)],
    }
}

/// Whether `m` can be sent: its tokens are one data item of the profile.
pub open spec fn message_ok(m: Message) -> bool {
    is_item(message_tokens(m))
}

/// The message with this `tag` and these field tokens.
pub open spec fn parse_fields(tag: u64, f: Seq<Token>) -> Option<Message> {
    if tag == 1 {
        if f.len() == 0 { Some(Message::CookieGet) } else { None }
    } else if tag == 2 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::CookieSet { cookie_string: s }), _ => None } } else { None }
    } else if tag == 3 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::StorageGetItem { key: s }), _ => None } } else { None }
    } else if tag == 4 {
        if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Text(k), Token::Text(v)) => Some(Message::StorageSetItem { key: k, value: v }),
                _ => None,
            }
        } else { None }
    } else if tag == 5 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::StorageRemoveItem { key: s }), _ => None } } else { None }
    } else if tag == 6 {
        if f.len() == 0 { Some(Message::StorageClear) } else { None }
    } else if tag == 7 {
        if f.len() == 1 { match f[0] { Token::Uint(i) => Some(Message::StorageKey { index: i }), _ => None } } else { None }
    } else if tag == 8 {
        if f.len() == 0 { Some(Message::StorageLength) } else { None }
    } else if tag == 9 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::Navigate { url: s }), _ => None } } else { None }
    } else if tag == 12 {
        if f.len() == 4 {
            match (f[0], f[1], f[2], f[3]) {
                (Token::Text(u), Token::Text(m), Token::Bytes(c), Token::Bytes(b)) => Some(Message::Submit { url: u, method: m, content_type: c, body: b }),
                _ => None,
            }
        } else { None }
    } else if tag == 11 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::Title { title: s }), _ => None } } else { None }
    } else if tag == 14 {
        if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Uint(r), Token::Text(u)) => Some(Message::FetchStyle { request: r, url: u }),
                _ => None,
            }
        } else { None }
    } else if tag == 15 {
        if f.len() == 3 {
            match (f[0], f[1], f[2]) {
                (Token::Uint(b), Token::Uint(w), Token::Uint(h)) => Some(Message::FrameReady { buffer: b, width: w, height: h }),
                _ => None,
            }
        } else { None }
    } else if tag == 18 {
        if f.len() == 1 { match f[0] { Token::Bool(b) => Some(Message::GpuReady { software: b }), _ => None } } else { None }
    } else if tag == 19 {
        if f.len() == 0 { Some(Message::GpuRefused) } else { None }
    } else if tag == 101 {
        if f.len() == 3 {
            match (f[0], f[1], f[2]) {
                (Token::Text(u), Token::Bytes(c), Token::Uint(k)) => Some(Message::Commit { url: u, content_type: c, kind: k }),
                _ => None,
            }
        } else { None }
    } else if tag == 102 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::CookieValue { cookie_string: s }), _ => None } } else { None }
    } else if tag == 103 {
        if f.len() == 1 {
            match f[0] { Token::Bool(false) => Some(Message::StorageValue { value: None }), _ => None }
        } else if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Bool(true), Token::Text(v)) => Some(Message::StorageValue { value: Some(v) }),
                _ => None,
            }
        } else { None }
    } else if tag == 104 {
        if f.len() == 1 { match f[0] { Token::Uint(n) => Some(Message::StorageLengthValue { length: n }), _ => None } } else { None }
    } else if tag == 105 {
        if f.len() == 1 { match f[0] { Token::Uint(n) => Some(Message::Error { code: n }), _ => None } } else { None }
    } else if tag == 106 {
        if f.len() == 1 { match f[0] { Token::Bytes(b) => Some(Message::Body { bytes: b }), _ => None } } else { None }
    } else if tag == 107 {
        if f.len() == 0 { Some(Message::BodyEnd) } else { None }
    } else if tag == 108 {
        if f.len() == 3 {
            match (f[0], f[1], f[2]) {
                (Token::Uint(w), Token::Uint(h), Token::Uint(sc)) => Some(Message::Viewport { width: w, height: h, scale: sc }),
                _ => None,
            }
        } else { None }
    } else if tag == 109 {
        if f.len() == 6 {
            match (f[0], f[1], f[2], f[3], f[4], f[5]) {
                (Token::Uint(k), Token::Uint(x), Token::Uint(y), Token::Bool(n), Token::Uint(d), Token::Uint(key)) => Some(
                    Message::Input { kind: k, x, y, negative: n, delta: d, key },
                ),
                _ => None,
            }
        } else { None }
    } else if tag == 110 {
        if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Uint(r), Token::Bytes(c)) => Some(Message::StyleResponse { request: r, content_type: c }),
                _ => None,
            }
        } else { None }
    } else if tag == 111 {
        if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Uint(r), Token::Bytes(b)) => Some(Message::StyleBody { request: r, bytes: b }),
                _ => None,
            }
        } else { None }
    } else if tag == 112 {
        if f.len() == 1 { match f[0] { Token::Uint(r) => Some(Message::StyleEnd { request: r }), _ => None } } else { None }
    } else if tag == 113 {
        if f.len() == 1 { match f[0] { Token::Uint(r) => Some(Message::StyleFailed { request: r }), _ => None } } else { None }
    } else if tag == 13 {
        if f.len() == 3 {
            match (f[0], f[1], f[2]) {
                (Token::Uint(r), Token::Uint(d), Token::Text(u)) => Some(Message::FetchSub { request: r, destination: d, url: u }),
                _ => None,
            }
        } else { None }
    } else if tag == 115 {
        if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Uint(r), Token::Bytes(c)) => Some(Message::SubResponse { request: r, content_type: c }),
                _ => None,
            }
        } else { None }
    } else if tag == 116 {
        if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Uint(r), Token::Bytes(b)) => Some(Message::SubBody { request: r, bytes: b }),
                _ => None,
            }
        } else { None }
    } else if tag == 117 {
        if f.len() == 1 { match f[0] { Token::Uint(r) => Some(Message::SubEnd { request: r }), _ => None } } else { None }
    } else if tag == 118 {
        if f.len() == 1 { match f[0] { Token::Uint(r) => Some(Message::SubFailed { request: r }), _ => None } } else { None }
    } else if tag == 114 {
        if f.len() == 3 {
            match (f[0], f[1], f[2]) {
                (Token::Uint(w), Token::Uint(h), Token::Uint(sc)) => Some(Message::GpuViewport { width: w, height: h, scale: sc }),
                _ => None,
            }
        } else { None }
    } else {
        None
    }
}

/// Every token of `ts` is a text string (by recursion, so that Verus can
/// evaluate it on a concrete message).
pub open spec fn all_text(ts: Seq<Token>) -> bool
    decreases ts.len(),
{
    ts.len() == 0 || (ts[0] is Text && all_text(ts.drop_first()))
}

/// The text strings of tokens that are all text strings.
pub open spec fn texts_of(ts: Seq<Token>) -> Seq<Seq<u8>> {
    ts.map_values(|t: Token| t->Text_0)
}

/// `Display` from the element count `n` of its array and the tokens after
/// the tag: four elements, two text strings, then an array of `k` text
/// strings that are the last `k` tokens.
pub open spec fn parse_display(n: u64, f: Seq<Token>) -> Option<Message> {
    if n == 4 && f.len() >= 3 {
        match (f[0], f[1], f[2]) {
            (Token::Text(title), Token::Text(text), Token::Array(k)) => {
                let rest = f.subrange(3, f.len() as int);
                if k as nat == rest.len() && all_text(rest) {
                    Some(Message::Display { title, text, links: texts_of(rest) })
                } else {
                    None
                }
            },
            _ => None,
        }
    } else {
        None
    }
}

/// The message in a token sequence: an array whose first element is the
/// tag, and which has exactly the message's fields after it (for `Display`,
/// whose last field is an array, [`parse_display`]).
pub open spec fn parse_message(t: Seq<Token>) -> Option<Message> {
    if t.len() < 2 {
        None
    } else {
        match (t[0], t[1]) {
            (Token::Array(n), Token::Uint(tag)) => {
                if tag == 10 {
                    parse_display(n, t.subrange(2, t.len() as int))
                } else if n as nat + 1 == t.len() {
                    parse_fields(tag, t.subrange(2, t.len() as int))
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

/// Decode one message, in either direction, from the bytes of a CBOR item.
pub open spec fn decode_message(b: Seq<u8>) -> Option<Message> {
    match decode(b) {
        Some(t) => parse_message(t),
        None => None,
    }
}

/// Decode a message the kernel receives: only renderer-to-kernel messages.
pub open spec fn decode_renderer_message(b: Seq<u8>) -> Option<Message> {
    match decode_message(b) {
        Some(m) => if is_from_renderer(m) { Some(m) } else { None },
        None => None,
    }
}

/// Decode a message the kernel receives from a GPU process: only
/// GPU-process-to-kernel messages (item 5.18).
pub open spec fn decode_gpu_message(b: Seq<u8>) -> Option<Message> {
    match decode_message(b) {
        Some(m) => if is_from_gpu(m) { Some(m) } else { None },
        None => None,
    }
}

/// The bytes of a message.
pub open spec fn encode_message(m: Message) -> Seq<u8> {
    encode(message_tokens(m))
}

/// Decode a message from a whole frame: split the frame, then decode.
pub open spec fn decode_framed(frame: Seq<u8>) -> Option<Message> {
    match crate::frame::spec::decode_frame(frame) {
        Some(p) => decode_message(p),
        None => None,
    }
}

} // verus!
