//! The renderer's document pipeline (phase-4.md item 4.13): a committed
//! document's URL, content type and body to what it displays.
//!
//! Tier 0 glue, tested and not proven: every step that reads the page's
//! bytes is a function of another crate, called at that crate's own tier,
//! in the order the plan gives:
//!
//! 1. the content type: `clazel-mime`'s MIME type parser (MIME Sniffing
//!    §4.4 "parse a MIME type" from bytes), then its MIME type sniffing
//!    algorithm (§7, "determining the computed MIME type of a resource")
//!    with the parsed type as the supplied MIME type;
//! 2. for an HTML MIME type: HTML §13.2.3.2 the encoding sniffing algorithm
//!    (`clazel-html` `sniff::exec::sniff`, with the transport layer's
//!    encoding from the `charset` parameter), Encoding §6 "decode"
//!    (`clazel-encoding` `hooks::decode::decode`), and the parser
//!    (`clazel-treebuilder` `exec::driver::parse_real`: §13.2.3.5
//!    preprocessing, the tokenizer and the tree builder);
//! 3. the parser's actions: on the first `ChangeEncoding`, §13.2.3.4
//!    "change the encoding" (`sniff::exec::change_the_encoding`) and, if it
//!    gives an encoding, decode and parse again from the start with
//!    confidence *certain*, which the tree builder never changes again, so
//!    the parser runs at most twice; `StopParsing` keeps the document built
//!    so far (the parser has stopped either way); `ScriptReady` is ignored
//!    (scripting is Phase 7);
//! 4. HTML "document base URL" (§2.4.1): the frozen base URL of the first
//!    HTML `base` element with an `href` attribute in tree order, else the
//!    document's URL; each `<a href>` and `<iframe src>` is parsed against
//!    it with `clazel-url`'s basic URL parser, and a value that fails is
//!    not a link;
//! 5. the text layout (`clazel-text`, tier 0).
//!
//! A `text/plain` document is decoded with the same sniff and shown as one
//! preformatted block. Any other computed type shows the notice
//! "`<type>` is not shown" with the URL.
//!
//! # Modelling choices (ours, each listed)
//!
//! - **The resource header** handed to the MIME type sniffing algorithm is
//!   the first 1445 bytes of the body (MIME Sniffing §5.2's suggested
//!   amount); the whole body is always there.
//! - **The supplied MIME type** is the commit's content type (the
//!   response's combined `Content-Type` value) parsed as one MIME type.
//!   Fetch's "extract a MIME type", which splits a combined value at
//!   commas, is not implemented: a value with several types does not parse
//!   and is sniffed as an unknown type. The no-sniff flag is unset (the
//!   commit does not carry `X-Content-Type-Options`); the check-for-apache-
//!   bug flag is MIME Sniffing §5.1's test on the supplied value; no image,
//!   audio or video type is "supported".
//! - **Parsing a URL** uses UTF-8 for the query whatever the document's
//!   encoding (HTML's "encoding-parse a URL" would use the document's).
//! - **"Extracting a character encoding from a meta element"** is
//!   `clazel-html`'s byte version applied to the `content` value with every
//!   code point above U+007F mapped to the byte 0xFF, and its result mapped
//!   back byte for byte. The algorithm only looks for ASCII, and every
//!   encoding label is ASCII, so "get an encoding" of the result fails for
//!   the original value exactly when it fails for the mapped one, which is
//!   all the tree builder asks of it.
//! - **An encoding without a decoder** here (the multi-byte encodings,
//!   item 4.4) is not rendered: the page shows "encoding `<name>` is not
//!   supported" and no links (phase-4.md item 4.0(b)).
//! - **A document at the node limit** (`clazel_dom::exec::MAX_NODES`) shows
//!   what was built, with a notice that it was cut there.
//! - **The display limit:** a `Display` must fit one frame
//!   (`MAX_FRAME`, 1 MiB). [`fit`] keeps the title to [`MAX_TITLE`]
//!   characters, the links to a quarter of the frame, and the text to the
//!   rest, cut at a line, and says so in the last line.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind, MAX_NODES};
use clazel_dom::spec::Namespace;
use clazel_encoding::labels::exec::{from_number, get_an_encoding, name, number};
use clazel_encoding::labels::spec::Encoding;
use clazel_html::sniff::exec::{
    change_the_encoding, extract_label_exec, sniff, transport_encoding,
};
use clazel_html::sniff::spec::Confidence;
use clazel_ipc::frame::spec::MAX_FRAME;
use clazel_ipc::message::codec::{Msg, encode_framed};
use clazel_mime::mime_type::groups::is_html_mime_type;
use clazel_mime::mime_type::parse::parse_from_bytes;
use clazel_mime::mime_type::record::MimeType;
use clazel_mime::mime_type::serialize::serialize;
use clazel_mime::sniff::algorithms::{
    Resource, check_for_apache_bug_exec, computed_mime_type_exec,
};
use clazel_text::{Page, layout_with};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::{EncFnsExec, ExecAction};
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;

/// The resource header's length (MIME Sniffing §5.2: "at least 1445 bytes").
pub const RESOURCE_HEADER: usize = 1445;

/// The most characters of a title a `Display` carries.
pub const MAX_TITLE: usize = 1024;

/// What a document displays: the fields of one `Display`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Shown {
    /// The title.
    pub title: String,
    /// The text, lines joined by line feeds.
    pub text: String,
    /// The absolute URLs of the links, link `n` at `n - 1`.
    pub links: Vec<String>,
}

/// An HTML document after the parser: the tree, the encoding it was decoded
/// with, and whether "change the encoding" made the pipeline parse again.
pub struct Parsed {
    /// The document.
    pub arena: Arena,
    /// The encoding of the parse that built it.
    pub encoding: Encoding,
    /// Whether the parser ran twice.
    pub restarted: bool,
}

/// Why an HTML body was not parsed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NotParsed {
    /// The encoding the body is in has no decoder here (item 4.4).
    Unsupported(Encoding),
}

/// The functions the tree builder takes from other standards (its
/// `EncFnsExec`): Encoding §4.2 "get an encoding", an encoding's id being
/// its number in the table (`clazel_encoding::labels::exec::number`), and
/// HTML's "extracting a character encoding from a meta element" (see the
/// module docs for the code point mapping).
pub struct Encodings;

impl EncFnsExec for Encodings {
    fn get_an_encoding(&self, label: &[u32]) -> Option<u64> {
        get_an_encoding(label).map(|e| u64::from(number(e)))
    }

    fn extract_from_meta(&self, content: &[u32]) -> Option<Vec<u32>> {
        let bytes: Vec<u8> = content
            .iter()
            .map(|c| {
                u8::try_from(*c)
                    .ok()
                    .filter(|b| b.is_ascii())
                    .unwrap_or(0xFF)
            })
            .collect();
        extract_label_exec(&bytes).map(|l| l.into_iter().map(u32::from).collect())
    }
}

/// The encoding an encoding id of [`Encodings`] stands for.
fn encoding_of(id: u64) -> Option<Encoding> {
    let n = u8::try_from(id).ok()?;
    let e = from_number(n);
    (u64::from(number(e)) == id).then_some(e)
}

/// The encoding's name, as text.
pub fn encoding_name(e: Encoding) -> String {
    String::from_utf8_lossy(&name(e)).into_owned()
}

fn code_points(s: &[u8]) -> Vec<u32> {
    String::from_utf8_lossy(s).chars().map(u32::from).collect()
}

fn string_of(cps: &[u32]) -> Option<String> {
    cps.iter().map(|c| char::from_u32(*c)).collect()
}

/// Decode `body` with `encoding` (Encoding §6 "decode": a byte order mark
/// wins) and parse it as a document at `url`, with the confidence given.
fn decode_and_parse(
    body: &[u8],
    encoding: Encoding,
    url: &[u32],
    tentative: bool,
) -> Result<(Arena, Vec<ExecAction>), NotParsed> {
    let input = clazel_encoding::hooks::decode::decode(body, encoding)
        .ok_or(NotParsed::Unsupported(encoding))?;
    let (parser, actions) = parse_real(&Encodings, &input, url.to_vec(), false, tentative);
    Ok((parser.arena, actions))
}

/// HTML §13.2.3.2 to §13.2.3.4 and the parser over a whole body: sniff the
/// encoding (with the transport layer's, if any), decode, parse; on the
/// parser's first `ChangeEncoding`, "change the encoding" and, if that
/// gives an encoding, decode and parse once more from the start with
/// confidence certain.
pub fn parse_html(
    body: &[u8],
    transport: Option<Encoding>,
    url: &[u32],
) -> Result<Parsed, NotParsed> {
    let (encoding, confidence) = sniff(body, transport);
    let tentative = confidence == Confidence::Tentative;
    let (arena, actions) = decode_and_parse(body, encoding, url, tentative)?;
    let change = actions.iter().find_map(|a| match a {
        ExecAction::ChangeEncoding(id) => Some(*id),
        _ => None,
    });
    let again = change
        .and_then(encoding_of)
        .and_then(|new| change_the_encoding(encoding, new));
    match again {
        Some(new) => {
            // Free the first tree before building the second.
            drop(arena);
            let (arena, _) = decode_and_parse(body, new, url, false)?;
            Ok(Parsed {
                arena,
                encoding: new,
                restarted: true,
            })
        }
        None => Ok(Parsed {
            arena,
            encoding,
            restarted: false,
        }),
    }
}

/// The value of the attribute `name` (no namespace) of an element.
fn attribute<'a>(attributes: &'a [ExecAttr], name: &str) -> Option<&'a [u32]> {
    attributes
        .iter()
        .find(|a| {
            a.namespace.is_none() && a.local_name.iter().copied().eq(name.chars().map(u32::from))
        })
        .map(|a| a.value.as_slice())
}

/// The first HTML `base` element with an `href` attribute, in tree order:
/// its `href` value. Iterative, and visits each node at most once.
fn first_base_href(doc: &Arena) -> Option<Vec<u32>> {
    let n = doc.len();
    let mut stack: Vec<usize> = vec![0];
    let mut budget = n;
    while let Some(id) = stack.pop() {
        if id >= n || budget == 0 {
            continue;
        }
        budget = budget.saturating_sub(1);
        if let ExecKind::Element {
            namespace: Some(Namespace::Html),
            local_name,
            attributes,
            ..
        } = doc.kind(id)
            && local_name.iter().copied().eq("base".chars().map(u32::from))
            && let Some(href) = attribute(attributes, "href")
        {
            return Some(href.to_vec());
        }
        stack.extend(doc.children(id).iter().rev());
    }
    None
}

/// Parse `input` against `base` (URL §4.4 basic URL parser): the URL, or
/// `None` on failure. Input with a surrogate is failure (the parser takes
/// scalar values only; decoders never produce one).
fn parse_url(input: &[u32], base: Option<&ParsedUrl>) -> Option<ParsedUrl> {
    if input.iter().any(|c| char::from_u32(*c).is_none()) {
        return None;
    }
    basic_url_parser(input, base)
}

/// HTML "document base URL": the frozen base URL of the first `base`
/// element with an `href` (its value parsed against the document's
/// fallback base URL, which is the document's URL here; that URL if the
/// parse fails), else the document's URL.
pub fn base_url(doc: &Arena, url: &[u32]) -> Option<ParsedUrl> {
    let fallback = parse_url(url, None);
    match first_base_href(doc) {
        Some(href) => parse_url(&href, fallback.as_ref()).or(fallback),
        None => fallback,
    }
}

/// The page of a parsed document: the layout with every link resolved
/// against the document base URL.
pub fn page_of(doc: &Arena, url: &[u32], width: usize) -> Page {
    let base = base_url(doc, url);
    layout_with(doc, width, |value| {
        let parsed = parse_url(value, base.as_ref())?;
        string_of(&parsed.serialize(false))
    })
}

/// Lines of a preformatted block: each line feed ends a line (after
/// §13.2.3.5's newline normalisation), each line broken every `width`
/// characters (0: never), unsafe characters replaced as `clazel-text` does.
fn preformatted(text: &[u32], width: usize) -> Vec<String> {
    let mut lines = Vec::new();
    let mut line = String::new();
    let mut cols = 0usize;
    let mut cr = false;
    for &c in text {
        if c == 0x0A && cr {
            cr = false;
            continue;
        }
        cr = c == 0x0D;
        if c == 0x0A || c == 0x0D {
            lines.push(std::mem::take(&mut line));
            cols = 0;
            continue;
        }
        if width > 0 && cols == width {
            lines.push(std::mem::take(&mut line));
            cols = 0;
        }
        let ch = match char::from_u32(c) {
            Some('\t' | '\u{0C}') => ' ',
            Some(ch) if !ch.is_control() => ch,
            _ => '\u{FFFD}',
        };
        line.push(ch);
        cols = cols.saturating_add(1);
    }
    if !line.is_empty() {
        lines.push(line);
    }
    lines
}

/// A notice as the page.
fn notice(text: String) -> Shown {
    Shown {
        title: String::new(),
        text,
        links: Vec::new(),
    }
}

/// The supplied and computed MIME types of a document.
fn computed_type(content_type: &[u8], body: &[u8]) -> (Option<MimeType>, MimeType) {
    let supplied = if content_type.is_empty() {
        None
    } else {
        parse_from_bytes(content_type)
    };
    let header = body.get(..RESOURCE_HEADER).unwrap_or(body).to_vec();
    let resource = Resource {
        supplied: supplied.as_ref().map(copy),
        check_for_apache_bug: supplied.is_some() && check_for_apache_bug_exec(content_type),
        no_sniff: false,
        header,
    };
    let computed = computed_mime_type_exec(&resource, false);
    (supplied, computed)
}

fn copy(m: &MimeType) -> MimeType {
    MimeType {
        type_: m.type_.clone(),
        subtype: m.subtype.clone(),
        parameters: m.parameters.clone(),
    }
}

fn is_essence(m: &MimeType, t: &str, s: &str) -> bool {
    m.type_.iter().copied().eq(t.chars().map(u32::from))
        && m.subtype.iter().copied().eq(s.chars().map(u32::from))
}

/// The whole pipeline: what the document committed at `url` with
/// `content_type` and `body` displays, laid out `width` columns wide (0: no
/// wrapping).
pub fn render(url: &[u8], content_type: &[u8], body: &[u8], width: usize) -> Shown {
    let url_cps = code_points(url);
    let url_text = String::from_utf8_lossy(url).into_owned();
    let (supplied, computed) = computed_type(content_type, body);
    // The transport layer's encoding: the supplied type's `charset`.
    let transport = supplied.as_ref().and_then(transport_encoding);
    if is_html_mime_type(&computed) {
        return match parse_html(body, transport, &url_cps) {
            Ok(parsed) => {
                let page = page_of(&parsed.arena, &url_cps, width);
                let mut lines = page.lines;
                if parsed.arena.len() >= MAX_NODES {
                    lines.push(format!(
                        "[the page was cut at {MAX_NODES} nodes, the parser's limit]"
                    ));
                }
                Shown {
                    title: page.title,
                    text: lines.join("\n"),
                    links: page.links,
                }
            }
            Err(NotParsed::Unsupported(e)) => {
                notice(format!("encoding {} is not supported", encoding_name(e)))
            }
        };
    }
    if is_essence(&computed, "text", "plain") {
        let (encoding, _) = sniff(body, transport);
        return match clazel_encoding::hooks::decode::decode(body, encoding) {
            Some(text) => Shown {
                title: String::new(),
                text: preformatted(&text, width).join("\n"),
                links: Vec::new(),
            },
            None => notice(format!(
                "encoding {} is not supported",
                encoding_name(encoding)
            )),
        };
    }
    let shown_type = string_of(&serialize(&computed)).unwrap_or_default();
    notice(format!("{shown_type} is not shown: {url_text}"))
}

/// `s` cut to at most `max` bytes, at a character boundary.
fn cut(s: &str, max: usize) -> &str {
    let mut end = max.min(s.len());
    while end > 0 && !s.is_char_boundary(end) {
        end = end.saturating_sub(1);
    }
    s.get(..end).unwrap_or_default()
}

/// The `Display` of `shown`, made to fit one frame (`MAX_FRAME`): the title
/// cut to [`MAX_TITLE`] characters, the links kept while they take at most
/// a quarter of the frame, and the text cut at a line to what is left, with
/// a last line saying what was cut. If even that does not encode, a notice
/// alone. A page that fits is moved into the message, not copied.
pub fn fit(shown: Shown) -> Msg {
    // Room for the headers: 4 for the frame, and at most 9 per string and
    // per array, with a margin for the tag.
    let budget = MAX_FRAME.saturating_sub(4096);
    let size = shown.links.iter().fold(
        shown.title.len().saturating_add(shown.text.len()),
        |a, l| a.saturating_add(l.len()).saturating_add(9),
    );
    if size <= budget {
        let whole = Msg::Display {
            title: shown.title.into_bytes(),
            text: shown.text.into_bytes(),
            links: shown.links.into_iter().map(String::into_bytes).collect(),
        };
        return if encode_framed(&whole).is_some() {
            whole
        } else {
            too_large()
        };
    }
    let title: String = shown.title.chars().take(MAX_TITLE).collect();
    let mut links = Vec::new();
    let mut used = 0usize;
    for l in &shown.links {
        let size = l.len().saturating_add(9);
        if used.saturating_add(size) > budget / 4 {
            break;
        }
        used = used.saturating_add(size);
        links.push(l.clone().into_bytes());
    }
    let kept_links = links.len();
    let room = budget.saturating_sub(used).saturating_sub(title.len());
    let mut text = cut(&shown.text, room).to_owned();
    if text.len() < shown.text.len()
        && let Some(i) = text.rfind('\n')
    {
        text.truncate(i);
    }
    text.push_str(&format!(
        "\n[page cut to fit the 1 MiB display limit: {} of {} bytes of text, {kept_links} of {} links]",
        text.len(),
        shown.text.len(),
        shown.links.len()
    ));
    let cut_msg = Msg::Display {
        title: title.into_bytes(),
        text: text.into_bytes(),
        links,
    };
    if encode_framed(&cut_msg).is_some() {
        cut_msg
    } else {
        too_large()
    }
}

/// The `Display` of a page that cannot be sent at all (not reached: [`fit`]
/// stays under the frame's size).
fn too_large() -> Msg {
    Msg::Display {
        title: Vec::new(),
        text: b"[the page is too large to display]".to_vec(),
        links: Vec::new(),
    }
}
