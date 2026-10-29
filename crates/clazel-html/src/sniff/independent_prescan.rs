//! A second, independent transcription of HTML §13.2.3.2's "prescan a byte
//! stream to determine its encoding", the "get an attribute" algorithm it
//! uses, and the "algorithm for extracting a character encoding from a
//! `meta` element", written from the standard's text alone without reading
//! the other transcription in this module.
//!
//! Source: HTML Standard, whatwg/html commit
//! `939677714df7379fee3667040113b41c91c851e7`:
//! - <https://html.spec.whatwg.org/multipage/parsing.html#prescan-a-byte-stream-to-determine-its-encoding>
//! - <https://html.spec.whatwg.org/multipage/parsing.html#concept-get-attributes-when-sniffing>
//! - <https://html.spec.whatwg.org/multipage/urls-and-fetching.html#algorithm-for-extracting-a-character-encoding-from-a-meta-element>
//!
//! Modelling choices (each a deviation in form, never in meaning):
//! - The input byte stream is `b: Seq<u8>`, already cut by the caller at the
//!   *end condition*; the pointer *position* is an index into it.
//! - "Runs out of bytes" is reading the byte at an index `>= b.len()`. Every
//!   such read yields an `OutOfBytes` result, which propagates out of every
//!   algorithm here to [`prescan`], which then returns "get an XML encoding"
//!   applied to the same bytes ([`crate::sniff::spec::get_xml_encoding`],
//!   not transcribed here). Moving the pointer past the end is not by itself
//!   an abort; the next read is. Every move is followed by a read before any
//!   result is returned, so this is the same.
//! - "A sequence of bytes starting with" a pattern matches only when the
//!   whole pattern lies within `b`; a shorter remainder is "any other byte"
//!   (or a shorter pattern below it in the switch).
//! - Attribute names and values, and the strings built from them, are
//!   `Seq<u8>`: every code point appended is a byte value (or a byte value
//!   plus 0x20 for A to Z, still below 0x80). They become `Seq<u32>` only
//!   when handed to "get an encoding".
//! - "Get an encoding" is [`clazel_encoding::labels::spec::get_an_encoding`],
//!   `None` being failure. A returned "character encoding" is `Some`,
//!   "nothing"/"failure" is `None`.
//! - *charset* in the `<meta` branch has three states: null (`None`),
//!   failure (`Some(None)`) and an encoding (`Some(Some(e))`).
//! - *need pragma* is `Option<bool>`, `None` being null.
//! - The "Processing" steps cannot meet a null *charset* (whenever *need
//!   pragma* is set, *charset* was set too); were it null, step 13 here
//!   treats it like failure ("next byte"). This changes no result.
//! - Loops ("return to the step labeled ...", "redo this step") are
//!   recursion on the position. A step that "aborts" get an attribute
//!   returns its result. The user agent's options ("may") are never taken.
//! - Termination of the recursions that call get an attribute (or a search)
//!   and continue from the position it returns is proven by the `#[via_fn]`
//!   proof functions at the end, from the fact that those return positions
//!   no earlier than they started (later, for an attribute). They are only
//!   termination arguments, not facts about the algorithm's results.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Byte classes
// ---------------------------------------------------------------------------

/// One of 0x09 (HT), 0x0A (LF), 0x0C (FF), 0x0D (CR) or 0x20 (SP). This is
/// also Infra's "ASCII whitespace" (U+0009 TAB, U+000A LF, U+000C FF,
/// U+000D CR, U+0020 SPACE), which the meta algorithm uses on characters
/// that here are bytes.
pub open spec fn is_space(c: u8) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

/// In the range 0x41 (A) to 0x5A (Z).
pub open spec fn is_upper(c: u8) -> bool {
    0x41 <= c && c <= 0x5A
}

/// In the range 0x61 (a) to 0x7A (z).
pub open spec fn is_lower(c: u8) -> bool {
    0x61 <= c && c <= 0x7A
}

/// "the code point b+0x20" for A to Z ("This converts the input to
/// lowercase"), and the byte itself otherwise.
pub open spec fn lowered(c: u8) -> u8 {
    if is_upper(c) {
        (c + 0x20) as u8
    } else {
        c
    }
}

/// A string of bytes as the string of code points with the same values.
pub open spec fn as_code_points(s: Seq<u8>) -> Seq<u32> {
    s.map_values(|x: u8| x as u32)
}

// ---------------------------------------------------------------------------
// Results
// ---------------------------------------------------------------------------

/// The outcome of "get an attribute".
pub enum GetAttribute {
    /// Ran out of bytes: the prescan aborts.
    OutOfBytes,
    /// "There isn't one" (no attribute was sniffed); *position* is where
    /// the pointer was left.
    NoAttribute {
        /// The pointer, at the 0x3E (>) byte.
        position: nat,
    },
    /// An attribute was sniffed.
    Attribute {
        /// *attribute name*.
        name: Seq<u8>,
        /// *attribute value*.
        value: Seq<u8>,
        /// Where the pointer was left.
        position: nat,
    },
}

/// The outcome of one pass of the prescan's step 3 (*Loop*) switch.
pub enum LoopStep {
    /// Ran out of bytes: the prescan aborts.
    OutOfBytes,
    /// The prescan returns this encoding.
    Return(clazel_encoding::labels::spec::Encoding),
    /// Go on to step 4 (*Next byte*) with the pointer here.
    NextByte(nat),
}

/// The outcome of the prescan's loop.
pub enum PrescanLoop {
    /// Ran out of bytes: the prescan aborts.
    OutOfBytes,
    /// The prescan returns this encoding.
    Return(clazel_encoding::labels::spec::Encoding),
}

// ---------------------------------------------------------------------------
// Prescan a byte stream to determine its encoding
// ---------------------------------------------------------------------------

/// "Prescan a byte stream to determine its encoding" (HTML §13.2.3.2,
/// <https://html.spec.whatwg.org/multipage/parsing.html#prescan-a-byte-stream-to-determine-its-encoding>)
/// on the bytes `b`. `None` is failure.
pub open spec fn prescan(b: Seq<u8>) -> Option<clazel_encoding::labels::spec::Encoding> {
    // 1. "Let position be a pointer to a byte in the input byte stream,
    //    initially pointing at the first byte."
    let position: nat = 0;
    // 2. "Prescan for UTF-16 XML declarations: If position points to:"
    //    "A sequence of bytes starting with: 0x3C, 0x0, 0x3F, 0x0, 0x78, 0x0
    //    (case-sensitive UTF-16 little-endian '<?x')" -> "Return UTF-16LE."
    if starts_with_6(b, position, 0x3C, 0x00, 0x3F, 0x00, 0x78, 0x00) {
        Some(clazel_encoding::labels::spec::Encoding::Utf16Le)
    }
    //    "A sequence of bytes starting with: 0x0, 0x3C, 0x0, 0x3F, 0x0, 0x78
    //    (case-sensitive UTF-16 big-endian '<?x')" -> "Return UTF-16BE."
    else if starts_with_6(b, position, 0x00, 0x3C, 0x00, 0x3F, 0x00, 0x78) {
        Some(clazel_encoding::labels::spec::Encoding::Utf16Be)
    } else {
        // 3, 4.
        match prescan_loop(b, position) {
            PrescanLoop::Return(e) => Some(e),
            // "If at any point during these steps ... the user agent ...
            // runs out of bytes ... then abort the prescan ... and return
            // the result get an XML encoding applied to the same bytes that
            // the prescan ... was applied to."
            PrescanLoop::OutOfBytes => crate::sniff::spec::get_xml_encoding(b),
        }
    }
}

/// `b` holds, from `p`, the six bytes `x0` to `x5`.
pub open spec fn starts_with_6(b: Seq<u8>, p: nat, x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8) -> bool {
    p + 6 <= b.len() && b[p as int] == x0 && b[(p + 1) as int] == x1 && b[(p + 2) as int] == x2 && b[(p + 3) as int] == x3
        && b[(p + 4) as int] == x4 && b[(p + 5) as int] == x5
}

/// Steps 3 (*Loop*) and 4 (*Next byte*), with the pointer at `position`.
pub open spec fn prescan_loop(b: Seq<u8>, position: nat) -> PrescanLoop
    decreases b.len() - position via prescan_loop_decreases
{
    // 3. "Loop: If position points to:" (reading the byte: none is left)
    if position >= b.len() {
        PrescanLoop::OutOfBytes
    } else {
        match loop_step(b, position) {
            LoopStep::OutOfBytes => PrescanLoop::OutOfBytes,
            LoopStep::Return(e) => PrescanLoop::Return(e),
            // 4. "Next byte: Move position so it points at the next byte in
            //    the input byte stream, and return to the step above labeled
            //    loop."
            LoopStep::NextByte(p) => prescan_loop(b, p + 1),
        }
    }
}

/// `<!--` at `p`: "0x3C 0x21 0x2D 0x2D".
pub open spec fn starts_comment(b: Seq<u8>, p: nat) -> bool {
    p + 4 <= b.len() && b[p as int] == 0x3C && b[(p + 1) as int] == 0x21 && b[(p + 2) as int] == 0x2D && b[(p + 3) as int]
        == 0x2D
}

/// `<meta` followed by a space or slash at `p`: "0x3C, 0x4D or 0x6D, 0x45 or
/// 0x65, 0x54 or 0x74, 0x41 or 0x61, and one of 0x09, 0x0A, 0x0C, 0x0D,
/// 0x20, 0x2F".
pub open spec fn starts_meta(b: Seq<u8>, p: nat) -> bool {
    p + 6 <= b.len() && b[p as int] == 0x3C && (b[(p + 1) as int] == 0x4D || b[(p + 1) as int] == 0x6D) && (b[(p + 2) as int]
        == 0x45 || b[(p + 2) as int] == 0x65) && (b[(p + 3) as int] == 0x54 || b[(p + 3) as int] == 0x74) && (b[(p + 4) as int] == 0x41
        || b[(p + 4) as int] == 0x61) && (is_space(b[(p + 5) as int]) || b[(p + 5) as int] == 0x2F)
}

/// A tag at `p`: "a 0x3C byte (<), optionally a 0x2F byte (/), and finally a
/// byte in the range 0x41-0x5A or 0x61-0x7A (A-Z or a-z)".
pub open spec fn starts_tag(b: Seq<u8>, p: nat) -> bool {
    // Without the optional 0x2F.
    (p + 2 <= b.len() && b[p as int] == 0x3C && (is_upper(b[(p + 1) as int]) || is_lower(b[(p + 1) as int])))
    // With it.
     || (p + 3 <= b.len() && b[p as int] == 0x3C && b[(p + 1) as int] == 0x2F && (is_upper(b[(p + 2) as int])
        || is_lower(b[(p + 2) as int])))
}

/// `<!`, `</` or `<?` at `p`: "0x3C 0x21", "0x3C 0x2F", "0x3C 0x3F".
pub open spec fn starts_markup(b: Seq<u8>, p: nat) -> bool {
    p + 2 <= b.len() && b[p as int] == 0x3C && (b[(p + 1) as int] == 0x21 || b[(p + 1) as int] == 0x2F || b[(p + 1) as int]
        == 0x3F)
}

/// One pass of step 3's switch with the pointer at `position`, which is
/// within `b`.
pub open spec fn loop_step(b: Seq<u8>, position: nat) -> LoopStep {
    // "A sequence of bytes starting with: 0x3C 0x21 0x2D 0x2D (`<!--`)"
    if starts_comment(b, position) {
        // "Advance the position pointer so that it points at the first 0x3E
        // byte which is preceded by two 0x2D bytes (i.e. at the end of an
        // ASCII '-->' sequence) and comes after the 0x3C byte that was
        // found. (The two 0x2D bytes can be the same as those in the '<!--'
        // sequence.)"
        match find_comment_end(b, position + 1) {
            None => LoopStep::OutOfBytes,
            Some(p) => LoopStep::NextByte(p),
        }
    }
    // "A sequence of bytes starting with: 0x3C, 0x4D or 0x6D, ... (case-
    // insensitive ASCII '<meta' followed by a space or slash)"
    else if starts_meta(b, position) {
        // 1. "Advance the position pointer so that it points at the next
        //    0x09, 0x0A, 0x0C, 0x0D, 0x20, or 0x2F byte (the one in sequence
        //    of characters matched above)."
        // 2. "Let attribute list be an empty list of strings."
        // 3. "Let got pragma be false."
        // 4. "Let need pragma be null."
        // 5. "Let charset be the null value ..."
        meta_attributes(b, position + 5, Seq::empty(), false, None, None)
    }
    // "A sequence of bytes starting with a 0x3C byte (<), optionally a 0x2F
    // byte (/), and finally a byte in the range 0x41-0x5A or 0x61-0x7A"
    else if starts_tag(b, position) {
        // 1. "Advance the position pointer so that it points at the next
        //    0x09 (HT), 0x0A (LF), 0x0C (FF), 0x0D (CR), 0x20 (SP), or 0x3E
        //    (>) byte." The byte at position is 0x3C, none of these, so the
        //    search starts after it.
        match find_tag_end(b, position + 1) {
            None => LoopStep::OutOfBytes,
            // 2. "Repeatedly get an attribute until no further attributes
            //    can be found, then jump to the step below labeled next
            //    byte."
            Some(p) => tag_attributes(b, p),
        }
    }
    // "0x3C 0x21 (`<!`)", "0x3C 0x2F (`</`)", "0x3C 0x3F (`<?`)"
    else if starts_markup(b, position) {
        // "Advance the position pointer so that it points at the first 0x3E
        // byte (>) that comes after the 0x3C byte that was found."
        match find_gt(b, position + 1) {
            None => LoopStep::OutOfBytes,
            Some(p) => LoopStep::NextByte(p),
        }
    }
    // "Any other byte": "Do nothing with that byte."
    else {
        LoopStep::NextByte(position)
    }
}

/// The first index at or after `p` of a 0x3E byte preceded by two 0x2D
/// bytes, or `None` on running out of bytes.
pub open spec fn find_comment_end(b: Seq<u8>, p: nat) -> Option<nat>
    decreases b.len() - p,
{
    if p >= b.len() {
        None
    } else if b[p as int] == 0x3E && b[(p - 1) as int] == 0x2D && b[(p - 2) as int] == 0x2D {
        Some(p)
    } else {
        find_comment_end(b, p + 1)
    }
}

/// The first index at or after `p` of a 0x09, 0x0A, 0x0C, 0x0D, 0x20 or
/// 0x3E byte, or `None` on running out of bytes.
pub open spec fn find_tag_end(b: Seq<u8>, p: nat) -> Option<nat>
    decreases b.len() - p,
{
    if p >= b.len() {
        None
    } else if is_space(b[p as int]) || b[p as int] == 0x3E {
        Some(p)
    } else {
        find_tag_end(b, p + 1)
    }
}

/// The first index at or after `p` of a 0x3E byte, or `None` on running out
/// of bytes.
pub open spec fn find_gt(b: Seq<u8>, p: nat) -> Option<nat>
    decreases b.len() - p,
{
    if p >= b.len() {
        None
    } else if b[p as int] == 0x3E {
        Some(p)
    } else {
        find_gt(b, p + 1)
    }
}

/// The tag branch's step 2: "Repeatedly get an attribute until no further
/// attributes can be found, then jump to the step below labeled next byte."
pub open spec fn tag_attributes(b: Seq<u8>, position: nat) -> LoopStep
    decreases b.len() - position via tag_attributes_decreases
{
    match get_an_attribute(b, position) {
        GetAttribute::OutOfBytes => LoopStep::OutOfBytes,
        GetAttribute::NoAttribute { position: p } => LoopStep::NextByte(p),
        GetAttribute::Attribute { name: _, value: _, position: p } => tag_attributes(b, p),
    }
}

/// "http-equiv"
pub open spec fn http_equiv() -> Seq<u8> {
    seq![0x68u8, 0x74, 0x74, 0x70, 0x2D, 0x65, 0x71, 0x75, 0x69, 0x76]
}

/// "content-type"
pub open spec fn content_type() -> Seq<u8> {
    seq![0x63u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65]
}

/// "content"
pub open spec fn content() -> Seq<u8> {
    seq![0x63u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74]
}

/// "charset"
pub open spec fn charset_name() -> Seq<u8> {
    seq![0x63u8, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74]
}

/// Whether `name` is an item of `list`.
pub open spec fn in_list(list: Seq<Seq<u8>>, name: Seq<u8>) -> bool
    decreases list.len(),
{
    if list.len() == 0 {
        false
    } else if list.last() == name {
        true
    } else {
        in_list(list.drop_last(), name)
    }
}

/// The `<meta` branch from step 6 (*Attributes*) on, with the pointer at
/// `position` and the state *attribute list*, *got pragma*, *need pragma*
/// and *charset*.
pub open spec fn meta_attributes(
    b: Seq<u8>,
    position: nat,
    attribute_list: Seq<Seq<u8>>,
    got_pragma: bool,
    need_pragma: Option<bool>,
    charset: Option<Option<clazel_encoding::labels::spec::Encoding>>,
) -> LoopStep
    decreases b.len() - position via meta_attributes_decreases
{
    // 6. "Attributes: Get an attribute and its value. If no attribute was
    //    sniffed, then jump to the processing step below."
    match get_an_attribute(b, position) {
        GetAttribute::OutOfBytes => LoopStep::OutOfBytes,
        GetAttribute::NoAttribute { position: p } => meta_processing(
            p,
            got_pragma,
            need_pragma,
            charset,
        ),
        GetAttribute::Attribute { name, value, position: p } => {
            // 7. "If the attribute's name is already in attribute list, then
            //    return to the step labeled attributes."
            if in_list(attribute_list, name) {
                meta_attributes(b, p, attribute_list, got_pragma, need_pragma, charset)
            } else {
                // 8. "Add the attribute's name to attribute list."
                let attribute_list = attribute_list.push(name);
                // 9. "Run the appropriate step from the following list, if
                //    one applies:"
                // "If the attribute's name is "http-equiv"": "If the
                // attribute's value is "content-type", then set got pragma
                // to true."
                if name == http_equiv() {
                    if value == content_type() {
                        // 10. "Return to the step labeled attributes."
                        meta_attributes(b, p, attribute_list, true, need_pragma, charset)
                    } else {
                        // 10.
                        meta_attributes(b, p, attribute_list, got_pragma, need_pragma, charset)
                    }
                }
                // "If the attribute's name is "content"": "Apply the
                // algorithm for extracting a character encoding from a meta
                // element, giving the attribute's value as the string to
                // parse. If a character encoding is returned, and if charset
                // is still set to null, let charset be the encoding
                // returned, and set need pragma to true."
                 else if name == content() {
                    match extract_character_encoding_from_meta(value) {
                        Some(e) => if charset is None {
                            // 10.
                            meta_attributes(b, p, attribute_list, got_pragma, Some(true), Some(Some(e)))
                        } else {
                            // 10.
                            meta_attributes(b, p, attribute_list, got_pragma, need_pragma, charset)
                        },
                        // 10.
                        None => meta_attributes(
                            b,
                            p,
                            attribute_list,
                            got_pragma,
                            need_pragma,
                            charset,
                        ),
                    }
                }
                // "If the attribute's name is "charset"": "Let charset be
                // the result of getting an encoding from the attribute's
                // value, and set need pragma to false."
                 else if name == charset_name() {
                    // 10.
                    meta_attributes(
                        b,
                        p,
                        attribute_list,
                        got_pragma,
                        Some(false),
                        Some(clazel_encoding::labels::spec::get_an_encoding(as_code_points(value))),
                    )
                } else {
                    // No step applies. 10.
                    meta_attributes(b, p, attribute_list, got_pragma, need_pragma, charset)
                }
            }
        },
    }
}

/// The `<meta` branch's steps 11 (*Processing*) to 16, with the pointer at
/// `position`.
pub open spec fn meta_processing(
    position: nat,
    got_pragma: bool,
    need_pragma: Option<bool>,
    charset: Option<Option<clazel_encoding::labels::spec::Encoding>>,
) -> LoopStep {
    // 11. "Processing: If need pragma is null, then jump to the step below
    //     labeled next byte."
    if need_pragma is None {
        LoopStep::NextByte(position)
    }
    // 12. "If need pragma is true but got pragma is false, then jump to the
    //     step below labeled next byte."
     else if need_pragma == Some(true) && !got_pragma {
        LoopStep::NextByte(position)
    } else {
        match charset {
            // 13. "If charset is failure, then jump to the step below labeled
            //     next byte."
            Some(None) => LoopStep::NextByte(position),
            // Null cannot occur here (need pragma is set only together with
            // charset); treated as failure (see the modelling choices).
            None => LoopStep::NextByte(position),
            Some(Some(e)) => {
                // 14. "If charset is UTF-16BE/LE, then set charset to UTF-8."
                let e = if e == clazel_encoding::labels::spec::Encoding::Utf16Be || e
                    == clazel_encoding::labels::spec::Encoding::Utf16Le {
                    clazel_encoding::labels::spec::Encoding::Utf8
                } else {
                    e
                };
                // 15. "If charset is x-user-defined, then set charset to
                //     windows-1252."
                let e = if e == clazel_encoding::labels::spec::Encoding::XUserDefined {
                    clazel_encoding::labels::spec::Encoding::Windows1252
                } else {
                    e
                };
                // 16. "Return charset."
                LoopStep::Return(e)
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Get an attribute
// ---------------------------------------------------------------------------

/// "Get an attribute" (HTML §13.2.3.2,
/// <https://html.spec.whatwg.org/multipage/parsing.html#concept-get-attributes-when-sniffing>)
/// with the pointer at `position`: steps 1 to 3.
pub open spec fn get_an_attribute(b: Seq<u8>, position: nat) -> GetAttribute
    decreases b.len() - position,
{
    if position >= b.len() {
        GetAttribute::OutOfBytes
    }
    // 1. "If the byte at position is one of 0x09 (HT), 0x0A (LF), 0x0C (FF),
    //    0x0D (CR), 0x20 (SP), or 0x2F (/), then advance position to the
    //    next byte and redo this step."
     else if is_space(b[position as int]) || b[position as int] == 0x2F {
        get_an_attribute(b, position + 1)
    }
    // 2. "If the byte at position is 0x3E (>), then abort the get an
    //    attribute algorithm. There isn't one."
     else if b[position as int] == 0x3E {
        GetAttribute::NoAttribute { position }
    } else {
        // 3. "Otherwise, the byte at position is the start of the attribute
        //    name. Let attribute name and attribute value be the empty
        //    string."
        attribute_name_step(b, position, Seq::empty())
    }
}

/// Get an attribute, steps 4 and 5, with the pointer at `position`.
pub open spec fn attribute_name_step(b: Seq<u8>, position: nat, attribute_name: Seq<u8>) -> GetAttribute
    decreases b.len() - position,
{
    if position >= b.len() {
        GetAttribute::OutOfBytes
    } else {
        // 4. "Process the byte at position as follows:"
        let c = b[position as int];
        // "If it is 0x3D (=), and the attribute name is longer than the
        // empty string": "Advance position to the next byte and jump to the
        // step below labeled value."
        if c == 0x3D && attribute_name.len() > 0 {
            value_step(b, position + 1, attribute_name)
        }
        // "If it is 0x09 (HT), 0x0A (LF), 0x0C (FF), 0x0D (CR), or 0x20
        // (SP)": "Jump to the step below labeled spaces."
         else if is_space(c) {
            spaces_step(b, position, attribute_name)
        }
        // "If it is 0x2F (/) or 0x3E (>)": "Abort the get an attribute
        // algorithm. The attribute's name is the value of attribute name,
        // its value is the empty string."
         else if c == 0x2F || c == 0x3E {
            GetAttribute::Attribute { name: attribute_name, value: Seq::empty(), position }
        }
        // "If it is in the range 0x41 (A) to 0x5A (Z)": "Append the code
        // point b+0x20 to attribute name"; "Anything else": "Append the code
        // point with the same value as the byte at position to attribute
        // name."
        // 5. "Advance position to the next byte and return to the previous
        //    step."
         else {
            attribute_name_step(b, position + 1, attribute_name.push(lowered(c)))
        }
    }
}

/// Get an attribute, steps 6 (*Spaces*) to 8, with the pointer at
/// `position`.
pub open spec fn spaces_step(b: Seq<u8>, position: nat, attribute_name: Seq<u8>) -> GetAttribute
    decreases b.len() - position,
{
    if position >= b.len() {
        GetAttribute::OutOfBytes
    }
    // 6. "Spaces: If the byte at position is one of 0x09 (HT), 0x0A (LF),
    //    0x0C (FF), 0x0D (CR), or 0x20 (SP), then advance position to the
    //    next byte, then, repeat this step."
     else if is_space(b[position as int]) {
        spaces_step(b, position + 1, attribute_name)
    }
    // 7. "If the byte at position is not 0x3D (=), abort the get an
    //    attribute algorithm. The attribute's name is the value of attribute
    //    name, its value is the empty string."
     else if b[position as int] != 0x3D {
        GetAttribute::Attribute { name: attribute_name, value: Seq::empty(), position }
    } else {
        // 8. "Advance position past the 0x3D (=) byte."
        value_step(b, position + 1, attribute_name)
    }
}

/// Get an attribute, steps 9 (*Value*) and 10, with the pointer at
/// `position`.
pub open spec fn value_step(b: Seq<u8>, position: nat, attribute_name: Seq<u8>) -> GetAttribute
    decreases b.len() - position,
{
    if position >= b.len() {
        GetAttribute::OutOfBytes
    }
    // 9. "Value: If the byte at position is one of 0x09 (HT), 0x0A (LF),
    //    0x0C (FF), 0x0D (CR), or 0x20 (SP), then advance position to the
    //    next byte, then, repeat this step."
     else if is_space(b[position as int]) {
        value_step(b, position + 1, attribute_name)
    } else {
        // 10. "Process the byte at position as follows:"
        let c = b[position as int];
        // "If it is 0x22 (") or 0x27 (')":
        //   1. "Let b be the value of the byte at position."
        if c == 0x22 || c == 0x27 {
            quote_loop(b, c, position, attribute_name, Seq::empty())
        }
        // "If it is 0x3E (>)": "Abort the get an attribute algorithm. The
        // attribute's name is the value of attribute name, its value is the
        // empty string."
         else if c == 0x3E {
            GetAttribute::Attribute { name: attribute_name, value: Seq::empty(), position }
        }
        // "If it is in the range 0x41 (A) to 0x5A (Z)": "Append a code point
        // b+0x20 to attribute value ... Advance position to the next byte.";
        // "Anything else": "Append a code point with the same value as the
        // byte at position to attribute value. Advance position to the next
        // byte."
         else {
            unquoted_value_step(b, position + 1, attribute_name, seq![lowered(c)])
        }
    }
}

/// Get an attribute, step 10's quoted value: from substep 2 (*Quote loop*),
/// with the pointer at `position` before it advances and the quote byte
/// `quote` (the standard's *b*).
pub open spec fn quote_loop(
    b: Seq<u8>,
    quote: u8,
    position: nat,
    attribute_name: Seq<u8>,
    attribute_value: Seq<u8>,
) -> GetAttribute
    decreases b.len() - position,
{
    // 2. "Quote loop: Advance position to the next byte."
    let position = position + 1;
    if position >= b.len() {
        GetAttribute::OutOfBytes
    }
    // 3. "If the value of the byte at position is the value of b, then
    //    advance position to the next byte and abort the "get an attribute"
    //    algorithm. The attribute's name is the value of attribute name, and
    //    its value is the value of attribute value."
     else if b[position as int] == quote {
        GetAttribute::Attribute { name: attribute_name, value: attribute_value, position: position + 1 }
    }
    // 4. "Otherwise, if the value of the byte at position is in the range
    //    0x41 (A) to 0x5A (Z), then append a code point to attribute value
    //    whose value is 0x20 more than the value of the byte at position."
    // 5. "Otherwise, append a code point to attribute value whose value is
    //    the same as the value of the byte at position."
    // 6. "Return to the step above labeled quote loop."
     else {
        quote_loop(b, quote, position, attribute_name, attribute_value.push(lowered(b[position as int])))
    }
}

/// Get an attribute, steps 11 and 12, with the pointer at `position`.
pub open spec fn unquoted_value_step(
    b: Seq<u8>,
    position: nat,
    attribute_name: Seq<u8>,
    attribute_value: Seq<u8>,
) -> GetAttribute
    decreases b.len() - position,
{
    if position >= b.len() {
        GetAttribute::OutOfBytes
    } else {
        // 11. "Process the byte at position as follows:"
        let c = b[position as int];
        // "If it is 0x09 (HT), 0x0A (LF), 0x0C (FF), 0x0D (CR), 0x20 (SP),
        // or 0x3E (>)": "Abort the get an attribute algorithm. The
        // attribute's name is the value of attribute name and its value is
        // the value of attribute value."
        if is_space(c) || c == 0x3E {
            GetAttribute::Attribute { name: attribute_name, value: attribute_value, position }
        }
        // "If it is in the range 0x41 (A) to 0x5A (Z)": "Append a code point
        // b+0x20 to attribute value"; "Anything else": "Append a code point
        // with the same value as the byte at position to attribute value."
        // 12. "Advance position to the next byte and return to the previous
        //     step."
         else {
            unquoted_value_step(b, position + 1, attribute_name, attribute_value.push(lowered(c)))
        }
    }
}

// ---------------------------------------------------------------------------
// The algorithm for extracting a character encoding from a meta element
// ---------------------------------------------------------------------------

/// "The algorithm for extracting a character encoding from a meta element"
/// (HTML "Extracting character encodings from meta elements",
/// <https://html.spec.whatwg.org/multipage/urls-and-fetching.html#algorithm-for-extracting-a-character-encoding-from-a-meta-element>)
/// given the string `s`. `None` is "nothing" (and also a failure of "get an
/// encoding", which the algorithm returns as its result).
pub open spec fn extract_character_encoding_from_meta(s: Seq<u8>) -> Option<
    clazel_encoding::labels::spec::Encoding,
> {
    // 1. "Let position be a pointer into s, initially pointing at the start
    //    of the string." (A pointer between characters: index i points just
    //    before s[i].)
    extract_loop(s, 0)
}

/// Whether the seven characters of `s` from `k` are an ASCII
/// case-insensitive match for "charset".
pub open spec fn matches_charset_at(s: Seq<u8>, k: nat) -> bool {
    k + 7 <= s.len() && lowered(s[k as int]) == 0x63 && lowered(s[(k + 1) as int]) == 0x68 && lowered(
        s[(k + 2) as int],
    ) == 0x61 && lowered(s[(k + 3) as int]) == 0x72 && lowered(s[(k + 4) as int]) == 0x73 && lowered(s[(k + 5) as int])
        == 0x65 && lowered(s[(k + 6) as int]) == 0x74
}

/// The first `k >= i` at which "charset" matches, or `None`.
pub open spec fn find_charset(s: Seq<u8>, i: nat) -> Option<nat>
    decreases s.len() - i,
{
    if i + 7 > s.len() {
        None
    } else if matches_charset_at(s, i) {
        Some(i)
    } else {
        find_charset(s, i + 1)
    }
}

/// The first index at or after `i` that is not ASCII whitespace (or
/// `s.len()`).
pub open spec fn skip_whitespace(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i,
{
    if i < s.len() && is_space(s[i as int]) {
        skip_whitespace(s, i + 1)
    } else {
        i
    }
}

/// The first index at or after `i` of a later `c` in `s`, or `None`.
pub open spec fn find_byte(s: Seq<u8>, i: nat, c: u8) -> Option<nat>
    decreases s.len() - i,
{
    if i >= s.len() {
        None
    } else if s[i as int] == c {
        Some(i)
    } else {
        find_byte(s, i + 1, c)
    }
}

/// The first index at or after `i` of ASCII whitespace or U+003B (;), or
/// `s.len()`.
pub open spec fn find_value_end(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i,
{
    if i >= s.len() {
        i
    } else if is_space(s[i as int]) || s[i as int] == 0x3B {
        i
    } else {
        find_value_end(s, i + 1)
    }
}

/// The extraction algorithm from step 2 (*Loop*), with the pointer just
/// before index `position`.
pub open spec fn extract_loop(s: Seq<u8>, position: nat) -> Option<
    clazel_encoding::labels::spec::Encoding,
>
    decreases s.len() - position via extract_loop_decreases
{
    // 2. "Loop: Find the first seven characters in s after position that are
    //    an ASCII case-insensitive match for the word "charset". If no such
    //    match is found, return nothing."
    match find_charset(s, position) {
        None => None,
        Some(k) => {
            // 3. "Skip any ASCII whitespace that immediately follow the word
            //    "charset" (there might not be any)."
            let j = skip_whitespace(s, k + 7);
            // 4. "If the next character is not a U+003D EQUALS SIGN (=), then
            //    move position to point just before that next character, and
            //    jump back to the step labeled loop." (No next character is
            //    not "=" either; the loop then finds no match.)
            if j >= s.len() || s[j as int] != 0x3D {
                extract_loop(s, j)
            } else {
                // 5. "Skip any ASCII whitespace that immediately follow the
                //    equals sign (there might not be any)."
                let v = skip_whitespace(s, j + 1);
                // 6. "Process the next character as follows:"
                // "If there is no next character": "Return nothing."
                if v >= s.len() {
                    None
                } else {
                    let c = s[v as int];
                    // "If it is a U+0022 QUOTATION MARK character (") and
                    // there is a later U+0022 QUOTATION MARK character (") in
                    // s", "If it is a U+0027 APOSTROPHE character (') and
                    // there is a later U+0027 APOSTROPHE character (') in s":
                    // "Return the result of getting an encoding from the
                    // substring that is between this character and the next
                    // earliest occurrence of this character."
                    // "If it is an unmatched U+0022 QUOTATION MARK character
                    // (")", "If it is an unmatched U+0027 APOSTROPHE
                    // character (')": "Return nothing."
                    if c == 0x22 || c == 0x27 {
                        match find_byte(s, v + 1, c) {
                            Some(m) => clazel_encoding::labels::spec::get_an_encoding(
                                as_code_points(s.subrange((v + 1) as int, m as int)),
                            ),
                            None => None,
                        }
                    }
                    // "Otherwise": "Return the result of getting an encoding
                    // from the substring that consists of this character up
                    // to but not including the first ASCII whitespace or
                    // U+003B SEMICOLON character (;), or the end of s,
                    // whichever comes first." (This character is ASCII
                    // whitespace by no means, step 5 skipped it; it is
                    // always included, so the search starts after it.)
                     else {
                        clazel_encoding::labels::spec::get_an_encoding(
                            as_code_points(s.subrange(v as int, find_value_end(s, v + 1) as int)),
                        )
                    }
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Termination only
// ---------------------------------------------------------------------------

/// Termination of [`prescan_loop`]: step 3 leaves the pointer within `b`
/// and no earlier than it found it.
#[via_fn]
pub proof fn prescan_loop_decreases(b: Seq<u8>, position: nat) {
    if position < b.len() {
        lemma_loop_step_progress(b, position);
    }
}

/// Termination of [`tag_attributes`]: a sniffed attribute ends after where
/// get an attribute started, and within or just past `b`.
#[via_fn]
pub proof fn tag_attributes_decreases(b: Seq<u8>, position: nat) {
    lemma_get_an_attribute_progress(b, position);
}

/// Termination of [`meta_attributes`]: as for [`tag_attributes`].
#[via_fn]
pub proof fn meta_attributes_decreases(
    b: Seq<u8>,
    position: nat,
    attribute_list: Seq<Seq<u8>>,
    got_pragma: bool,
    need_pragma: Option<bool>,
    charset: Option<Option<clazel_encoding::labels::spec::Encoding>>,
) {
    lemma_get_an_attribute_progress(b, position);
}

/// Termination of [`extract_loop`]: the loop resumes after the match.
#[via_fn]
pub proof fn extract_loop_decreases(s: Seq<u8>, position: nat) {
    lemma_find_charset_progress(s, position);
    match find_charset(s, position) {
        Some(k) => lemma_skip_whitespace_progress(s, k + 7),
        None => {},
    }
}

/// Step 3 of the prescan leaves the pointer within `b` and no earlier than
/// `position`.
pub proof fn lemma_loop_step_progress(b: Seq<u8>, position: nat)
    requires
        position < b.len(),
    ensures
        match loop_step(b, position) {
            LoopStep::NextByte(p) => position <= p < b.len(),
            _ => true,
        },
{
    lemma_find_comment_end_progress(b, position + 1);
    lemma_meta_attributes_progress(b, position + 5, Seq::empty(), false, None, None);
    lemma_find_tag_end_progress(b, position + 1);
    match find_tag_end(b, position + 1) {
        Some(p) => lemma_tag_attributes_progress(b, p),
        None => {},
    }
    lemma_find_gt_progress(b, position + 1);
}

/// [`find_comment_end`] finds within `b`, no earlier than it starts.
pub proof fn lemma_find_comment_end_progress(b: Seq<u8>, p: nat)
    ensures
        match find_comment_end(b, p) {
            Some(k) => p <= k < b.len(),
            None => true,
        },
    decreases b.len() - p,
{
    if p < b.len() {
        lemma_find_comment_end_progress(b, p + 1);
    }
}

/// [`find_tag_end`] finds within `b`, no earlier than it starts.
pub proof fn lemma_find_tag_end_progress(b: Seq<u8>, p: nat)
    ensures
        match find_tag_end(b, p) {
            Some(k) => p <= k < b.len(),
            None => true,
        },
    decreases b.len() - p,
{
    if p < b.len() {
        lemma_find_tag_end_progress(b, p + 1);
    }
}

/// [`find_gt`] finds within `b`, no earlier than it starts.
pub proof fn lemma_find_gt_progress(b: Seq<u8>, p: nat)
    ensures
        match find_gt(b, p) {
            Some(k) => p <= k < b.len(),
            None => true,
        },
    decreases b.len() - p,
{
    if p < b.len() {
        lemma_find_gt_progress(b, p + 1);
    }
}

/// [`tag_attributes`] stops within `b`, no earlier than it starts.
pub proof fn lemma_tag_attributes_progress(b: Seq<u8>, position: nat)
    ensures
        match tag_attributes(b, position) {
            LoopStep::NextByte(p) => position <= p < b.len(),
            _ => true,
        },
    decreases b.len() - position,
{
    lemma_get_an_attribute_progress(b, position);
    match get_an_attribute(b, position) {
        GetAttribute::Attribute { name: _, value: _, position: p } => {
            lemma_tag_attributes_progress(b, p);
        },
        _ => {},
    }
}

/// [`meta_attributes`] stops within `b`, no earlier than it starts.
pub proof fn lemma_meta_attributes_progress(
    b: Seq<u8>,
    position: nat,
    attribute_list: Seq<Seq<u8>>,
    got_pragma: bool,
    need_pragma: Option<bool>,
    charset: Option<Option<clazel_encoding::labels::spec::Encoding>>,
)
    ensures
        match meta_attributes(b, position, attribute_list, got_pragma, need_pragma, charset) {
            LoopStep::NextByte(p) => position <= p < b.len(),
            _ => true,
        },
    decreases b.len() - position,
{
    lemma_get_an_attribute_progress(b, position);
    match get_an_attribute(b, position) {
        GetAttribute::Attribute { name, value, position: p } => {
            let list = attribute_list.push(name);
            lemma_meta_attributes_progress(b, p, attribute_list, got_pragma, need_pragma, charset);
            lemma_meta_attributes_progress(b, p, list, true, need_pragma, charset);
            lemma_meta_attributes_progress(b, p, list, got_pragma, need_pragma, charset);
            match extract_character_encoding_from_meta(value) {
                Some(e) => {
                    lemma_meta_attributes_progress(
                        b,
                        p,
                        list,
                        got_pragma,
                        Some(true),
                        Some(Some(e)),
                    );
                },
                None => {},
            }
            lemma_meta_attributes_progress(
                b,
                p,
                list,
                got_pragma,
                Some(false),
                Some(clazel_encoding::labels::spec::get_an_encoding(as_code_points(value))),
            );
        },
        _ => {},
    }
}

/// The position in a result of get an attribute, if it has one, is at
/// least `p` and at most `len`; and the result is out of bytes unless `p`
/// is below `len` (the byte at `p` was read).
pub open spec fn attribute_position_within(r: GetAttribute, p: nat, len: nat) -> bool {
    match r {
        GetAttribute::OutOfBytes => true,
        GetAttribute::NoAttribute { position } => p <= position < len,
        GetAttribute::Attribute { name: _, value: _, position } => p <= position <= len && p < len,
    }
}

/// Get an attribute leaves the pointer no earlier than it found it, and
/// strictly later when it sniffs an attribute; it reads the byte at
/// `position` unless it runs out of bytes.
pub proof fn lemma_get_an_attribute_progress(b: Seq<u8>, position: nat)
    ensures
        attribute_position_within(get_an_attribute(b, position), position, b.len()),
        match get_an_attribute(b, position) {
            GetAttribute::Attribute { name: _, value: _, position: p } => p > position,
            _ => true,
        },
    decreases b.len() - position,
{
    if position < b.len() {
        let c = b[position as int];
        if is_space(c) || c == 0x2F {
            lemma_get_an_attribute_progress(b, position + 1);
        } else if c != 0x3E {
            // The first byte of the name is none of 0x3D-with-a-name,
            // spaces, 0x2F or 0x3E, so it is appended and the pointer
            // advances.
            lemma_attribute_name_step_progress(
                b,
                position + 1,
                Seq::<u8>::empty().push(lowered(c)),
            );
        }
    }
}

/// Steps 4 and 5 leave the pointer no earlier than they found it.
pub proof fn lemma_attribute_name_step_progress(b: Seq<u8>, position: nat, attribute_name: Seq<u8>)
    ensures
        attribute_position_within(
            attribute_name_step(b, position, attribute_name),
            position,
            b.len(),
        ),
    decreases b.len() - position,
{
    if position < b.len() {
        let c = b[position as int];
        lemma_value_step_progress(b, position + 1, attribute_name);
        lemma_spaces_step_progress(b, position, attribute_name);
        lemma_attribute_name_step_progress(b, position + 1, attribute_name.push(lowered(c)));
    }
}

/// Steps 6 to 8 leave the pointer no earlier than they found it.
pub proof fn lemma_spaces_step_progress(b: Seq<u8>, position: nat, attribute_name: Seq<u8>)
    ensures
        attribute_position_within(spaces_step(b, position, attribute_name), position, b.len()),
    decreases b.len() - position,
{
    if position < b.len() {
        lemma_spaces_step_progress(b, position + 1, attribute_name);
        lemma_value_step_progress(b, position + 1, attribute_name);
    }
}

/// Steps 9 and 10 leave the pointer no earlier than they found it.
pub proof fn lemma_value_step_progress(b: Seq<u8>, position: nat, attribute_name: Seq<u8>)
    ensures
        attribute_position_within(value_step(b, position, attribute_name), position, b.len()),
    decreases b.len() - position,
{
    if position < b.len() {
        let c = b[position as int];
        lemma_value_step_progress(b, position + 1, attribute_name);
        lemma_quote_loop_progress(b, c, position, attribute_name, Seq::empty());
        lemma_unquoted_value_step_progress(b, position + 1, attribute_name, seq![lowered(c)]);
    }
}

/// The quote loop leaves the pointer after where it found it.
pub proof fn lemma_quote_loop_progress(
    b: Seq<u8>,
    quote: u8,
    position: nat,
    attribute_name: Seq<u8>,
    attribute_value: Seq<u8>,
)
    ensures
        attribute_position_within(
            quote_loop(b, quote, position, attribute_name, attribute_value),
            position,
            b.len(),
        ),
    decreases b.len() - position,
{
    let next = position + 1;
    if next < b.len() {
        lemma_quote_loop_progress(
            b,
            quote,
            next,
            attribute_name,
            attribute_value.push(lowered(b[next as int])),
        );
    }
}

/// Steps 11 and 12 leave the pointer no earlier than they found it.
pub proof fn lemma_unquoted_value_step_progress(
    b: Seq<u8>,
    position: nat,
    attribute_name: Seq<u8>,
    attribute_value: Seq<u8>,
)
    ensures
        attribute_position_within(
            unquoted_value_step(b, position, attribute_name, attribute_value),
            position,
            b.len(),
        ),
    decreases b.len() - position,
{
    if position < b.len() {
        let c = b[position as int];
        lemma_unquoted_value_step_progress(
            b,
            position + 1,
            attribute_name,
            attribute_value.push(lowered(c)),
        );
    }
}

/// [`find_charset`] finds no earlier than it starts, with room for the
/// seven characters.
pub proof fn lemma_find_charset_progress(s: Seq<u8>, i: nat)
    ensures
        match find_charset(s, i) {
            Some(k) => k >= i && k + 7 <= s.len(),
            None => true,
        },
    decreases s.len() - i,
{
    if i + 7 <= s.len() {
        lemma_find_charset_progress(s, i + 1);
    }
}

/// [`skip_whitespace`] stops no earlier than it starts, and within `s` if
/// it starts there.
pub proof fn lemma_skip_whitespace_progress(s: Seq<u8>, i: nat)
    ensures
        skip_whitespace(s, i) >= i,
        i <= s.len() ==> skip_whitespace(s, i) <= s.len(),
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_skip_whitespace_progress(s, i + 1);
    }
}

} // verus!
