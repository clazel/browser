//! Tag names the tree construction rules name (HTML §13.2.4.2's element
//! categories and every tag name quoted in §13.2.6), as an enum, and the
//! classification of a name. A rule such as "a start tag whose tag name is
//! one of: "b", "big", …" matches on [`Tag`]; the element's or token's name
//! itself is kept as well (`Elem::name`, `TagTok::name`), and "the same tag
//! name" compares the names.
//!
//! Modelling choice (listed in [`super`]): the enum is a cache of the name,
//! `tag_of(name)`, computed once per token and stored with each open
//! element; it changes nothing, since an element's local name never changes.
//! The SVG element `foreignObject` (HTML §13.2.6.5's tag name adjustment of
//! "foreignobject") classifies as [`Tag::Foreignobject`] under both
//! spellings.
//!
//! This file was written from the list of names; each arm compares the
//! name with its code points, spelled out in the comment.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A tag name the tree construction rules mention, or [`Tag::Other`].
pub enum Tag {
    /// "a"
    A,
    /// "address"
    Address,
    /// "annotation-xml"
    AnnotationXml,
    /// "applet"
    Applet,
    /// "area"
    Area,
    /// "article"
    Article,
    /// "aside"
    Aside,
    /// "b"
    B,
    /// "base"
    Base,
    /// "basefont"
    Basefont,
    /// "bgsound"
    Bgsound,
    /// "big"
    Big,
    /// "blockquote"
    Blockquote,
    /// "body"
    Body,
    /// "br"
    Br,
    /// "button"
    Button,
    /// "caption"
    Caption,
    /// "center"
    Center,
    /// "code"
    Code,
    /// "col"
    Col,
    /// "colgroup"
    Colgroup,
    /// "dd"
    Dd,
    /// "desc"
    Desc,
    /// "details"
    Details,
    /// "dialog"
    Dialog,
    /// "dir"
    Dir,
    /// "div"
    Div,
    /// "dl"
    Dl,
    /// "dt"
    Dt,
    /// "em"
    Em,
    /// "embed"
    Embed,
    /// "fieldset"
    Fieldset,
    /// "figcaption"
    Figcaption,
    /// "figure"
    Figure,
    /// "font"
    Font,
    /// "footer"
    Footer,
    /// "foreignobject" (SVG "foreignObject")
    Foreignobject,
    /// "form"
    Form,
    /// "frame"
    Frame,
    /// "frameset"
    Frameset,
    /// "h1"
    H1,
    /// "h2"
    H2,
    /// "h3"
    H3,
    /// "h4"
    H4,
    /// "h5"
    H5,
    /// "h6"
    H6,
    /// "head"
    Head,
    /// "header"
    Header,
    /// "hgroup"
    Hgroup,
    /// "hr"
    Hr,
    /// "html"
    Html,
    /// "i"
    I,
    /// "iframe"
    Iframe,
    /// "image"
    Image,
    /// "img"
    Img,
    /// "input"
    Input,
    /// "keygen"
    Keygen,
    /// "li"
    Li,
    /// "link"
    Link,
    /// "listing"
    Listing,
    /// "main"
    Main,
    /// "malignmark"
    Malignmark,
    /// "marquee"
    Marquee,
    /// "math"
    Math,
    /// "menu"
    Menu,
    /// "meta"
    Meta,
    /// "mglyph"
    Mglyph,
    /// "mi"
    Mi,
    /// "mn"
    Mn,
    /// "mo"
    Mo,
    /// "ms"
    Ms,
    /// "mtext"
    Mtext,
    /// "nav"
    Nav,
    /// "nobr"
    Nobr,
    /// "noembed"
    Noembed,
    /// "noframes"
    Noframes,
    /// "noscript"
    Noscript,
    /// "object"
    Object,
    /// "ol"
    Ol,
    /// "optgroup"
    Optgroup,
    /// "option"
    Option,
    /// "output"
    Output,
    /// "p"
    P,
    /// "param"
    Param,
    /// "plaintext"
    Plaintext,
    /// "pre"
    Pre,
    /// "rb"
    Rb,
    /// "rp"
    Rp,
    /// "rt"
    Rt,
    /// "rtc"
    Rtc,
    /// "ruby"
    Ruby,
    /// "s"
    S,
    /// "script"
    Script,
    /// "search"
    Search,
    /// "section"
    Section,
    /// "select"
    Select,
    /// "small"
    Small,
    /// "source"
    Source,
    /// "span"
    Span,
    /// "strike"
    Strike,
    /// "strong"
    Strong,
    /// "style"
    Style,
    /// "sub"
    Sub,
    /// "summary"
    Summary,
    /// "sup"
    Sup,
    /// "svg"
    Svg,
    /// "table"
    Table,
    /// "tbody"
    Tbody,
    /// "td"
    Td,
    /// "template"
    Template,
    /// "textarea"
    Textarea,
    /// "tfoot"
    Tfoot,
    /// "th"
    Th,
    /// "thead"
    Thead,
    /// "title"
    Title,
    /// "tr"
    Tr,
    /// "track"
    Track,
    /// "tt"
    Tt,
    /// "u"
    U,
    /// "ul"
    Ul,
    /// "var"
    Var,
    /// "wbr"
    Wbr,
    /// "xmp"
    Xmp,
    /// Any other name.
    Other,
}

/// The [`Tag`] of a name (its exact code points; the tokenizer lowercases
/// HTML tag names, and the foreign content rules adjust SVG ones).
pub open spec fn tag_of(name: Seq<u32>) -> Tag {
    if name == seq![0x61u32] {
        // "a"
        Tag::A
    } else if name == seq![0x61u32, 0x64u32, 0x64u32, 0x72u32, 0x65u32, 0x73u32, 0x73u32] {
        // "address"
        Tag::Address
    } else if name == seq![0x61u32, 0x6eu32, 0x6eu32, 0x6fu32, 0x74u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32, 0x2du32, 0x78u32, 0x6du32, 0x6cu32] {
        // "annotation-xml"
        Tag::AnnotationXml
    } else if name == seq![0x61u32, 0x70u32, 0x70u32, 0x6cu32, 0x65u32, 0x74u32] {
        // "applet"
        Tag::Applet
    } else if name == seq![0x61u32, 0x72u32, 0x65u32, 0x61u32] {
        // "area"
        Tag::Area
    } else if name == seq![0x61u32, 0x72u32, 0x74u32, 0x69u32, 0x63u32, 0x6cu32, 0x65u32] {
        // "article"
        Tag::Article
    } else if name == seq![0x61u32, 0x73u32, 0x69u32, 0x64u32, 0x65u32] {
        // "aside"
        Tag::Aside
    } else if name == seq![0x62u32] {
        // "b"
        Tag::B
    } else if name == seq![0x62u32, 0x61u32, 0x73u32, 0x65u32] {
        // "base"
        Tag::Base
    } else if name == seq![0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x66u32, 0x6fu32, 0x6eu32, 0x74u32] {
        // "basefont"
        Tag::Basefont
    } else if name == seq![0x62u32, 0x67u32, 0x73u32, 0x6fu32, 0x75u32, 0x6eu32, 0x64u32] {
        // "bgsound"
        Tag::Bgsound
    } else if name == seq![0x62u32, 0x69u32, 0x67u32] {
        // "big"
        Tag::Big
    } else if name == seq![0x62u32, 0x6cu32, 0x6fu32, 0x63u32, 0x6bu32, 0x71u32, 0x75u32, 0x6fu32, 0x74u32, 0x65u32] {
        // "blockquote"
        Tag::Blockquote
    } else if name == seq![0x62u32, 0x6fu32, 0x64u32, 0x79u32] {
        // "body"
        Tag::Body
    } else if name == seq![0x62u32, 0x72u32] {
        // "br"
        Tag::Br
    } else if name == seq![0x62u32, 0x75u32, 0x74u32, 0x74u32, 0x6fu32, 0x6eu32] {
        // "button"
        Tag::Button
    } else if name == seq![0x63u32, 0x61u32, 0x70u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32] {
        // "caption"
        Tag::Caption
    } else if name == seq![0x63u32, 0x65u32, 0x6eu32, 0x74u32, 0x65u32, 0x72u32] {
        // "center"
        Tag::Center
    } else if name == seq![0x63u32, 0x6fu32, 0x64u32, 0x65u32] {
        // "code"
        Tag::Code
    } else if name == seq![0x63u32, 0x6fu32, 0x6cu32] {
        // "col"
        Tag::Col
    } else if name == seq![0x63u32, 0x6fu32, 0x6cu32, 0x67u32, 0x72u32, 0x6fu32, 0x75u32, 0x70u32] {
        // "colgroup"
        Tag::Colgroup
    } else if name == seq![0x64u32, 0x64u32] {
        // "dd"
        Tag::Dd
    } else if name == seq![0x64u32, 0x65u32, 0x73u32, 0x63u32] {
        // "desc"
        Tag::Desc
    } else if name == seq![0x64u32, 0x65u32, 0x74u32, 0x61u32, 0x69u32, 0x6cu32, 0x73u32] {
        // "details"
        Tag::Details
    } else if name == seq![0x64u32, 0x69u32, 0x61u32, 0x6cu32, 0x6fu32, 0x67u32] {
        // "dialog"
        Tag::Dialog
    } else if name == seq![0x64u32, 0x69u32, 0x72u32] {
        // "dir"
        Tag::Dir
    } else if name == seq![0x64u32, 0x69u32, 0x76u32] {
        // "div"
        Tag::Div
    } else if name == seq![0x64u32, 0x6cu32] {
        // "dl"
        Tag::Dl
    } else if name == seq![0x64u32, 0x74u32] {
        // "dt"
        Tag::Dt
    } else if name == seq![0x65u32, 0x6du32] {
        // "em"
        Tag::Em
    } else if name == seq![0x65u32, 0x6du32, 0x62u32, 0x65u32, 0x64u32] {
        // "embed"
        Tag::Embed
    } else if name == seq![0x66u32, 0x69u32, 0x65u32, 0x6cu32, 0x64u32, 0x73u32, 0x65u32, 0x74u32] {
        // "fieldset"
        Tag::Fieldset
    } else if name == seq![0x66u32, 0x69u32, 0x67u32, 0x63u32, 0x61u32, 0x70u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32] {
        // "figcaption"
        Tag::Figcaption
    } else if name == seq![0x66u32, 0x69u32, 0x67u32, 0x75u32, 0x72u32, 0x65u32] {
        // "figure"
        Tag::Figure
    } else if name == seq![0x66u32, 0x6fu32, 0x6eu32, 0x74u32] {
        // "font"
        Tag::Font
    } else if name == seq![0x66u32, 0x6fu32, 0x6fu32, 0x74u32, 0x65u32, 0x72u32] {
        // "footer"
        Tag::Footer
    } else if name == seq![0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x6fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32] {
        // "foreignobject"
        Tag::Foreignobject
    } else if name == seq![0x66u32, 0x6fu32, 0x72u32, 0x6du32] {
        // "form"
        Tag::Form
    } else if name == seq![0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32] {
        // "frame"
        Tag::Frame
    } else if name == seq![0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32, 0x73u32, 0x65u32, 0x74u32] {
        // "frameset"
        Tag::Frameset
    } else if name == seq![0x68u32, 0x31u32] {
        // "h1"
        Tag::H1
    } else if name == seq![0x68u32, 0x32u32] {
        // "h2"
        Tag::H2
    } else if name == seq![0x68u32, 0x33u32] {
        // "h3"
        Tag::H3
    } else if name == seq![0x68u32, 0x34u32] {
        // "h4"
        Tag::H4
    } else if name == seq![0x68u32, 0x35u32] {
        // "h5"
        Tag::H5
    } else if name == seq![0x68u32, 0x36u32] {
        // "h6"
        Tag::H6
    } else if name == seq![0x68u32, 0x65u32, 0x61u32, 0x64u32] {
        // "head"
        Tag::Head
    } else if name == seq![0x68u32, 0x65u32, 0x61u32, 0x64u32, 0x65u32, 0x72u32] {
        // "header"
        Tag::Header
    } else if name == seq![0x68u32, 0x67u32, 0x72u32, 0x6fu32, 0x75u32, 0x70u32] {
        // "hgroup"
        Tag::Hgroup
    } else if name == seq![0x68u32, 0x72u32] {
        // "hr"
        Tag::Hr
    } else if name == seq![0x68u32, 0x74u32, 0x6du32, 0x6cu32] {
        // "html"
        Tag::Html
    } else if name == seq![0x69u32] {
        // "i"
        Tag::I
    } else if name == seq![0x69u32, 0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32] {
        // "iframe"
        Tag::Iframe
    } else if name == seq![0x69u32, 0x6du32, 0x61u32, 0x67u32, 0x65u32] {
        // "image"
        Tag::Image
    } else if name == seq![0x69u32, 0x6du32, 0x67u32] {
        // "img"
        Tag::Img
    } else if name == seq![0x69u32, 0x6eu32, 0x70u32, 0x75u32, 0x74u32] {
        // "input"
        Tag::Input
    } else if name == seq![0x6bu32, 0x65u32, 0x79u32, 0x67u32, 0x65u32, 0x6eu32] {
        // "keygen"
        Tag::Keygen
    } else if name == seq![0x6cu32, 0x69u32] {
        // "li"
        Tag::Li
    } else if name == seq![0x6cu32, 0x69u32, 0x6eu32, 0x6bu32] {
        // "link"
        Tag::Link
    } else if name == seq![0x6cu32, 0x69u32, 0x73u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32] {
        // "listing"
        Tag::Listing
    } else if name == seq![0x6du32, 0x61u32, 0x69u32, 0x6eu32] {
        // "main"
        Tag::Main
    } else if name == seq![0x6du32, 0x61u32, 0x6cu32, 0x69u32, 0x67u32, 0x6eu32, 0x6du32, 0x61u32, 0x72u32, 0x6bu32] {
        // "malignmark"
        Tag::Malignmark
    } else if name == seq![0x6du32, 0x61u32, 0x72u32, 0x71u32, 0x75u32, 0x65u32, 0x65u32] {
        // "marquee"
        Tag::Marquee
    } else if name == seq![0x6du32, 0x61u32, 0x74u32, 0x68u32] {
        // "math"
        Tag::Math
    } else if name == seq![0x6du32, 0x65u32, 0x6eu32, 0x75u32] {
        // "menu"
        Tag::Menu
    } else if name == seq![0x6du32, 0x65u32, 0x74u32, 0x61u32] {
        // "meta"
        Tag::Meta
    } else if name == seq![0x6du32, 0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32] {
        // "mglyph"
        Tag::Mglyph
    } else if name == seq![0x6du32, 0x69u32] {
        // "mi"
        Tag::Mi
    } else if name == seq![0x6du32, 0x6eu32] {
        // "mn"
        Tag::Mn
    } else if name == seq![0x6du32, 0x6fu32] {
        // "mo"
        Tag::Mo
    } else if name == seq![0x6du32, 0x73u32] {
        // "ms"
        Tag::Ms
    } else if name == seq![0x6du32, 0x74u32, 0x65u32, 0x78u32, 0x74u32] {
        // "mtext"
        Tag::Mtext
    } else if name == seq![0x6eu32, 0x61u32, 0x76u32] {
        // "nav"
        Tag::Nav
    } else if name == seq![0x6eu32, 0x6fu32, 0x62u32, 0x72u32] {
        // "nobr"
        Tag::Nobr
    } else if name == seq![0x6eu32, 0x6fu32, 0x65u32, 0x6du32, 0x62u32, 0x65u32, 0x64u32] {
        // "noembed"
        Tag::Noembed
    } else if name == seq![0x6eu32, 0x6fu32, 0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32, 0x73u32] {
        // "noframes"
        Tag::Noframes
    } else if name == seq![0x6eu32, 0x6fu32, 0x73u32, 0x63u32, 0x72u32, 0x69u32, 0x70u32, 0x74u32] {
        // "noscript"
        Tag::Noscript
    } else if name == seq![0x6fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32] {
        // "object"
        Tag::Object
    } else if name == seq![0x6fu32, 0x6cu32] {
        // "ol"
        Tag::Ol
    } else if name == seq![0x6fu32, 0x70u32, 0x74u32, 0x67u32, 0x72u32, 0x6fu32, 0x75u32, 0x70u32] {
        // "optgroup"
        Tag::Optgroup
    } else if name == seq![0x6fu32, 0x70u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32] {
        // "option"
        Tag::Option
    } else if name == seq![0x6fu32, 0x75u32, 0x74u32, 0x70u32, 0x75u32, 0x74u32] {
        // "output"
        Tag::Output
    } else if name == seq![0x70u32] {
        // "p"
        Tag::P
    } else if name == seq![0x70u32, 0x61u32, 0x72u32, 0x61u32, 0x6du32] {
        // "param"
        Tag::Param
    } else if name == seq![0x70u32, 0x6cu32, 0x61u32, 0x69u32, 0x6eu32, 0x74u32, 0x65u32, 0x78u32, 0x74u32] {
        // "plaintext"
        Tag::Plaintext
    } else if name == seq![0x70u32, 0x72u32, 0x65u32] {
        // "pre"
        Tag::Pre
    } else if name == seq![0x72u32, 0x62u32] {
        // "rb"
        Tag::Rb
    } else if name == seq![0x72u32, 0x70u32] {
        // "rp"
        Tag::Rp
    } else if name == seq![0x72u32, 0x74u32] {
        // "rt"
        Tag::Rt
    } else if name == seq![0x72u32, 0x74u32, 0x63u32] {
        // "rtc"
        Tag::Rtc
    } else if name == seq![0x72u32, 0x75u32, 0x62u32, 0x79u32] {
        // "ruby"
        Tag::Ruby
    } else if name == seq![0x73u32] {
        // "s"
        Tag::S
    } else if name == seq![0x73u32, 0x63u32, 0x72u32, 0x69u32, 0x70u32, 0x74u32] {
        // "script"
        Tag::Script
    } else if name == seq![0x73u32, 0x65u32, 0x61u32, 0x72u32, 0x63u32, 0x68u32] {
        // "search"
        Tag::Search
    } else if name == seq![0x73u32, 0x65u32, 0x63u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32] {
        // "section"
        Tag::Section
    } else if name == seq![0x73u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32] {
        // "select"
        Tag::Select
    } else if name == seq![0x73u32, 0x6du32, 0x61u32, 0x6cu32, 0x6cu32] {
        // "small"
        Tag::Small
    } else if name == seq![0x73u32, 0x6fu32, 0x75u32, 0x72u32, 0x63u32, 0x65u32] {
        // "source"
        Tag::Source
    } else if name == seq![0x73u32, 0x70u32, 0x61u32, 0x6eu32] {
        // "span"
        Tag::Span
    } else if name == seq![0x73u32, 0x74u32, 0x72u32, 0x69u32, 0x6bu32, 0x65u32] {
        // "strike"
        Tag::Strike
    } else if name == seq![0x73u32, 0x74u32, 0x72u32, 0x6fu32, 0x6eu32, 0x67u32] {
        // "strong"
        Tag::Strong
    } else if name == seq![0x73u32, 0x74u32, 0x79u32, 0x6cu32, 0x65u32] {
        // "style"
        Tag::Style
    } else if name == seq![0x73u32, 0x75u32, 0x62u32] {
        // "sub"
        Tag::Sub
    } else if name == seq![0x73u32, 0x75u32, 0x6du32, 0x6du32, 0x61u32, 0x72u32, 0x79u32] {
        // "summary"
        Tag::Summary
    } else if name == seq![0x73u32, 0x75u32, 0x70u32] {
        // "sup"
        Tag::Sup
    } else if name == seq![0x73u32, 0x76u32, 0x67u32] {
        // "svg"
        Tag::Svg
    } else if name == seq![0x74u32, 0x61u32, 0x62u32, 0x6cu32, 0x65u32] {
        // "table"
        Tag::Table
    } else if name == seq![0x74u32, 0x62u32, 0x6fu32, 0x64u32, 0x79u32] {
        // "tbody"
        Tag::Tbody
    } else if name == seq![0x74u32, 0x64u32] {
        // "td"
        Tag::Td
    } else if name == seq![0x74u32, 0x65u32, 0x6du32, 0x70u32, 0x6cu32, 0x61u32, 0x74u32, 0x65u32] {
        // "template"
        Tag::Template
    } else if name == seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x61u32, 0x72u32, 0x65u32, 0x61u32] {
        // "textarea"
        Tag::Textarea
    } else if name == seq![0x74u32, 0x66u32, 0x6fu32, 0x6fu32, 0x74u32] {
        // "tfoot"
        Tag::Tfoot
    } else if name == seq![0x74u32, 0x68u32] {
        // "th"
        Tag::Th
    } else if name == seq![0x74u32, 0x68u32, 0x65u32, 0x61u32, 0x64u32] {
        // "thead"
        Tag::Thead
    } else if name == seq![0x74u32, 0x69u32, 0x74u32, 0x6cu32, 0x65u32] {
        // "title"
        Tag::Title
    } else if name == seq![0x74u32, 0x72u32] {
        // "tr"
        Tag::Tr
    } else if name == seq![0x74u32, 0x72u32, 0x61u32, 0x63u32, 0x6bu32] {
        // "track"
        Tag::Track
    } else if name == seq![0x74u32, 0x74u32] {
        // "tt"
        Tag::Tt
    } else if name == seq![0x75u32] {
        // "u"
        Tag::U
    } else if name == seq![0x75u32, 0x6cu32] {
        // "ul"
        Tag::Ul
    } else if name == seq![0x76u32, 0x61u32, 0x72u32] {
        // "var"
        Tag::Var
    } else if name == seq![0x77u32, 0x62u32, 0x72u32] {
        // "wbr"
        Tag::Wbr
    } else if name == seq![0x78u32, 0x6du32, 0x70u32] {
        // "xmp"
        Tag::Xmp
    } else if name == seq![0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x4fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32] {
        // "foreignObject"
        Tag::Foreignobject
    } else {
        Tag::Other
    }
}

} // verus!
