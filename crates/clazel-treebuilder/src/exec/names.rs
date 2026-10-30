//! Generated from `spec/base/tags.rs` and `spec/base/tables.rs` (one arm
//! per arm of the spec, in its order): the exec classification of a tag
//! name, the copy and equality of [`Tag`], and the adjustment tables.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Whether `a` equals `b` (code points).
pub fn u32s_eq(a: &[u32], b: &[u32]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => {
                if *x != *y {
                    return false;
                }
            },
            _ => return false,
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// A number for each [`Tag`], in declaration order.
pub open spec fn tag_code(t: Tag) -> u8 {
    match t {
        Tag::A => 0,
        Tag::Address => 1,
        Tag::AnnotationXml => 2,
        Tag::Applet => 3,
        Tag::Area => 4,
        Tag::Article => 5,
        Tag::Aside => 6,
        Tag::B => 7,
        Tag::Base => 8,
        Tag::Basefont => 9,
        Tag::Bgsound => 10,
        Tag::Big => 11,
        Tag::Blockquote => 12,
        Tag::Body => 13,
        Tag::Br => 14,
        Tag::Button => 15,
        Tag::Caption => 16,
        Tag::Center => 17,
        Tag::Code => 18,
        Tag::Col => 19,
        Tag::Colgroup => 20,
        Tag::Dd => 21,
        Tag::Desc => 22,
        Tag::Details => 23,
        Tag::Dialog => 24,
        Tag::Dir => 25,
        Tag::Div => 26,
        Tag::Dl => 27,
        Tag::Dt => 28,
        Tag::Em => 29,
        Tag::Embed => 30,
        Tag::Fieldset => 31,
        Tag::Figcaption => 32,
        Tag::Figure => 33,
        Tag::Font => 34,
        Tag::Footer => 35,
        Tag::Foreignobject => 36,
        Tag::Form => 37,
        Tag::Frame => 38,
        Tag::Frameset => 39,
        Tag::H1 => 40,
        Tag::H2 => 41,
        Tag::H3 => 42,
        Tag::H4 => 43,
        Tag::H5 => 44,
        Tag::H6 => 45,
        Tag::Head => 46,
        Tag::Header => 47,
        Tag::Hgroup => 48,
        Tag::Hr => 49,
        Tag::Html => 50,
        Tag::I => 51,
        Tag::Iframe => 52,
        Tag::Image => 53,
        Tag::Img => 54,
        Tag::Input => 55,
        Tag::Keygen => 56,
        Tag::Li => 57,
        Tag::Link => 58,
        Tag::Listing => 59,
        Tag::Main => 60,
        Tag::Malignmark => 61,
        Tag::Marquee => 62,
        Tag::Math => 63,
        Tag::Menu => 64,
        Tag::Meta => 65,
        Tag::Mglyph => 66,
        Tag::Mi => 67,
        Tag::Mn => 68,
        Tag::Mo => 69,
        Tag::Ms => 70,
        Tag::Mtext => 71,
        Tag::Nav => 72,
        Tag::Nobr => 73,
        Tag::Noembed => 74,
        Tag::Noframes => 75,
        Tag::Noscript => 76,
        Tag::Object => 77,
        Tag::Ol => 78,
        Tag::Optgroup => 79,
        Tag::Option => 80,
        Tag::Output => 81,
        Tag::P => 82,
        Tag::Param => 83,
        Tag::Plaintext => 84,
        Tag::Pre => 85,
        Tag::Rb => 86,
        Tag::Rp => 87,
        Tag::Rt => 88,
        Tag::Rtc => 89,
        Tag::Ruby => 90,
        Tag::S => 91,
        Tag::Script => 92,
        Tag::Search => 93,
        Tag::Section => 94,
        Tag::Select => 95,
        Tag::Small => 96,
        Tag::Source => 97,
        Tag::Span => 98,
        Tag::Strike => 99,
        Tag::Strong => 100,
        Tag::Style => 101,
        Tag::Sub => 102,
        Tag::Summary => 103,
        Tag::Sup => 104,
        Tag::Svg => 105,
        Tag::Table => 106,
        Tag::Tbody => 107,
        Tag::Td => 108,
        Tag::Template => 109,
        Tag::Textarea => 110,
        Tag::Tfoot => 111,
        Tag::Th => 112,
        Tag::Thead => 113,
        Tag::Title => 114,
        Tag::Tr => 115,
        Tag::Track => 116,
        Tag::Tt => 117,
        Tag::U => 118,
        Tag::Ul => 119,
        Tag::Var => 120,
        Tag::Wbr => 121,
        Tag::Xmp => 122,
        Tag::Other => 123,
    }
}

/// The [`Tag`] of a [`tag_code`].
pub open spec fn tag_of_code(c: u8) -> Tag {
    if c == 0 {
        Tag::A
    } else if c == 1 {
        Tag::Address
    } else if c == 2 {
        Tag::AnnotationXml
    } else if c == 3 {
        Tag::Applet
    } else if c == 4 {
        Tag::Area
    } else if c == 5 {
        Tag::Article
    } else if c == 6 {
        Tag::Aside
    } else if c == 7 {
        Tag::B
    } else if c == 8 {
        Tag::Base
    } else if c == 9 {
        Tag::Basefont
    } else if c == 10 {
        Tag::Bgsound
    } else if c == 11 {
        Tag::Big
    } else if c == 12 {
        Tag::Blockquote
    } else if c == 13 {
        Tag::Body
    } else if c == 14 {
        Tag::Br
    } else if c == 15 {
        Tag::Button
    } else if c == 16 {
        Tag::Caption
    } else if c == 17 {
        Tag::Center
    } else if c == 18 {
        Tag::Code
    } else if c == 19 {
        Tag::Col
    } else if c == 20 {
        Tag::Colgroup
    } else if c == 21 {
        Tag::Dd
    } else if c == 22 {
        Tag::Desc
    } else if c == 23 {
        Tag::Details
    } else if c == 24 {
        Tag::Dialog
    } else if c == 25 {
        Tag::Dir
    } else if c == 26 {
        Tag::Div
    } else if c == 27 {
        Tag::Dl
    } else if c == 28 {
        Tag::Dt
    } else if c == 29 {
        Tag::Em
    } else if c == 30 {
        Tag::Embed
    } else if c == 31 {
        Tag::Fieldset
    } else if c == 32 {
        Tag::Figcaption
    } else if c == 33 {
        Tag::Figure
    } else if c == 34 {
        Tag::Font
    } else if c == 35 {
        Tag::Footer
    } else if c == 36 {
        Tag::Foreignobject
    } else if c == 37 {
        Tag::Form
    } else if c == 38 {
        Tag::Frame
    } else if c == 39 {
        Tag::Frameset
    } else if c == 40 {
        Tag::H1
    } else if c == 41 {
        Tag::H2
    } else if c == 42 {
        Tag::H3
    } else if c == 43 {
        Tag::H4
    } else if c == 44 {
        Tag::H5
    } else if c == 45 {
        Tag::H6
    } else if c == 46 {
        Tag::Head
    } else if c == 47 {
        Tag::Header
    } else if c == 48 {
        Tag::Hgroup
    } else if c == 49 {
        Tag::Hr
    } else if c == 50 {
        Tag::Html
    } else if c == 51 {
        Tag::I
    } else if c == 52 {
        Tag::Iframe
    } else if c == 53 {
        Tag::Image
    } else if c == 54 {
        Tag::Img
    } else if c == 55 {
        Tag::Input
    } else if c == 56 {
        Tag::Keygen
    } else if c == 57 {
        Tag::Li
    } else if c == 58 {
        Tag::Link
    } else if c == 59 {
        Tag::Listing
    } else if c == 60 {
        Tag::Main
    } else if c == 61 {
        Tag::Malignmark
    } else if c == 62 {
        Tag::Marquee
    } else if c == 63 {
        Tag::Math
    } else if c == 64 {
        Tag::Menu
    } else if c == 65 {
        Tag::Meta
    } else if c == 66 {
        Tag::Mglyph
    } else if c == 67 {
        Tag::Mi
    } else if c == 68 {
        Tag::Mn
    } else if c == 69 {
        Tag::Mo
    } else if c == 70 {
        Tag::Ms
    } else if c == 71 {
        Tag::Mtext
    } else if c == 72 {
        Tag::Nav
    } else if c == 73 {
        Tag::Nobr
    } else if c == 74 {
        Tag::Noembed
    } else if c == 75 {
        Tag::Noframes
    } else if c == 76 {
        Tag::Noscript
    } else if c == 77 {
        Tag::Object
    } else if c == 78 {
        Tag::Ol
    } else if c == 79 {
        Tag::Optgroup
    } else if c == 80 {
        Tag::Option
    } else if c == 81 {
        Tag::Output
    } else if c == 82 {
        Tag::P
    } else if c == 83 {
        Tag::Param
    } else if c == 84 {
        Tag::Plaintext
    } else if c == 85 {
        Tag::Pre
    } else if c == 86 {
        Tag::Rb
    } else if c == 87 {
        Tag::Rp
    } else if c == 88 {
        Tag::Rt
    } else if c == 89 {
        Tag::Rtc
    } else if c == 90 {
        Tag::Ruby
    } else if c == 91 {
        Tag::S
    } else if c == 92 {
        Tag::Script
    } else if c == 93 {
        Tag::Search
    } else if c == 94 {
        Tag::Section
    } else if c == 95 {
        Tag::Select
    } else if c == 96 {
        Tag::Small
    } else if c == 97 {
        Tag::Source
    } else if c == 98 {
        Tag::Span
    } else if c == 99 {
        Tag::Strike
    } else if c == 100 {
        Tag::Strong
    } else if c == 101 {
        Tag::Style
    } else if c == 102 {
        Tag::Sub
    } else if c == 103 {
        Tag::Summary
    } else if c == 104 {
        Tag::Sup
    } else if c == 105 {
        Tag::Svg
    } else if c == 106 {
        Tag::Table
    } else if c == 107 {
        Tag::Tbody
    } else if c == 108 {
        Tag::Td
    } else if c == 109 {
        Tag::Template
    } else if c == 110 {
        Tag::Textarea
    } else if c == 111 {
        Tag::Tfoot
    } else if c == 112 {
        Tag::Th
    } else if c == 113 {
        Tag::Thead
    } else if c == 114 {
        Tag::Title
    } else if c == 115 {
        Tag::Tr
    } else if c == 116 {
        Tag::Track
    } else if c == 117 {
        Tag::Tt
    } else if c == 118 {
        Tag::U
    } else if c == 119 {
        Tag::Ul
    } else if c == 120 {
        Tag::Var
    } else if c == 121 {
        Tag::Wbr
    } else if c == 122 {
        Tag::Xmp
    } else {
        Tag::Other
    }
}

/// [`tag_code`] is injective.
pub proof fn lemma_tag_code(t: Tag)
    ensures
        tag_of_code(tag_code(t)) == t,
{
    match t {
        Tag::A => {},
        Tag::Address => {},
        Tag::AnnotationXml => {},
        Tag::Applet => {},
        Tag::Area => {},
        Tag::Article => {},
        Tag::Aside => {},
        Tag::B => {},
        Tag::Base => {},
        Tag::Basefont => {},
        Tag::Bgsound => {},
        Tag::Big => {},
        Tag::Blockquote => {},
        Tag::Body => {},
        Tag::Br => {},
        Tag::Button => {},
        Tag::Caption => {},
        Tag::Center => {},
        Tag::Code => {},
        Tag::Col => {},
        Tag::Colgroup => {},
        Tag::Dd => {},
        Tag::Desc => {},
        Tag::Details => {},
        Tag::Dialog => {},
        Tag::Dir => {},
        Tag::Div => {},
        Tag::Dl => {},
        Tag::Dt => {},
        Tag::Em => {},
        Tag::Embed => {},
        Tag::Fieldset => {},
        Tag::Figcaption => {},
        Tag::Figure => {},
        Tag::Font => {},
        Tag::Footer => {},
        Tag::Foreignobject => {},
        Tag::Form => {},
        Tag::Frame => {},
        Tag::Frameset => {},
        Tag::H1 => {},
        Tag::H2 => {},
        Tag::H3 => {},
        Tag::H4 => {},
        Tag::H5 => {},
        Tag::H6 => {},
        Tag::Head => {},
        Tag::Header => {},
        Tag::Hgroup => {},
        Tag::Hr => {},
        Tag::Html => {},
        Tag::I => {},
        Tag::Iframe => {},
        Tag::Image => {},
        Tag::Img => {},
        Tag::Input => {},
        Tag::Keygen => {},
        Tag::Li => {},
        Tag::Link => {},
        Tag::Listing => {},
        Tag::Main => {},
        Tag::Malignmark => {},
        Tag::Marquee => {},
        Tag::Math => {},
        Tag::Menu => {},
        Tag::Meta => {},
        Tag::Mglyph => {},
        Tag::Mi => {},
        Tag::Mn => {},
        Tag::Mo => {},
        Tag::Ms => {},
        Tag::Mtext => {},
        Tag::Nav => {},
        Tag::Nobr => {},
        Tag::Noembed => {},
        Tag::Noframes => {},
        Tag::Noscript => {},
        Tag::Object => {},
        Tag::Ol => {},
        Tag::Optgroup => {},
        Tag::Option => {},
        Tag::Output => {},
        Tag::P => {},
        Tag::Param => {},
        Tag::Plaintext => {},
        Tag::Pre => {},
        Tag::Rb => {},
        Tag::Rp => {},
        Tag::Rt => {},
        Tag::Rtc => {},
        Tag::Ruby => {},
        Tag::S => {},
        Tag::Script => {},
        Tag::Search => {},
        Tag::Section => {},
        Tag::Select => {},
        Tag::Small => {},
        Tag::Source => {},
        Tag::Span => {},
        Tag::Strike => {},
        Tag::Strong => {},
        Tag::Style => {},
        Tag::Sub => {},
        Tag::Summary => {},
        Tag::Sup => {},
        Tag::Svg => {},
        Tag::Table => {},
        Tag::Tbody => {},
        Tag::Td => {},
        Tag::Template => {},
        Tag::Textarea => {},
        Tag::Tfoot => {},
        Tag::Th => {},
        Tag::Thead => {},
        Tag::Title => {},
        Tag::Tr => {},
        Tag::Track => {},
        Tag::Tt => {},
        Tag::U => {},
        Tag::Ul => {},
        Tag::Var => {},
        Tag::Wbr => {},
        Tag::Xmp => {},
        Tag::Other => {},
    }
}

/// [`tag_code`].
pub fn tag_code_exec(t: &Tag) -> (r: u8)
    ensures
        r == tag_code(*t),
{
    match t {
        Tag::A => 0,
        Tag::Address => 1,
        Tag::AnnotationXml => 2,
        Tag::Applet => 3,
        Tag::Area => 4,
        Tag::Article => 5,
        Tag::Aside => 6,
        Tag::B => 7,
        Tag::Base => 8,
        Tag::Basefont => 9,
        Tag::Bgsound => 10,
        Tag::Big => 11,
        Tag::Blockquote => 12,
        Tag::Body => 13,
        Tag::Br => 14,
        Tag::Button => 15,
        Tag::Caption => 16,
        Tag::Center => 17,
        Tag::Code => 18,
        Tag::Col => 19,
        Tag::Colgroup => 20,
        Tag::Dd => 21,
        Tag::Desc => 22,
        Tag::Details => 23,
        Tag::Dialog => 24,
        Tag::Dir => 25,
        Tag::Div => 26,
        Tag::Dl => 27,
        Tag::Dt => 28,
        Tag::Em => 29,
        Tag::Embed => 30,
        Tag::Fieldset => 31,
        Tag::Figcaption => 32,
        Tag::Figure => 33,
        Tag::Font => 34,
        Tag::Footer => 35,
        Tag::Foreignobject => 36,
        Tag::Form => 37,
        Tag::Frame => 38,
        Tag::Frameset => 39,
        Tag::H1 => 40,
        Tag::H2 => 41,
        Tag::H3 => 42,
        Tag::H4 => 43,
        Tag::H5 => 44,
        Tag::H6 => 45,
        Tag::Head => 46,
        Tag::Header => 47,
        Tag::Hgroup => 48,
        Tag::Hr => 49,
        Tag::Html => 50,
        Tag::I => 51,
        Tag::Iframe => 52,
        Tag::Image => 53,
        Tag::Img => 54,
        Tag::Input => 55,
        Tag::Keygen => 56,
        Tag::Li => 57,
        Tag::Link => 58,
        Tag::Listing => 59,
        Tag::Main => 60,
        Tag::Malignmark => 61,
        Tag::Marquee => 62,
        Tag::Math => 63,
        Tag::Menu => 64,
        Tag::Meta => 65,
        Tag::Mglyph => 66,
        Tag::Mi => 67,
        Tag::Mn => 68,
        Tag::Mo => 69,
        Tag::Ms => 70,
        Tag::Mtext => 71,
        Tag::Nav => 72,
        Tag::Nobr => 73,
        Tag::Noembed => 74,
        Tag::Noframes => 75,
        Tag::Noscript => 76,
        Tag::Object => 77,
        Tag::Ol => 78,
        Tag::Optgroup => 79,
        Tag::Option => 80,
        Tag::Output => 81,
        Tag::P => 82,
        Tag::Param => 83,
        Tag::Plaintext => 84,
        Tag::Pre => 85,
        Tag::Rb => 86,
        Tag::Rp => 87,
        Tag::Rt => 88,
        Tag::Rtc => 89,
        Tag::Ruby => 90,
        Tag::S => 91,
        Tag::Script => 92,
        Tag::Search => 93,
        Tag::Section => 94,
        Tag::Select => 95,
        Tag::Small => 96,
        Tag::Source => 97,
        Tag::Span => 98,
        Tag::Strike => 99,
        Tag::Strong => 100,
        Tag::Style => 101,
        Tag::Sub => 102,
        Tag::Summary => 103,
        Tag::Sup => 104,
        Tag::Svg => 105,
        Tag::Table => 106,
        Tag::Tbody => 107,
        Tag::Td => 108,
        Tag::Template => 109,
        Tag::Textarea => 110,
        Tag::Tfoot => 111,
        Tag::Th => 112,
        Tag::Thead => 113,
        Tag::Title => 114,
        Tag::Tr => 115,
        Tag::Track => 116,
        Tag::Tt => 117,
        Tag::U => 118,
        Tag::Ul => 119,
        Tag::Var => 120,
        Tag::Wbr => 121,
        Tag::Xmp => 122,
        Tag::Other => 123,
    }
}

/// Whether two tags are equal.
pub fn tag_eq(a: &Tag, b: &Tag) -> (r: bool)
    ensures
        r == (*a == *b),
{
    proof {
        lemma_tag_code(*a);
        lemma_tag_code(*b);
    }
    tag_code_exec(a) == tag_code_exec(b)
}

/// A copy of a tag.
pub fn copy_tag(t: &Tag) -> (r: Tag)
    ensures
        r == *t,
{
    match t {
        Tag::A => Tag::A,
        Tag::Address => Tag::Address,
        Tag::AnnotationXml => Tag::AnnotationXml,
        Tag::Applet => Tag::Applet,
        Tag::Area => Tag::Area,
        Tag::Article => Tag::Article,
        Tag::Aside => Tag::Aside,
        Tag::B => Tag::B,
        Tag::Base => Tag::Base,
        Tag::Basefont => Tag::Basefont,
        Tag::Bgsound => Tag::Bgsound,
        Tag::Big => Tag::Big,
        Tag::Blockquote => Tag::Blockquote,
        Tag::Body => Tag::Body,
        Tag::Br => Tag::Br,
        Tag::Button => Tag::Button,
        Tag::Caption => Tag::Caption,
        Tag::Center => Tag::Center,
        Tag::Code => Tag::Code,
        Tag::Col => Tag::Col,
        Tag::Colgroup => Tag::Colgroup,
        Tag::Dd => Tag::Dd,
        Tag::Desc => Tag::Desc,
        Tag::Details => Tag::Details,
        Tag::Dialog => Tag::Dialog,
        Tag::Dir => Tag::Dir,
        Tag::Div => Tag::Div,
        Tag::Dl => Tag::Dl,
        Tag::Dt => Tag::Dt,
        Tag::Em => Tag::Em,
        Tag::Embed => Tag::Embed,
        Tag::Fieldset => Tag::Fieldset,
        Tag::Figcaption => Tag::Figcaption,
        Tag::Figure => Tag::Figure,
        Tag::Font => Tag::Font,
        Tag::Footer => Tag::Footer,
        Tag::Foreignobject => Tag::Foreignobject,
        Tag::Form => Tag::Form,
        Tag::Frame => Tag::Frame,
        Tag::Frameset => Tag::Frameset,
        Tag::H1 => Tag::H1,
        Tag::H2 => Tag::H2,
        Tag::H3 => Tag::H3,
        Tag::H4 => Tag::H4,
        Tag::H5 => Tag::H5,
        Tag::H6 => Tag::H6,
        Tag::Head => Tag::Head,
        Tag::Header => Tag::Header,
        Tag::Hgroup => Tag::Hgroup,
        Tag::Hr => Tag::Hr,
        Tag::Html => Tag::Html,
        Tag::I => Tag::I,
        Tag::Iframe => Tag::Iframe,
        Tag::Image => Tag::Image,
        Tag::Img => Tag::Img,
        Tag::Input => Tag::Input,
        Tag::Keygen => Tag::Keygen,
        Tag::Li => Tag::Li,
        Tag::Link => Tag::Link,
        Tag::Listing => Tag::Listing,
        Tag::Main => Tag::Main,
        Tag::Malignmark => Tag::Malignmark,
        Tag::Marquee => Tag::Marquee,
        Tag::Math => Tag::Math,
        Tag::Menu => Tag::Menu,
        Tag::Meta => Tag::Meta,
        Tag::Mglyph => Tag::Mglyph,
        Tag::Mi => Tag::Mi,
        Tag::Mn => Tag::Mn,
        Tag::Mo => Tag::Mo,
        Tag::Ms => Tag::Ms,
        Tag::Mtext => Tag::Mtext,
        Tag::Nav => Tag::Nav,
        Tag::Nobr => Tag::Nobr,
        Tag::Noembed => Tag::Noembed,
        Tag::Noframes => Tag::Noframes,
        Tag::Noscript => Tag::Noscript,
        Tag::Object => Tag::Object,
        Tag::Ol => Tag::Ol,
        Tag::Optgroup => Tag::Optgroup,
        Tag::Option => Tag::Option,
        Tag::Output => Tag::Output,
        Tag::P => Tag::P,
        Tag::Param => Tag::Param,
        Tag::Plaintext => Tag::Plaintext,
        Tag::Pre => Tag::Pre,
        Tag::Rb => Tag::Rb,
        Tag::Rp => Tag::Rp,
        Tag::Rt => Tag::Rt,
        Tag::Rtc => Tag::Rtc,
        Tag::Ruby => Tag::Ruby,
        Tag::S => Tag::S,
        Tag::Script => Tag::Script,
        Tag::Search => Tag::Search,
        Tag::Section => Tag::Section,
        Tag::Select => Tag::Select,
        Tag::Small => Tag::Small,
        Tag::Source => Tag::Source,
        Tag::Span => Tag::Span,
        Tag::Strike => Tag::Strike,
        Tag::Strong => Tag::Strong,
        Tag::Style => Tag::Style,
        Tag::Sub => Tag::Sub,
        Tag::Summary => Tag::Summary,
        Tag::Sup => Tag::Sup,
        Tag::Svg => Tag::Svg,
        Tag::Table => Tag::Table,
        Tag::Tbody => Tag::Tbody,
        Tag::Td => Tag::Td,
        Tag::Template => Tag::Template,
        Tag::Textarea => Tag::Textarea,
        Tag::Tfoot => Tag::Tfoot,
        Tag::Th => Tag::Th,
        Tag::Thead => Tag::Thead,
        Tag::Title => Tag::Title,
        Tag::Tr => Tag::Tr,
        Tag::Track => Tag::Track,
        Tag::Tt => Tag::Tt,
        Tag::U => Tag::U,
        Tag::Ul => Tag::Ul,
        Tag::Var => Tag::Var,
        Tag::Wbr => Tag::Wbr,
        Tag::Xmp => Tag::Xmp,
        Tag::Other => Tag::Other,
    }
}

/// [`tag_of`]: the tag of a name, comparing it with each name in the
/// spec's order.
pub fn tag_of_exec(name: &[u32]) -> (r: Tag)
    ensures
        r == tag_of(name@),
{
    let l: &[u32] = &[0x61u32];
    proof {
        assert(l@ =~= seq![0x61u32]);
    }
    if u32s_eq(name, l) {
        // "a"
        return Tag::A;
    }
    let l: &[u32] = &[0x61u32, 0x64u32, 0x64u32, 0x72u32, 0x65u32, 0x73u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x64u32, 0x64u32, 0x72u32, 0x65u32, 0x73u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // "address"
        return Tag::Address;
    }
    let l: &[u32] = &[0x61u32, 0x6eu32, 0x6eu32, 0x6fu32, 0x74u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32, 0x2du32, 0x78u32, 0x6du32, 0x6cu32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x6eu32, 0x6eu32, 0x6fu32, 0x74u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32, 0x2du32, 0x78u32, 0x6du32, 0x6cu32]);
    }
    if u32s_eq(name, l) {
        // "annotation-xml"
        return Tag::AnnotationXml;
    }
    let l: &[u32] = &[0x61u32, 0x70u32, 0x70u32, 0x6cu32, 0x65u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x70u32, 0x70u32, 0x6cu32, 0x65u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "applet"
        return Tag::Applet;
    }
    let l: &[u32] = &[0x61u32, 0x72u32, 0x65u32, 0x61u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x72u32, 0x65u32, 0x61u32]);
    }
    if u32s_eq(name, l) {
        // "area"
        return Tag::Area;
    }
    let l: &[u32] = &[0x61u32, 0x72u32, 0x74u32, 0x69u32, 0x63u32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x72u32, 0x74u32, 0x69u32, 0x63u32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "article"
        return Tag::Article;
    }
    let l: &[u32] = &[0x61u32, 0x73u32, 0x69u32, 0x64u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x73u32, 0x69u32, 0x64u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "aside"
        return Tag::Aside;
    }
    let l: &[u32] = &[0x62u32];
    proof {
        assert(l@ =~= seq![0x62u32]);
    }
    if u32s_eq(name, l) {
        // "b"
        return Tag::B;
    }
    let l: &[u32] = &[0x62u32, 0x61u32, 0x73u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x61u32, 0x73u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "base"
        return Tag::Base;
    }
    let l: &[u32] = &[0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x66u32, 0x6fu32, 0x6eu32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x66u32, 0x6fu32, 0x6eu32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "basefont"
        return Tag::Basefont;
    }
    let l: &[u32] = &[0x62u32, 0x67u32, 0x73u32, 0x6fu32, 0x75u32, 0x6eu32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x67u32, 0x73u32, 0x6fu32, 0x75u32, 0x6eu32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // "bgsound"
        return Tag::Bgsound;
    }
    let l: &[u32] = &[0x62u32, 0x69u32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x69u32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // "big"
        return Tag::Big;
    }
    let l: &[u32] = &[0x62u32, 0x6cu32, 0x6fu32, 0x63u32, 0x6bu32, 0x71u32, 0x75u32, 0x6fu32, 0x74u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x6cu32, 0x6fu32, 0x63u32, 0x6bu32, 0x71u32, 0x75u32, 0x6fu32, 0x74u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "blockquote"
        return Tag::Blockquote;
    }
    let l: &[u32] = &[0x62u32, 0x6fu32, 0x64u32, 0x79u32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x6fu32, 0x64u32, 0x79u32]);
    }
    if u32s_eq(name, l) {
        // "body"
        return Tag::Body;
    }
    let l: &[u32] = &[0x62u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "br"
        return Tag::Br;
    }
    let l: &[u32] = &[0x62u32, 0x75u32, 0x74u32, 0x74u32, 0x6fu32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x75u32, 0x74u32, 0x74u32, 0x6fu32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // "button"
        return Tag::Button;
    }
    let l: &[u32] = &[0x63u32, 0x61u32, 0x70u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x63u32, 0x61u32, 0x70u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // "caption"
        return Tag::Caption;
    }
    let l: &[u32] = &[0x63u32, 0x65u32, 0x6eu32, 0x74u32, 0x65u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x63u32, 0x65u32, 0x6eu32, 0x74u32, 0x65u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "center"
        return Tag::Center;
    }
    let l: &[u32] = &[0x63u32, 0x6fu32, 0x64u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x63u32, 0x6fu32, 0x64u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "code"
        return Tag::Code;
    }
    let l: &[u32] = &[0x63u32, 0x6fu32, 0x6cu32];
    proof {
        assert(l@ =~= seq![0x63u32, 0x6fu32, 0x6cu32]);
    }
    if u32s_eq(name, l) {
        // "col"
        return Tag::Col;
    }
    let l: &[u32] = &[0x63u32, 0x6fu32, 0x6cu32, 0x67u32, 0x72u32, 0x6fu32, 0x75u32, 0x70u32];
    proof {
        assert(l@ =~= seq![0x63u32, 0x6fu32, 0x6cu32, 0x67u32, 0x72u32, 0x6fu32, 0x75u32, 0x70u32]);
    }
    if u32s_eq(name, l) {
        // "colgroup"
        return Tag::Colgroup;
    }
    let l: &[u32] = &[0x64u32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x64u32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // "dd"
        return Tag::Dd;
    }
    let l: &[u32] = &[0x64u32, 0x65u32, 0x73u32, 0x63u32];
    proof {
        assert(l@ =~= seq![0x64u32, 0x65u32, 0x73u32, 0x63u32]);
    }
    if u32s_eq(name, l) {
        // "desc"
        return Tag::Desc;
    }
    let l: &[u32] = &[0x64u32, 0x65u32, 0x74u32, 0x61u32, 0x69u32, 0x6cu32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x64u32, 0x65u32, 0x74u32, 0x61u32, 0x69u32, 0x6cu32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // "details"
        return Tag::Details;
    }
    let l: &[u32] = &[0x64u32, 0x69u32, 0x61u32, 0x6cu32, 0x6fu32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x64u32, 0x69u32, 0x61u32, 0x6cu32, 0x6fu32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // "dialog"
        return Tag::Dialog;
    }
    let l: &[u32] = &[0x64u32, 0x69u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x64u32, 0x69u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "dir"
        return Tag::Dir;
    }
    let l: &[u32] = &[0x64u32, 0x69u32, 0x76u32];
    proof {
        assert(l@ =~= seq![0x64u32, 0x69u32, 0x76u32]);
    }
    if u32s_eq(name, l) {
        // "div"
        return Tag::Div;
    }
    let l: &[u32] = &[0x64u32, 0x6cu32];
    proof {
        assert(l@ =~= seq![0x64u32, 0x6cu32]);
    }
    if u32s_eq(name, l) {
        // "dl"
        return Tag::Dl;
    }
    let l: &[u32] = &[0x64u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x64u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "dt"
        return Tag::Dt;
    }
    let l: &[u32] = &[0x65u32, 0x6du32];
    proof {
        assert(l@ =~= seq![0x65u32, 0x6du32]);
    }
    if u32s_eq(name, l) {
        // "em"
        return Tag::Em;
    }
    let l: &[u32] = &[0x65u32, 0x6du32, 0x62u32, 0x65u32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x65u32, 0x6du32, 0x62u32, 0x65u32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // "embed"
        return Tag::Embed;
    }
    let l: &[u32] = &[0x66u32, 0x69u32, 0x65u32, 0x6cu32, 0x64u32, 0x73u32, 0x65u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x69u32, 0x65u32, 0x6cu32, 0x64u32, 0x73u32, 0x65u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "fieldset"
        return Tag::Fieldset;
    }
    let l: &[u32] = &[0x66u32, 0x69u32, 0x67u32, 0x63u32, 0x61u32, 0x70u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x69u32, 0x67u32, 0x63u32, 0x61u32, 0x70u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // "figcaption"
        return Tag::Figcaption;
    }
    let l: &[u32] = &[0x66u32, 0x69u32, 0x67u32, 0x75u32, 0x72u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x69u32, 0x67u32, 0x75u32, 0x72u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "figure"
        return Tag::Figure;
    }
    let l: &[u32] = &[0x66u32, 0x6fu32, 0x6eu32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x6fu32, 0x6eu32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "font"
        return Tag::Font;
    }
    let l: &[u32] = &[0x66u32, 0x6fu32, 0x6fu32, 0x74u32, 0x65u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x6fu32, 0x6fu32, 0x74u32, 0x65u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "footer"
        return Tag::Footer;
    }
    let l: &[u32] = &[0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x6fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x6fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "foreignobject"
        return Tag::Foreignobject;
    }
    let l: &[u32] = &[0x66u32, 0x6fu32, 0x72u32, 0x6du32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x6fu32, 0x72u32, 0x6du32]);
    }
    if u32s_eq(name, l) {
        // "form"
        return Tag::Form;
    }
    let l: &[u32] = &[0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "frame"
        return Tag::Frame;
    }
    let l: &[u32] = &[0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32, 0x73u32, 0x65u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32, 0x73u32, 0x65u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "frameset"
        return Tag::Frameset;
    }
    let l: &[u32] = &[0x68u32, 0x31u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x31u32]);
    }
    if u32s_eq(name, l) {
        // "h1"
        return Tag::H1;
    }
    let l: &[u32] = &[0x68u32, 0x32u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x32u32]);
    }
    if u32s_eq(name, l) {
        // "h2"
        return Tag::H2;
    }
    let l: &[u32] = &[0x68u32, 0x33u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x33u32]);
    }
    if u32s_eq(name, l) {
        // "h3"
        return Tag::H3;
    }
    let l: &[u32] = &[0x68u32, 0x34u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x34u32]);
    }
    if u32s_eq(name, l) {
        // "h4"
        return Tag::H4;
    }
    let l: &[u32] = &[0x68u32, 0x35u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x35u32]);
    }
    if u32s_eq(name, l) {
        // "h5"
        return Tag::H5;
    }
    let l: &[u32] = &[0x68u32, 0x36u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x36u32]);
    }
    if u32s_eq(name, l) {
        // "h6"
        return Tag::H6;
    }
    let l: &[u32] = &[0x68u32, 0x65u32, 0x61u32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x65u32, 0x61u32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // "head"
        return Tag::Head;
    }
    let l: &[u32] = &[0x68u32, 0x65u32, 0x61u32, 0x64u32, 0x65u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x65u32, 0x61u32, 0x64u32, 0x65u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "header"
        return Tag::Header;
    }
    let l: &[u32] = &[0x68u32, 0x67u32, 0x72u32, 0x6fu32, 0x75u32, 0x70u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x67u32, 0x72u32, 0x6fu32, 0x75u32, 0x70u32]);
    }
    if u32s_eq(name, l) {
        // "hgroup"
        return Tag::Hgroup;
    }
    let l: &[u32] = &[0x68u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "hr"
        return Tag::Hr;
    }
    let l: &[u32] = &[0x68u32, 0x74u32, 0x6du32, 0x6cu32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x74u32, 0x6du32, 0x6cu32]);
    }
    if u32s_eq(name, l) {
        // "html"
        return Tag::Html;
    }
    let l: &[u32] = &[0x69u32];
    proof {
        assert(l@ =~= seq![0x69u32]);
    }
    if u32s_eq(name, l) {
        // "i"
        return Tag::I;
    }
    let l: &[u32] = &[0x69u32, 0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x69u32, 0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "iframe"
        return Tag::Iframe;
    }
    let l: &[u32] = &[0x69u32, 0x6du32, 0x61u32, 0x67u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x69u32, 0x6du32, 0x61u32, 0x67u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "image"
        return Tag::Image;
    }
    let l: &[u32] = &[0x69u32, 0x6du32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x69u32, 0x6du32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // "img"
        return Tag::Img;
    }
    let l: &[u32] = &[0x69u32, 0x6eu32, 0x70u32, 0x75u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x69u32, 0x6eu32, 0x70u32, 0x75u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "input"
        return Tag::Input;
    }
    let l: &[u32] = &[0x6bu32, 0x65u32, 0x79u32, 0x67u32, 0x65u32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x6bu32, 0x65u32, 0x79u32, 0x67u32, 0x65u32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // "keygen"
        return Tag::Keygen;
    }
    let l: &[u32] = &[0x6cu32, 0x69u32];
    proof {
        assert(l@ =~= seq![0x6cu32, 0x69u32]);
    }
    if u32s_eq(name, l) {
        // "li"
        return Tag::Li;
    }
    let l: &[u32] = &[0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
    proof {
        assert(l@ =~= seq![0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
    }
    if u32s_eq(name, l) {
        // "link"
        return Tag::Link;
    }
    let l: &[u32] = &[0x6cu32, 0x69u32, 0x73u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x6cu32, 0x69u32, 0x73u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // "listing"
        return Tag::Listing;
    }
    let l: &[u32] = &[0x6du32, 0x61u32, 0x69u32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x61u32, 0x69u32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // "main"
        return Tag::Main;
    }
    let l: &[u32] = &[0x6du32, 0x61u32, 0x6cu32, 0x69u32, 0x67u32, 0x6eu32, 0x6du32, 0x61u32, 0x72u32, 0x6bu32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x61u32, 0x6cu32, 0x69u32, 0x67u32, 0x6eu32, 0x6du32, 0x61u32, 0x72u32, 0x6bu32]);
    }
    if u32s_eq(name, l) {
        // "malignmark"
        return Tag::Malignmark;
    }
    let l: &[u32] = &[0x6du32, 0x61u32, 0x72u32, 0x71u32, 0x75u32, 0x65u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x61u32, 0x72u32, 0x71u32, 0x75u32, 0x65u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "marquee"
        return Tag::Marquee;
    }
    let l: &[u32] = &[0x6du32, 0x61u32, 0x74u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x61u32, 0x74u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // "math"
        return Tag::Math;
    }
    let l: &[u32] = &[0x6du32, 0x65u32, 0x6eu32, 0x75u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x65u32, 0x6eu32, 0x75u32]);
    }
    if u32s_eq(name, l) {
        // "menu"
        return Tag::Menu;
    }
    let l: &[u32] = &[0x6du32, 0x65u32, 0x74u32, 0x61u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x65u32, 0x74u32, 0x61u32]);
    }
    if u32s_eq(name, l) {
        // "meta"
        return Tag::Meta;
    }
    let l: &[u32] = &[0x6du32, 0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // "mglyph"
        return Tag::Mglyph;
    }
    let l: &[u32] = &[0x6du32, 0x69u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x69u32]);
    }
    if u32s_eq(name, l) {
        // "mi"
        return Tag::Mi;
    }
    let l: &[u32] = &[0x6du32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // "mn"
        return Tag::Mn;
    }
    let l: &[u32] = &[0x6du32, 0x6fu32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x6fu32]);
    }
    if u32s_eq(name, l) {
        // "mo"
        return Tag::Mo;
    }
    let l: &[u32] = &[0x6du32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // "ms"
        return Tag::Ms;
    }
    let l: &[u32] = &[0x6du32, 0x74u32, 0x65u32, 0x78u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x74u32, 0x65u32, 0x78u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "mtext"
        return Tag::Mtext;
    }
    let l: &[u32] = &[0x6eu32, 0x61u32, 0x76u32];
    proof {
        assert(l@ =~= seq![0x6eu32, 0x61u32, 0x76u32]);
    }
    if u32s_eq(name, l) {
        // "nav"
        return Tag::Nav;
    }
    let l: &[u32] = &[0x6eu32, 0x6fu32, 0x62u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x6eu32, 0x6fu32, 0x62u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "nobr"
        return Tag::Nobr;
    }
    let l: &[u32] = &[0x6eu32, 0x6fu32, 0x65u32, 0x6du32, 0x62u32, 0x65u32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x6eu32, 0x6fu32, 0x65u32, 0x6du32, 0x62u32, 0x65u32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // "noembed"
        return Tag::Noembed;
    }
    let l: &[u32] = &[0x6eu32, 0x6fu32, 0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x6eu32, 0x6fu32, 0x66u32, 0x72u32, 0x61u32, 0x6du32, 0x65u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // "noframes"
        return Tag::Noframes;
    }
    let l: &[u32] = &[0x6eu32, 0x6fu32, 0x73u32, 0x63u32, 0x72u32, 0x69u32, 0x70u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x6eu32, 0x6fu32, 0x73u32, 0x63u32, 0x72u32, 0x69u32, 0x70u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "noscript"
        return Tag::Noscript;
    }
    let l: &[u32] = &[0x6fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x6fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "object"
        return Tag::Object;
    }
    let l: &[u32] = &[0x6fu32, 0x6cu32];
    proof {
        assert(l@ =~= seq![0x6fu32, 0x6cu32]);
    }
    if u32s_eq(name, l) {
        // "ol"
        return Tag::Ol;
    }
    let l: &[u32] = &[0x6fu32, 0x70u32, 0x74u32, 0x67u32, 0x72u32, 0x6fu32, 0x75u32, 0x70u32];
    proof {
        assert(l@ =~= seq![0x6fu32, 0x70u32, 0x74u32, 0x67u32, 0x72u32, 0x6fu32, 0x75u32, 0x70u32]);
    }
    if u32s_eq(name, l) {
        // "optgroup"
        return Tag::Optgroup;
    }
    let l: &[u32] = &[0x6fu32, 0x70u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x6fu32, 0x70u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // "option"
        return Tag::Option;
    }
    let l: &[u32] = &[0x6fu32, 0x75u32, 0x74u32, 0x70u32, 0x75u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x6fu32, 0x75u32, 0x74u32, 0x70u32, 0x75u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "output"
        return Tag::Output;
    }
    let l: &[u32] = &[0x70u32];
    proof {
        assert(l@ =~= seq![0x70u32]);
    }
    if u32s_eq(name, l) {
        // "p"
        return Tag::P;
    }
    let l: &[u32] = &[0x70u32, 0x61u32, 0x72u32, 0x61u32, 0x6du32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x61u32, 0x72u32, 0x61u32, 0x6du32]);
    }
    if u32s_eq(name, l) {
        // "param"
        return Tag::Param;
    }
    let l: &[u32] = &[0x70u32, 0x6cu32, 0x61u32, 0x69u32, 0x6eu32, 0x74u32, 0x65u32, 0x78u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x6cu32, 0x61u32, 0x69u32, 0x6eu32, 0x74u32, 0x65u32, 0x78u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "plaintext"
        return Tag::Plaintext;
    }
    let l: &[u32] = &[0x70u32, 0x72u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x72u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "pre"
        return Tag::Pre;
    }
    let l: &[u32] = &[0x72u32, 0x62u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x62u32]);
    }
    if u32s_eq(name, l) {
        // "rb"
        return Tag::Rb;
    }
    let l: &[u32] = &[0x72u32, 0x70u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x70u32]);
    }
    if u32s_eq(name, l) {
        // "rp"
        return Tag::Rp;
    }
    let l: &[u32] = &[0x72u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "rt"
        return Tag::Rt;
    }
    let l: &[u32] = &[0x72u32, 0x74u32, 0x63u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x74u32, 0x63u32]);
    }
    if u32s_eq(name, l) {
        // "rtc"
        return Tag::Rtc;
    }
    let l: &[u32] = &[0x72u32, 0x75u32, 0x62u32, 0x79u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x75u32, 0x62u32, 0x79u32]);
    }
    if u32s_eq(name, l) {
        // "ruby"
        return Tag::Ruby;
    }
    let l: &[u32] = &[0x73u32];
    proof {
        assert(l@ =~= seq![0x73u32]);
    }
    if u32s_eq(name, l) {
        // "s"
        return Tag::S;
    }
    let l: &[u32] = &[0x73u32, 0x63u32, 0x72u32, 0x69u32, 0x70u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x63u32, 0x72u32, 0x69u32, 0x70u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "script"
        return Tag::Script;
    }
    let l: &[u32] = &[0x73u32, 0x65u32, 0x61u32, 0x72u32, 0x63u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x65u32, 0x61u32, 0x72u32, 0x63u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // "search"
        return Tag::Search;
    }
    let l: &[u32] = &[0x73u32, 0x65u32, 0x63u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x65u32, 0x63u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // "section"
        return Tag::Section;
    }
    let l: &[u32] = &[0x73u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "select"
        return Tag::Select;
    }
    let l: &[u32] = &[0x73u32, 0x6du32, 0x61u32, 0x6cu32, 0x6cu32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x6du32, 0x61u32, 0x6cu32, 0x6cu32]);
    }
    if u32s_eq(name, l) {
        // "small"
        return Tag::Small;
    }
    let l: &[u32] = &[0x73u32, 0x6fu32, 0x75u32, 0x72u32, 0x63u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x6fu32, 0x75u32, 0x72u32, 0x63u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "source"
        return Tag::Source;
    }
    let l: &[u32] = &[0x73u32, 0x70u32, 0x61u32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x70u32, 0x61u32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // "span"
        return Tag::Span;
    }
    let l: &[u32] = &[0x73u32, 0x74u32, 0x72u32, 0x69u32, 0x6bu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x74u32, 0x72u32, 0x69u32, 0x6bu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "strike"
        return Tag::Strike;
    }
    let l: &[u32] = &[0x73u32, 0x74u32, 0x72u32, 0x6fu32, 0x6eu32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x74u32, 0x72u32, 0x6fu32, 0x6eu32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // "strong"
        return Tag::Strong;
    }
    let l: &[u32] = &[0x73u32, 0x74u32, 0x79u32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x74u32, 0x79u32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "style"
        return Tag::Style;
    }
    let l: &[u32] = &[0x73u32, 0x75u32, 0x62u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x75u32, 0x62u32]);
    }
    if u32s_eq(name, l) {
        // "sub"
        return Tag::Sub;
    }
    let l: &[u32] = &[0x73u32, 0x75u32, 0x6du32, 0x6du32, 0x61u32, 0x72u32, 0x79u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x75u32, 0x6du32, 0x6du32, 0x61u32, 0x72u32, 0x79u32]);
    }
    if u32s_eq(name, l) {
        // "summary"
        return Tag::Summary;
    }
    let l: &[u32] = &[0x73u32, 0x75u32, 0x70u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x75u32, 0x70u32]);
    }
    if u32s_eq(name, l) {
        // "sup"
        return Tag::Sup;
    }
    let l: &[u32] = &[0x73u32, 0x76u32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x76u32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // "svg"
        return Tag::Svg;
    }
    let l: &[u32] = &[0x74u32, 0x61u32, 0x62u32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x61u32, 0x62u32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "table"
        return Tag::Table;
    }
    let l: &[u32] = &[0x74u32, 0x62u32, 0x6fu32, 0x64u32, 0x79u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x62u32, 0x6fu32, 0x64u32, 0x79u32]);
    }
    if u32s_eq(name, l) {
        // "tbody"
        return Tag::Tbody;
    }
    let l: &[u32] = &[0x74u32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // "td"
        return Tag::Td;
    }
    let l: &[u32] = &[0x74u32, 0x65u32, 0x6du32, 0x70u32, 0x6cu32, 0x61u32, 0x74u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x65u32, 0x6du32, 0x70u32, 0x6cu32, 0x61u32, 0x74u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "template"
        return Tag::Template;
    }
    let l: &[u32] = &[0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x61u32, 0x72u32, 0x65u32, 0x61u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x61u32, 0x72u32, 0x65u32, 0x61u32]);
    }
    if u32s_eq(name, l) {
        // "textarea"
        return Tag::Textarea;
    }
    let l: &[u32] = &[0x74u32, 0x66u32, 0x6fu32, 0x6fu32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x66u32, 0x6fu32, 0x6fu32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "tfoot"
        return Tag::Tfoot;
    }
    let l: &[u32] = &[0x74u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // "th"
        return Tag::Th;
    }
    let l: &[u32] = &[0x74u32, 0x68u32, 0x65u32, 0x61u32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x68u32, 0x65u32, 0x61u32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // "thead"
        return Tag::Thead;
    }
    let l: &[u32] = &[0x74u32, 0x69u32, 0x74u32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x69u32, 0x74u32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // "title"
        return Tag::Title;
    }
    let l: &[u32] = &[0x74u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "tr"
        return Tag::Tr;
    }
    let l: &[u32] = &[0x74u32, 0x72u32, 0x61u32, 0x63u32, 0x6bu32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x72u32, 0x61u32, 0x63u32, 0x6bu32]);
    }
    if u32s_eq(name, l) {
        // "track"
        return Tag::Track;
    }
    let l: &[u32] = &[0x74u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "tt"
        return Tag::Tt;
    }
    let l: &[u32] = &[0x75u32];
    proof {
        assert(l@ =~= seq![0x75u32]);
    }
    if u32s_eq(name, l) {
        // "u"
        return Tag::U;
    }
    let l: &[u32] = &[0x75u32, 0x6cu32];
    proof {
        assert(l@ =~= seq![0x75u32, 0x6cu32]);
    }
    if u32s_eq(name, l) {
        // "ul"
        return Tag::Ul;
    }
    let l: &[u32] = &[0x76u32, 0x61u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x76u32, 0x61u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "var"
        return Tag::Var;
    }
    let l: &[u32] = &[0x77u32, 0x62u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x77u32, 0x62u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // "wbr"
        return Tag::Wbr;
    }
    let l: &[u32] = &[0x78u32, 0x6du32, 0x70u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6du32, 0x70u32]);
    }
    if u32s_eq(name, l) {
        // "xmp"
        return Tag::Xmp;
    }
    let l: &[u32] = &[0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x4fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x4fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // "foreignObject"
        return Tag::Foreignobject;
    }
    Tag::Other
}

/// [`svg_attribute_name`]: `Some` of the new name for a name in the
/// table, `None` for a name it keeps.
pub fn svg_attribute_name_exec(name: &[u32]) -> (r: Option<Vec<u32>>)
    ensures
        match r {
            Some(v) => v@ == svg_attribute_name(name@),
            None => svg_attribute_name(name@) == name@,
        },
{
    let l: &[u32] = &[0x61u32, 0x74u32, 0x74u32, 0x72u32, 0x69u32, 0x62u32, 0x75u32, 0x74u32, 0x65u32, 0x6eu32, 0x61u32, 0x6du32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x74u32, 0x74u32, 0x72u32, 0x69u32, 0x62u32, 0x75u32, 0x74u32, 0x65u32, 0x6eu32, 0x61u32, 0x6du32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | attributename | attributeName |
        let v = vec![0x61u32, 0x74u32, 0x74u32, 0x72u32, 0x69u32, 0x62u32, 0x75u32, 0x74u32, 0x65u32, 0x4eu32, 0x61u32, 0x6du32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x61u32, 0x74u32, 0x74u32, 0x72u32, 0x69u32, 0x62u32, 0x75u32, 0x74u32, 0x65u32, 0x4eu32, 0x61u32, 0x6du32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x61u32, 0x74u32, 0x74u32, 0x72u32, 0x69u32, 0x62u32, 0x75u32, 0x74u32, 0x65u32, 0x74u32, 0x79u32, 0x70u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x74u32, 0x74u32, 0x72u32, 0x69u32, 0x62u32, 0x75u32, 0x74u32, 0x65u32, 0x74u32, 0x79u32, 0x70u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | attributetype | attributeType |
        let v = vec![0x61u32, 0x74u32, 0x74u32, 0x72u32, 0x69u32, 0x62u32, 0x75u32, 0x74u32, 0x65u32, 0x54u32, 0x79u32, 0x70u32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x61u32, 0x74u32, 0x74u32, 0x72u32, 0x69u32, 0x62u32, 0x75u32, 0x74u32, 0x65u32, 0x54u32, 0x79u32, 0x70u32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x66u32, 0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x65u32, 0x6eu32, 0x63u32, 0x79u32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x66u32, 0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x65u32, 0x6eu32, 0x63u32, 0x79u32]);
    }
    if u32s_eq(name, l) {
        // | basefrequency | baseFrequency |
        let v = vec![0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x46u32, 0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x65u32, 0x6eu32, 0x63u32, 0x79u32];
        proof {
            assert(v@ =~= seq![0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x46u32, 0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x65u32, 0x6eu32, 0x63u32, 0x79u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x70u32, 0x72u32, 0x6fu32, 0x66u32, 0x69u32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x70u32, 0x72u32, 0x6fu32, 0x66u32, 0x69u32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | baseprofile | baseProfile |
        let v = vec![0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x50u32, 0x72u32, 0x6fu32, 0x66u32, 0x69u32, 0x6cu32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x62u32, 0x61u32, 0x73u32, 0x65u32, 0x50u32, 0x72u32, 0x6fu32, 0x66u32, 0x69u32, 0x6cu32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x63u32, 0x61u32, 0x6cu32, 0x63u32, 0x6du32, 0x6fu32, 0x64u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x63u32, 0x61u32, 0x6cu32, 0x63u32, 0x6du32, 0x6fu32, 0x64u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | calcmode | calcMode |
        let v = vec![0x63u32, 0x61u32, 0x6cu32, 0x63u32, 0x4du32, 0x6fu32, 0x64u32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x63u32, 0x61u32, 0x6cu32, 0x63u32, 0x4du32, 0x6fu32, 0x64u32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x63u32, 0x6cu32, 0x69u32, 0x70u32, 0x70u32, 0x61u32, 0x74u32, 0x68u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x63u32, 0x6cu32, 0x69u32, 0x70u32, 0x70u32, 0x61u32, 0x74u32, 0x68u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | clippathunits | clipPathUnits |
        let v = vec![0x63u32, 0x6cu32, 0x69u32, 0x70u32, 0x50u32, 0x61u32, 0x74u32, 0x68u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x63u32, 0x6cu32, 0x69u32, 0x70u32, 0x50u32, 0x61u32, 0x74u32, 0x68u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x64u32, 0x69u32, 0x66u32, 0x66u32, 0x75u32, 0x73u32, 0x65u32, 0x63u32, 0x6fu32, 0x6eu32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x64u32, 0x69u32, 0x66u32, 0x66u32, 0x75u32, 0x73u32, 0x65u32, 0x63u32, 0x6fu32, 0x6eu32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | diffuseconstant | diffuseConstant |
        let v = vec![0x64u32, 0x69u32, 0x66u32, 0x66u32, 0x75u32, 0x73u32, 0x65u32, 0x43u32, 0x6fu32, 0x6eu32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x64u32, 0x69u32, 0x66u32, 0x66u32, 0x75u32, 0x73u32, 0x65u32, 0x43u32, 0x6fu32, 0x6eu32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x65u32, 0x64u32, 0x67u32, 0x65u32, 0x6du32, 0x6fu32, 0x64u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x65u32, 0x64u32, 0x67u32, 0x65u32, 0x6du32, 0x6fu32, 0x64u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | edgemode | edgeMode |
        let v = vec![0x65u32, 0x64u32, 0x67u32, 0x65u32, 0x4du32, 0x6fu32, 0x64u32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x65u32, 0x64u32, 0x67u32, 0x65u32, 0x4du32, 0x6fu32, 0x64u32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x69u32, 0x6cu32, 0x74u32, 0x65u32, 0x72u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x69u32, 0x6cu32, 0x74u32, 0x65u32, 0x72u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | filterunits | filterUnits |
        let v = vec![0x66u32, 0x69u32, 0x6cu32, 0x74u32, 0x65u32, 0x72u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x69u32, 0x6cu32, 0x74u32, 0x65u32, 0x72u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x72u32, 0x65u32, 0x66u32];
    proof {
        assert(l@ =~= seq![0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x72u32, 0x65u32, 0x66u32]);
    }
    if u32s_eq(name, l) {
        // | glyphref | glyphRef |
        let v = vec![0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x52u32, 0x65u32, 0x66u32];
        proof {
            assert(v@ =~= seq![0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x52u32, 0x65u32, 0x66u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32, 0x74u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32];
    proof {
        assert(l@ =~= seq![0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32, 0x74u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32]);
    }
    if u32s_eq(name, l) {
        // | gradienttransform | gradientTransform |
        let v = vec![0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32, 0x54u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32];
        proof {
            assert(v@ =~= seq![0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32, 0x54u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | gradientunits | gradientUnits |
        let v = vec![0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6bu32, 0x65u32, 0x72u32, 0x6eu32, 0x65u32, 0x6cu32, 0x6du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32];
    proof {
        assert(l@ =~= seq![0x6bu32, 0x65u32, 0x72u32, 0x6eu32, 0x65u32, 0x6cu32, 0x6du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32]);
    }
    if u32s_eq(name, l) {
        // | kernelmatrix | kernelMatrix |
        let v = vec![0x6bu32, 0x65u32, 0x72u32, 0x6eu32, 0x65u32, 0x6cu32, 0x4du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32];
        proof {
            assert(v@ =~= seq![0x6bu32, 0x65u32, 0x72u32, 0x6eu32, 0x65u32, 0x6cu32, 0x4du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6bu32, 0x65u32, 0x72u32, 0x6eu32, 0x65u32, 0x6cu32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x6bu32, 0x65u32, 0x72u32, 0x6eu32, 0x65u32, 0x6cu32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // | kernelunitlength | kernelUnitLength |
        let v = vec![0x6bu32, 0x65u32, 0x72u32, 0x6eu32, 0x65u32, 0x6cu32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x4cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32];
        proof {
            assert(v@ =~= seq![0x6bu32, 0x65u32, 0x72u32, 0x6eu32, 0x65u32, 0x6cu32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x4cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6bu32, 0x65u32, 0x79u32, 0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x6bu32, 0x65u32, 0x79u32, 0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | keypoints | keyPoints |
        let v = vec![0x6bu32, 0x65u32, 0x79u32, 0x50u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x6bu32, 0x65u32, 0x79u32, 0x50u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6bu32, 0x65u32, 0x79u32, 0x73u32, 0x70u32, 0x6cu32, 0x69u32, 0x6eu32, 0x65u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x6bu32, 0x65u32, 0x79u32, 0x73u32, 0x70u32, 0x6cu32, 0x69u32, 0x6eu32, 0x65u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | keysplines | keySplines |
        let v = vec![0x6bu32, 0x65u32, 0x79u32, 0x53u32, 0x70u32, 0x6cu32, 0x69u32, 0x6eu32, 0x65u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x6bu32, 0x65u32, 0x79u32, 0x53u32, 0x70u32, 0x6cu32, 0x69u32, 0x6eu32, 0x65u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6bu32, 0x65u32, 0x79u32, 0x74u32, 0x69u32, 0x6du32, 0x65u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x6bu32, 0x65u32, 0x79u32, 0x74u32, 0x69u32, 0x6du32, 0x65u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | keytimes | keyTimes |
        let v = vec![0x6bu32, 0x65u32, 0x79u32, 0x54u32, 0x69u32, 0x6du32, 0x65u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x6bu32, 0x65u32, 0x79u32, 0x54u32, 0x69u32, 0x6du32, 0x65u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32, 0x61u32, 0x64u32, 0x6au32, 0x75u32, 0x73u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32, 0x61u32, 0x64u32, 0x6au32, 0x75u32, 0x73u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | lengthadjust | lengthAdjust |
        let v = vec![0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32, 0x41u32, 0x64u32, 0x6au32, 0x75u32, 0x73u32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32, 0x41u32, 0x64u32, 0x6au32, 0x75u32, 0x73u32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6cu32, 0x69u32, 0x6du32, 0x69u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32, 0x63u32, 0x6fu32, 0x6eu32, 0x65u32, 0x61u32, 0x6eu32, 0x67u32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x6cu32, 0x69u32, 0x6du32, 0x69u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32, 0x63u32, 0x6fu32, 0x6eu32, 0x65u32, 0x61u32, 0x6eu32, 0x67u32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | limitingconeangle | limitingConeAngle |
        let v = vec![0x6cu32, 0x69u32, 0x6du32, 0x69u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32, 0x43u32, 0x6fu32, 0x6eu32, 0x65u32, 0x41u32, 0x6eu32, 0x67u32, 0x6cu32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x6cu32, 0x69u32, 0x6du32, 0x69u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32, 0x43u32, 0x6fu32, 0x6eu32, 0x65u32, 0x41u32, 0x6eu32, 0x67u32, 0x6cu32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x68u32, 0x65u32, 0x69u32, 0x67u32, 0x68u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x68u32, 0x65u32, 0x69u32, 0x67u32, 0x68u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | markerheight | markerHeight |
        let v = vec![0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x48u32, 0x65u32, 0x69u32, 0x67u32, 0x68u32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x48u32, 0x65u32, 0x69u32, 0x67u32, 0x68u32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | markerunits | markerUnits |
        let v = vec![0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x77u32, 0x69u32, 0x64u32, 0x74u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x77u32, 0x69u32, 0x64u32, 0x74u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // | markerwidth | markerWidth |
        let v = vec![0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x57u32, 0x69u32, 0x64u32, 0x74u32, 0x68u32];
        proof {
            assert(v@ =~= seq![0x6du32, 0x61u32, 0x72u32, 0x6bu32, 0x65u32, 0x72u32, 0x57u32, 0x69u32, 0x64u32, 0x74u32, 0x68u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6du32, 0x61u32, 0x73u32, 0x6bu32, 0x63u32, 0x6fu32, 0x6eu32, 0x74u32, 0x65u32, 0x6eu32, 0x74u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x61u32, 0x73u32, 0x6bu32, 0x63u32, 0x6fu32, 0x6eu32, 0x74u32, 0x65u32, 0x6eu32, 0x74u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | maskcontentunits | maskContentUnits |
        let v = vec![0x6du32, 0x61u32, 0x73u32, 0x6bu32, 0x43u32, 0x6fu32, 0x6eu32, 0x74u32, 0x65u32, 0x6eu32, 0x74u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x6du32, 0x61u32, 0x73u32, 0x6bu32, 0x43u32, 0x6fu32, 0x6eu32, 0x74u32, 0x65u32, 0x6eu32, 0x74u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6du32, 0x61u32, 0x73u32, 0x6bu32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x6du32, 0x61u32, 0x73u32, 0x6bu32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | maskunits | maskUnits |
        let v = vec![0x6du32, 0x61u32, 0x73u32, 0x6bu32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x6du32, 0x61u32, 0x73u32, 0x6bu32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6eu32, 0x75u32, 0x6du32, 0x6fu32, 0x63u32, 0x74u32, 0x61u32, 0x76u32, 0x65u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x6eu32, 0x75u32, 0x6du32, 0x6fu32, 0x63u32, 0x74u32, 0x61u32, 0x76u32, 0x65u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | numoctaves | numOctaves |
        let v = vec![0x6eu32, 0x75u32, 0x6du32, 0x4fu32, 0x63u32, 0x74u32, 0x61u32, 0x76u32, 0x65u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x6eu32, 0x75u32, 0x6du32, 0x4fu32, 0x63u32, 0x74u32, 0x61u32, 0x76u32, 0x65u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x61u32, 0x74u32, 0x68u32, 0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x61u32, 0x74u32, 0x68u32, 0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // | pathlength | pathLength |
        let v = vec![0x70u32, 0x61u32, 0x74u32, 0x68u32, 0x4cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x61u32, 0x74u32, 0x68u32, 0x4cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x63u32, 0x6fu32, 0x6eu32, 0x74u32, 0x65u32, 0x6eu32, 0x74u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x63u32, 0x6fu32, 0x6eu32, 0x74u32, 0x65u32, 0x6eu32, 0x74u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | patterncontentunits | patternContentUnits |
        let v = vec![0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x43u32, 0x6fu32, 0x6eu32, 0x74u32, 0x65u32, 0x6eu32, 0x74u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x43u32, 0x6fu32, 0x6eu32, 0x74u32, 0x65u32, 0x6eu32, 0x74u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x74u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x74u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32]);
    }
    if u32s_eq(name, l) {
        // | patterntransform | patternTransform |
        let v = vec![0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x54u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x54u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | patternunits | patternUnits |
        let v = vec![0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x61u32, 0x74u32, 0x74u32, 0x65u32, 0x72u32, 0x6eu32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x61u32, 0x74u32, 0x78u32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x61u32, 0x74u32, 0x78u32]);
    }
    if u32s_eq(name, l) {
        // | pointsatx | pointsAtX |
        let v = vec![0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x41u32, 0x74u32, 0x58u32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x41u32, 0x74u32, 0x58u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x61u32, 0x74u32, 0x79u32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x61u32, 0x74u32, 0x79u32]);
    }
    if u32s_eq(name, l) {
        // | pointsaty | pointsAtY |
        let v = vec![0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x41u32, 0x74u32, 0x59u32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x41u32, 0x74u32, 0x59u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x61u32, 0x74u32, 0x7au32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x61u32, 0x74u32, 0x7au32]);
    }
    if u32s_eq(name, l) {
        // | pointsatz | pointsAtZ |
        let v = vec![0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x41u32, 0x74u32, 0x5au32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x73u32, 0x41u32, 0x74u32, 0x5au32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x72u32, 0x65u32, 0x73u32, 0x65u32, 0x72u32, 0x76u32, 0x65u32, 0x61u32, 0x6cu32, 0x70u32, 0x68u32, 0x61u32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x72u32, 0x65u32, 0x73u32, 0x65u32, 0x72u32, 0x76u32, 0x65u32, 0x61u32, 0x6cu32, 0x70u32, 0x68u32, 0x61u32]);
    }
    if u32s_eq(name, l) {
        // | preservealpha | preserveAlpha |
        let v = vec![0x70u32, 0x72u32, 0x65u32, 0x73u32, 0x65u32, 0x72u32, 0x76u32, 0x65u32, 0x41u32, 0x6cu32, 0x70u32, 0x68u32, 0x61u32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x72u32, 0x65u32, 0x73u32, 0x65u32, 0x72u32, 0x76u32, 0x65u32, 0x41u32, 0x6cu32, 0x70u32, 0x68u32, 0x61u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x72u32, 0x65u32, 0x73u32, 0x65u32, 0x72u32, 0x76u32, 0x65u32, 0x61u32, 0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x74u32, 0x72u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x72u32, 0x65u32, 0x73u32, 0x65u32, 0x72u32, 0x76u32, 0x65u32, 0x61u32, 0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x74u32, 0x72u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32]);
    }
    if u32s_eq(name, l) {
        // | preserveaspectratio | preserveAspectRatio |
        let v = vec![0x70u32, 0x72u32, 0x65u32, 0x73u32, 0x65u32, 0x72u32, 0x76u32, 0x65u32, 0x41u32, 0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x74u32, 0x52u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x72u32, 0x65u32, 0x73u32, 0x65u32, 0x72u32, 0x76u32, 0x65u32, 0x41u32, 0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x74u32, 0x52u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x70u32, 0x72u32, 0x69u32, 0x6du32, 0x69u32, 0x74u32, 0x69u32, 0x76u32, 0x65u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x70u32, 0x72u32, 0x69u32, 0x6du32, 0x69u32, 0x74u32, 0x69u32, 0x76u32, 0x65u32, 0x75u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | primitiveunits | primitiveUnits |
        let v = vec![0x70u32, 0x72u32, 0x69u32, 0x6du32, 0x69u32, 0x74u32, 0x69u32, 0x76u32, 0x65u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x70u32, 0x72u32, 0x69u32, 0x6du32, 0x69u32, 0x74u32, 0x69u32, 0x76u32, 0x65u32, 0x55u32, 0x6eu32, 0x69u32, 0x74u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x72u32, 0x65u32, 0x66u32, 0x78u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x65u32, 0x66u32, 0x78u32]);
    }
    if u32s_eq(name, l) {
        // | refx | refX |
        let v = vec![0x72u32, 0x65u32, 0x66u32, 0x58u32];
        proof {
            assert(v@ =~= seq![0x72u32, 0x65u32, 0x66u32, 0x58u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x72u32, 0x65u32, 0x66u32, 0x79u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x65u32, 0x66u32, 0x79u32]);
    }
    if u32s_eq(name, l) {
        // | refy | refY |
        let v = vec![0x72u32, 0x65u32, 0x66u32, 0x59u32];
        proof {
            assert(v@ =~= seq![0x72u32, 0x65u32, 0x66u32, 0x59u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x72u32, 0x65u32, 0x70u32, 0x65u32, 0x61u32, 0x74u32, 0x63u32, 0x6fu32, 0x75u32, 0x6eu32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x65u32, 0x70u32, 0x65u32, 0x61u32, 0x74u32, 0x63u32, 0x6fu32, 0x75u32, 0x6eu32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | repeatcount | repeatCount |
        let v = vec![0x72u32, 0x65u32, 0x70u32, 0x65u32, 0x61u32, 0x74u32, 0x43u32, 0x6fu32, 0x75u32, 0x6eu32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x72u32, 0x65u32, 0x70u32, 0x65u32, 0x61u32, 0x74u32, 0x43u32, 0x6fu32, 0x75u32, 0x6eu32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x72u32, 0x65u32, 0x70u32, 0x65u32, 0x61u32, 0x74u32, 0x64u32, 0x75u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x65u32, 0x70u32, 0x65u32, 0x61u32, 0x74u32, 0x64u32, 0x75u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // | repeatdur | repeatDur |
        let v = vec![0x72u32, 0x65u32, 0x70u32, 0x65u32, 0x61u32, 0x74u32, 0x44u32, 0x75u32, 0x72u32];
        proof {
            assert(v@ =~= seq![0x72u32, 0x65u32, 0x70u32, 0x65u32, 0x61u32, 0x74u32, 0x44u32, 0x75u32, 0x72u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x69u32, 0x72u32, 0x65u32, 0x64u32, 0x65u32, 0x78u32, 0x74u32, 0x65u32, 0x6eu32, 0x73u32, 0x69u32, 0x6fu32, 0x6eu32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x69u32, 0x72u32, 0x65u32, 0x64u32, 0x65u32, 0x78u32, 0x74u32, 0x65u32, 0x6eu32, 0x73u32, 0x69u32, 0x6fu32, 0x6eu32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | requiredextensions | requiredExtensions |
        let v = vec![0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x69u32, 0x72u32, 0x65u32, 0x64u32, 0x45u32, 0x78u32, 0x74u32, 0x65u32, 0x6eu32, 0x73u32, 0x69u32, 0x6fu32, 0x6eu32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x69u32, 0x72u32, 0x65u32, 0x64u32, 0x45u32, 0x78u32, 0x74u32, 0x65u32, 0x6eu32, 0x73u32, 0x69u32, 0x6fu32, 0x6eu32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x69u32, 0x72u32, 0x65u32, 0x64u32, 0x66u32, 0x65u32, 0x61u32, 0x74u32, 0x75u32, 0x72u32, 0x65u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x69u32, 0x72u32, 0x65u32, 0x64u32, 0x66u32, 0x65u32, 0x61u32, 0x74u32, 0x75u32, 0x72u32, 0x65u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | requiredfeatures | requiredFeatures |
        let v = vec![0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x69u32, 0x72u32, 0x65u32, 0x64u32, 0x46u32, 0x65u32, 0x61u32, 0x74u32, 0x75u32, 0x72u32, 0x65u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x72u32, 0x65u32, 0x71u32, 0x75u32, 0x69u32, 0x72u32, 0x65u32, 0x64u32, 0x46u32, 0x65u32, 0x61u32, 0x74u32, 0x75u32, 0x72u32, 0x65u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x63u32, 0x6fu32, 0x6eu32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x63u32, 0x6fu32, 0x6eu32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | specularconstant | specularConstant |
        let v = vec![0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x43u32, 0x6fu32, 0x6eu32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x43u32, 0x6fu32, 0x6eu32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x65u32, 0x78u32, 0x70u32, 0x6fu32, 0x6eu32, 0x65u32, 0x6eu32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x65u32, 0x78u32, 0x70u32, 0x6fu32, 0x6eu32, 0x65u32, 0x6eu32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | specularexponent | specularExponent |
        let v = vec![0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x45u32, 0x78u32, 0x70u32, 0x6fu32, 0x6eu32, 0x65u32, 0x6eu32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x45u32, 0x78u32, 0x70u32, 0x6fu32, 0x6eu32, 0x65u32, 0x6eu32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x73u32, 0x70u32, 0x72u32, 0x65u32, 0x61u32, 0x64u32, 0x6du32, 0x65u32, 0x74u32, 0x68u32, 0x6fu32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x70u32, 0x72u32, 0x65u32, 0x61u32, 0x64u32, 0x6du32, 0x65u32, 0x74u32, 0x68u32, 0x6fu32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // | spreadmethod | spreadMethod |
        let v = vec![0x73u32, 0x70u32, 0x72u32, 0x65u32, 0x61u32, 0x64u32, 0x4du32, 0x65u32, 0x74u32, 0x68u32, 0x6fu32, 0x64u32];
        proof {
            assert(v@ =~= seq![0x73u32, 0x70u32, 0x72u32, 0x65u32, 0x61u32, 0x64u32, 0x4du32, 0x65u32, 0x74u32, 0x68u32, 0x6fu32, 0x64u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x73u32, 0x74u32, 0x61u32, 0x72u32, 0x74u32, 0x6fu32, 0x66u32, 0x66u32, 0x73u32, 0x65u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x74u32, 0x61u32, 0x72u32, 0x74u32, 0x6fu32, 0x66u32, 0x66u32, 0x73u32, 0x65u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | startoffset | startOffset |
        let v = vec![0x73u32, 0x74u32, 0x61u32, 0x72u32, 0x74u32, 0x4fu32, 0x66u32, 0x66u32, 0x73u32, 0x65u32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x73u32, 0x74u32, 0x61u32, 0x72u32, 0x74u32, 0x4fu32, 0x66u32, 0x66u32, 0x73u32, 0x65u32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x73u32, 0x74u32, 0x64u32, 0x64u32, 0x65u32, 0x76u32, 0x69u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x74u32, 0x64u32, 0x64u32, 0x65u32, 0x76u32, 0x69u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // | stddeviation | stdDeviation |
        let v = vec![0x73u32, 0x74u32, 0x64u32, 0x44u32, 0x65u32, 0x76u32, 0x69u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32];
        proof {
            assert(v@ =~= seq![0x73u32, 0x74u32, 0x64u32, 0x44u32, 0x65u32, 0x76u32, 0x69u32, 0x61u32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x73u32, 0x74u32, 0x69u32, 0x74u32, 0x63u32, 0x68u32, 0x74u32, 0x69u32, 0x6cu32, 0x65u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x74u32, 0x69u32, 0x74u32, 0x63u32, 0x68u32, 0x74u32, 0x69u32, 0x6cu32, 0x65u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | stitchtiles | stitchTiles |
        let v = vec![0x73u32, 0x74u32, 0x69u32, 0x74u32, 0x63u32, 0x68u32, 0x54u32, 0x69u32, 0x6cu32, 0x65u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x73u32, 0x74u32, 0x69u32, 0x74u32, 0x63u32, 0x68u32, 0x54u32, 0x69u32, 0x6cu32, 0x65u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x73u32, 0x75u32, 0x72u32, 0x66u32, 0x61u32, 0x63u32, 0x65u32, 0x73u32, 0x63u32, 0x61u32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x75u32, 0x72u32, 0x66u32, 0x61u32, 0x63u32, 0x65u32, 0x73u32, 0x63u32, 0x61u32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | surfacescale | surfaceScale |
        let v = vec![0x73u32, 0x75u32, 0x72u32, 0x66u32, 0x61u32, 0x63u32, 0x65u32, 0x53u32, 0x63u32, 0x61u32, 0x6cu32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x73u32, 0x75u32, 0x72u32, 0x66u32, 0x61u32, 0x63u32, 0x65u32, 0x53u32, 0x63u32, 0x61u32, 0x6cu32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x73u32, 0x79u32, 0x73u32, 0x74u32, 0x65u32, 0x6du32, 0x6cu32, 0x61u32, 0x6eu32, 0x67u32, 0x75u32, 0x61u32, 0x67u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x73u32, 0x79u32, 0x73u32, 0x74u32, 0x65u32, 0x6du32, 0x6cu32, 0x61u32, 0x6eu32, 0x67u32, 0x75u32, 0x61u32, 0x67u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | systemlanguage | systemLanguage |
        let v = vec![0x73u32, 0x79u32, 0x73u32, 0x74u32, 0x65u32, 0x6du32, 0x4cu32, 0x61u32, 0x6eu32, 0x67u32, 0x75u32, 0x61u32, 0x67u32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x73u32, 0x79u32, 0x73u32, 0x74u32, 0x65u32, 0x6du32, 0x4cu32, 0x61u32, 0x6eu32, 0x67u32, 0x75u32, 0x61u32, 0x67u32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x74u32, 0x61u32, 0x62u32, 0x6cu32, 0x65u32, 0x76u32, 0x61u32, 0x6cu32, 0x75u32, 0x65u32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x61u32, 0x62u32, 0x6cu32, 0x65u32, 0x76u32, 0x61u32, 0x6cu32, 0x75u32, 0x65u32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | tablevalues | tableValues |
        let v = vec![0x74u32, 0x61u32, 0x62u32, 0x6cu32, 0x65u32, 0x56u32, 0x61u32, 0x6cu32, 0x75u32, 0x65u32, 0x73u32];
        proof {
            assert(v@ =~= seq![0x74u32, 0x61u32, 0x62u32, 0x6cu32, 0x65u32, 0x56u32, 0x61u32, 0x6cu32, 0x75u32, 0x65u32, 0x73u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32, 0x78u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32, 0x78u32]);
    }
    if u32s_eq(name, l) {
        // | targetx | targetX |
        let v = vec![0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32, 0x58u32];
        proof {
            assert(v@ =~= seq![0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32, 0x58u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32, 0x79u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32, 0x79u32]);
    }
    if u32s_eq(name, l) {
        // | targety | targetY |
        let v = vec![0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32, 0x59u32];
        proof {
            assert(v@ =~= seq![0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32, 0x59u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x6cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // | textlength | textLength |
        let v = vec![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x4cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32];
        proof {
            assert(v@ =~= seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x4cu32, 0x65u32, 0x6eu32, 0x67u32, 0x74u32, 0x68u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x76u32, 0x69u32, 0x65u32, 0x77u32, 0x62u32, 0x6fu32, 0x78u32];
    proof {
        assert(l@ =~= seq![0x76u32, 0x69u32, 0x65u32, 0x77u32, 0x62u32, 0x6fu32, 0x78u32]);
    }
    if u32s_eq(name, l) {
        // | viewbox | viewBox |
        let v = vec![0x76u32, 0x69u32, 0x65u32, 0x77u32, 0x42u32, 0x6fu32, 0x78u32];
        proof {
            assert(v@ =~= seq![0x76u32, 0x69u32, 0x65u32, 0x77u32, 0x42u32, 0x6fu32, 0x78u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x76u32, 0x69u32, 0x65u32, 0x77u32, 0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x76u32, 0x69u32, 0x65u32, 0x77u32, 0x74u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | viewtarget | viewTarget |
        let v = vec![0x76u32, 0x69u32, 0x65u32, 0x77u32, 0x54u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x76u32, 0x69u32, 0x65u32, 0x77u32, 0x54u32, 0x61u32, 0x72u32, 0x67u32, 0x65u32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x78u32, 0x63u32, 0x68u32, 0x61u32, 0x6eu32, 0x6eu32, 0x65u32, 0x6cu32, 0x73u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32, 0x6fu32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x63u32, 0x68u32, 0x61u32, 0x6eu32, 0x6eu32, 0x65u32, 0x6cu32, 0x73u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32, 0x6fu32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // | xchannelselector | xChannelSelector |
        let v = vec![0x78u32, 0x43u32, 0x68u32, 0x61u32, 0x6eu32, 0x6eu32, 0x65u32, 0x6cu32, 0x53u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32, 0x6fu32, 0x72u32];
        proof {
            assert(v@ =~= seq![0x78u32, 0x43u32, 0x68u32, 0x61u32, 0x6eu32, 0x6eu32, 0x65u32, 0x6cu32, 0x53u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32, 0x6fu32, 0x72u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x79u32, 0x63u32, 0x68u32, 0x61u32, 0x6eu32, 0x6eu32, 0x65u32, 0x6cu32, 0x73u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32, 0x6fu32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x79u32, 0x63u32, 0x68u32, 0x61u32, 0x6eu32, 0x6eu32, 0x65u32, 0x6cu32, 0x73u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32, 0x6fu32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // | ychannelselector | yChannelSelector |
        let v = vec![0x79u32, 0x43u32, 0x68u32, 0x61u32, 0x6eu32, 0x6eu32, 0x65u32, 0x6cu32, 0x53u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32, 0x6fu32, 0x72u32];
        proof {
            assert(v@ =~= seq![0x79u32, 0x43u32, 0x68u32, 0x61u32, 0x6eu32, 0x6eu32, 0x65u32, 0x6cu32, 0x53u32, 0x65u32, 0x6cu32, 0x65u32, 0x63u32, 0x74u32, 0x6fu32, 0x72u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x7au32, 0x6fu32, 0x6fu32, 0x6du32, 0x61u32, 0x6eu32, 0x64u32, 0x70u32, 0x61u32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x7au32, 0x6fu32, 0x6fu32, 0x6du32, 0x61u32, 0x6eu32, 0x64u32, 0x70u32, 0x61u32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // | zoomandpan | zoomAndPan |
        let v = vec![0x7au32, 0x6fu32, 0x6fu32, 0x6du32, 0x41u32, 0x6eu32, 0x64u32, 0x50u32, 0x61u32, 0x6eu32];
        proof {
            assert(v@ =~= seq![0x7au32, 0x6fu32, 0x6fu32, 0x6du32, 0x41u32, 0x6eu32, 0x64u32, 0x50u32, 0x61u32, 0x6eu32]);
        }
        return Some(v);
    }
    None
}

/// [`svg_tag_name`]: `Some` of the new name for a name in the table,
/// `None` for a name it keeps.
pub fn svg_tag_name_exec(name: &[u32]) -> (r: Option<Vec<u32>>)
    ensures
        match r {
            Some(v) => v@ == svg_tag_name(name@),
            None => svg_tag_name(name@) == name@,
        },
{
    let l: &[u32] = &[0x61u32, 0x6cu32, 0x74u32, 0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x6cu32, 0x74u32, 0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // | altglyph | altGlyph |
        let v = vec![0x61u32, 0x6cu32, 0x74u32, 0x47u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32];
        proof {
            assert(v@ =~= seq![0x61u32, 0x6cu32, 0x74u32, 0x47u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x61u32, 0x6cu32, 0x74u32, 0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x64u32, 0x65u32, 0x66u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x6cu32, 0x74u32, 0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x64u32, 0x65u32, 0x66u32]);
    }
    if u32s_eq(name, l) {
        // | altglyphdef | altGlyphDef |
        let v = vec![0x61u32, 0x6cu32, 0x74u32, 0x47u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x44u32, 0x65u32, 0x66u32];
        proof {
            assert(v@ =~= seq![0x61u32, 0x6cu32, 0x74u32, 0x47u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x44u32, 0x65u32, 0x66u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x61u32, 0x6cu32, 0x74u32, 0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x69u32, 0x74u32, 0x65u32, 0x6du32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x6cu32, 0x74u32, 0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x69u32, 0x74u32, 0x65u32, 0x6du32]);
    }
    if u32s_eq(name, l) {
        // | altglyphitem | altGlyphItem |
        let v = vec![0x61u32, 0x6cu32, 0x74u32, 0x47u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x49u32, 0x74u32, 0x65u32, 0x6du32];
        proof {
            assert(v@ =~= seq![0x61u32, 0x6cu32, 0x74u32, 0x47u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x49u32, 0x74u32, 0x65u32, 0x6du32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x63u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x63u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // | animatecolor | animateColor |
        let v = vec![0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x43u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x72u32];
        proof {
            assert(v@ =~= seq![0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x43u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x72u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x6du32, 0x6fu32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x6du32, 0x6fu32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32]);
    }
    if u32s_eq(name, l) {
        // | animatemotion | animateMotion |
        let v = vec![0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x4du32, 0x6fu32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32];
        proof {
            assert(v@ =~= seq![0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x4du32, 0x6fu32, 0x74u32, 0x69u32, 0x6fu32, 0x6eu32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x74u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32];
    proof {
        assert(l@ =~= seq![0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x74u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32]);
    }
    if u32s_eq(name, l) {
        // | animatetransform | animateTransform |
        let v = vec![0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x54u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32];
        proof {
            assert(v@ =~= seq![0x61u32, 0x6eu32, 0x69u32, 0x6du32, 0x61u32, 0x74u32, 0x65u32, 0x54u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x6fu32, 0x72u32, 0x6du32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x63u32, 0x6cu32, 0x69u32, 0x70u32, 0x70u32, 0x61u32, 0x74u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x63u32, 0x6cu32, 0x69u32, 0x70u32, 0x70u32, 0x61u32, 0x74u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // | clippath | clipPath |
        let v = vec![0x63u32, 0x6cu32, 0x69u32, 0x70u32, 0x50u32, 0x61u32, 0x74u32, 0x68u32];
        proof {
            assert(v@ =~= seq![0x63u32, 0x6cu32, 0x69u32, 0x70u32, 0x50u32, 0x61u32, 0x74u32, 0x68u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x62u32, 0x6cu32, 0x65u32, 0x6eu32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x62u32, 0x6cu32, 0x65u32, 0x6eu32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // | feblend | feBlend |
        let v = vec![0x66u32, 0x65u32, 0x42u32, 0x6cu32, 0x65u32, 0x6eu32, 0x64u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x42u32, 0x6cu32, 0x65u32, 0x6eu32, 0x64u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x63u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x72u32, 0x6du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x63u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x72u32, 0x6du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32]);
    }
    if u32s_eq(name, l) {
        // | fecolormatrix | feColorMatrix |
        let v = vec![0x66u32, 0x65u32, 0x43u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x72u32, 0x4du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x43u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x72u32, 0x4du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x63u32, 0x6fu32, 0x6du32, 0x70u32, 0x6fu32, 0x6eu32, 0x65u32, 0x6eu32, 0x74u32, 0x74u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x65u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x63u32, 0x6fu32, 0x6du32, 0x70u32, 0x6fu32, 0x6eu32, 0x65u32, 0x6eu32, 0x74u32, 0x74u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x65u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // | fecomponenttransfer | feComponentTransfer |
        let v = vec![0x66u32, 0x65u32, 0x43u32, 0x6fu32, 0x6du32, 0x70u32, 0x6fu32, 0x6eu32, 0x65u32, 0x6eu32, 0x74u32, 0x54u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x65u32, 0x72u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x43u32, 0x6fu32, 0x6du32, 0x70u32, 0x6fu32, 0x6eu32, 0x65u32, 0x6eu32, 0x74u32, 0x54u32, 0x72u32, 0x61u32, 0x6eu32, 0x73u32, 0x66u32, 0x65u32, 0x72u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x63u32, 0x6fu32, 0x6du32, 0x70u32, 0x6fu32, 0x73u32, 0x69u32, 0x74u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x63u32, 0x6fu32, 0x6du32, 0x70u32, 0x6fu32, 0x73u32, 0x69u32, 0x74u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | fecomposite | feComposite |
        let v = vec![0x66u32, 0x65u32, 0x43u32, 0x6fu32, 0x6du32, 0x70u32, 0x6fu32, 0x73u32, 0x69u32, 0x74u32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x43u32, 0x6fu32, 0x6du32, 0x70u32, 0x6fu32, 0x73u32, 0x69u32, 0x74u32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x63u32, 0x6fu32, 0x6eu32, 0x76u32, 0x6fu32, 0x6cu32, 0x76u32, 0x65u32, 0x6du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x63u32, 0x6fu32, 0x6eu32, 0x76u32, 0x6fu32, 0x6cu32, 0x76u32, 0x65u32, 0x6du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32]);
    }
    if u32s_eq(name, l) {
        // | feconvolvematrix | feConvolveMatrix |
        let v = vec![0x66u32, 0x65u32, 0x43u32, 0x6fu32, 0x6eu32, 0x76u32, 0x6fu32, 0x6cu32, 0x76u32, 0x65u32, 0x4du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x43u32, 0x6fu32, 0x6eu32, 0x76u32, 0x6fu32, 0x6cu32, 0x76u32, 0x65u32, 0x4du32, 0x61u32, 0x74u32, 0x72u32, 0x69u32, 0x78u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x64u32, 0x69u32, 0x66u32, 0x66u32, 0x75u32, 0x73u32, 0x65u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x64u32, 0x69u32, 0x66u32, 0x66u32, 0x75u32, 0x73u32, 0x65u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // | fediffuselighting | feDiffuseLighting |
        let v = vec![0x66u32, 0x65u32, 0x44u32, 0x69u32, 0x66u32, 0x66u32, 0x75u32, 0x73u32, 0x65u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x44u32, 0x69u32, 0x66u32, 0x66u32, 0x75u32, 0x73u32, 0x65u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x64u32, 0x69u32, 0x73u32, 0x70u32, 0x6cu32, 0x61u32, 0x63u32, 0x65u32, 0x6du32, 0x65u32, 0x6eu32, 0x74u32, 0x6du32, 0x61u32, 0x70u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x64u32, 0x69u32, 0x73u32, 0x70u32, 0x6cu32, 0x61u32, 0x63u32, 0x65u32, 0x6du32, 0x65u32, 0x6eu32, 0x74u32, 0x6du32, 0x61u32, 0x70u32]);
    }
    if u32s_eq(name, l) {
        // | fedisplacementmap | feDisplacementMap |
        let v = vec![0x66u32, 0x65u32, 0x44u32, 0x69u32, 0x73u32, 0x70u32, 0x6cu32, 0x61u32, 0x63u32, 0x65u32, 0x6du32, 0x65u32, 0x6eu32, 0x74u32, 0x4du32, 0x61u32, 0x70u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x44u32, 0x69u32, 0x73u32, 0x70u32, 0x6cu32, 0x61u32, 0x63u32, 0x65u32, 0x6du32, 0x65u32, 0x6eu32, 0x74u32, 0x4du32, 0x61u32, 0x70u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x64u32, 0x69u32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x64u32, 0x69u32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | fedistantlight | feDistantLight |
        let v = vec![0x66u32, 0x65u32, 0x44u32, 0x69u32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x44u32, 0x69u32, 0x73u32, 0x74u32, 0x61u32, 0x6eu32, 0x74u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x64u32, 0x72u32, 0x6fu32, 0x70u32, 0x73u32, 0x68u32, 0x61u32, 0x64u32, 0x6fu32, 0x77u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x64u32, 0x72u32, 0x6fu32, 0x70u32, 0x73u32, 0x68u32, 0x61u32, 0x64u32, 0x6fu32, 0x77u32]);
    }
    if u32s_eq(name, l) {
        // | fedropshadow | feDropShadow |
        let v = vec![0x66u32, 0x65u32, 0x44u32, 0x72u32, 0x6fu32, 0x70u32, 0x53u32, 0x68u32, 0x61u32, 0x64u32, 0x6fu32, 0x77u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x44u32, 0x72u32, 0x6fu32, 0x70u32, 0x53u32, 0x68u32, 0x61u32, 0x64u32, 0x6fu32, 0x77u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x66u32, 0x6cu32, 0x6fu32, 0x6fu32, 0x64u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x66u32, 0x6cu32, 0x6fu32, 0x6fu32, 0x64u32]);
    }
    if u32s_eq(name, l) {
        // | feflood | feFlood |
        let v = vec![0x66u32, 0x65u32, 0x46u32, 0x6cu32, 0x6fu32, 0x6fu32, 0x64u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x46u32, 0x6cu32, 0x6fu32, 0x6fu32, 0x64u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x66u32, 0x75u32, 0x6eu32, 0x63u32, 0x61u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x66u32, 0x75u32, 0x6eu32, 0x63u32, 0x61u32]);
    }
    if u32s_eq(name, l) {
        // | fefunca | feFuncA |
        let v = vec![0x66u32, 0x65u32, 0x46u32, 0x75u32, 0x6eu32, 0x63u32, 0x41u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x46u32, 0x75u32, 0x6eu32, 0x63u32, 0x41u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x66u32, 0x75u32, 0x6eu32, 0x63u32, 0x62u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x66u32, 0x75u32, 0x6eu32, 0x63u32, 0x62u32]);
    }
    if u32s_eq(name, l) {
        // | fefuncb | feFuncB |
        let v = vec![0x66u32, 0x65u32, 0x46u32, 0x75u32, 0x6eu32, 0x63u32, 0x42u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x46u32, 0x75u32, 0x6eu32, 0x63u32, 0x42u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x66u32, 0x75u32, 0x6eu32, 0x63u32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x66u32, 0x75u32, 0x6eu32, 0x63u32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // | fefuncg | feFuncG |
        let v = vec![0x66u32, 0x65u32, 0x46u32, 0x75u32, 0x6eu32, 0x63u32, 0x47u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x46u32, 0x75u32, 0x6eu32, 0x63u32, 0x47u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x66u32, 0x75u32, 0x6eu32, 0x63u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x66u32, 0x75u32, 0x6eu32, 0x63u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // | fefuncr | feFuncR |
        let v = vec![0x66u32, 0x65u32, 0x46u32, 0x75u32, 0x6eu32, 0x63u32, 0x52u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x46u32, 0x75u32, 0x6eu32, 0x63u32, 0x52u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x67u32, 0x61u32, 0x75u32, 0x73u32, 0x73u32, 0x69u32, 0x61u32, 0x6eu32, 0x62u32, 0x6cu32, 0x75u32, 0x72u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x67u32, 0x61u32, 0x75u32, 0x73u32, 0x73u32, 0x69u32, 0x61u32, 0x6eu32, 0x62u32, 0x6cu32, 0x75u32, 0x72u32]);
    }
    if u32s_eq(name, l) {
        // | fegaussianblur | feGaussianBlur |
        let v = vec![0x66u32, 0x65u32, 0x47u32, 0x61u32, 0x75u32, 0x73u32, 0x73u32, 0x69u32, 0x61u32, 0x6eu32, 0x42u32, 0x6cu32, 0x75u32, 0x72u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x47u32, 0x61u32, 0x75u32, 0x73u32, 0x73u32, 0x69u32, 0x61u32, 0x6eu32, 0x42u32, 0x6cu32, 0x75u32, 0x72u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x69u32, 0x6du32, 0x61u32, 0x67u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x69u32, 0x6du32, 0x61u32, 0x67u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | feimage | feImage |
        let v = vec![0x66u32, 0x65u32, 0x49u32, 0x6du32, 0x61u32, 0x67u32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x49u32, 0x6du32, 0x61u32, 0x67u32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x6du32, 0x65u32, 0x72u32, 0x67u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x6du32, 0x65u32, 0x72u32, 0x67u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | femerge | feMerge |
        let v = vec![0x66u32, 0x65u32, 0x4du32, 0x65u32, 0x72u32, 0x67u32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x4du32, 0x65u32, 0x72u32, 0x67u32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x6du32, 0x65u32, 0x72u32, 0x67u32, 0x65u32, 0x6eu32, 0x6fu32, 0x64u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x6du32, 0x65u32, 0x72u32, 0x67u32, 0x65u32, 0x6eu32, 0x6fu32, 0x64u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | femergenode | feMergeNode |
        let v = vec![0x66u32, 0x65u32, 0x4du32, 0x65u32, 0x72u32, 0x67u32, 0x65u32, 0x4eu32, 0x6fu32, 0x64u32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x4du32, 0x65u32, 0x72u32, 0x67u32, 0x65u32, 0x4eu32, 0x6fu32, 0x64u32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x6du32, 0x6fu32, 0x72u32, 0x70u32, 0x68u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x67u32, 0x79u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x6du32, 0x6fu32, 0x72u32, 0x70u32, 0x68u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x67u32, 0x79u32]);
    }
    if u32s_eq(name, l) {
        // | femorphology | feMorphology |
        let v = vec![0x66u32, 0x65u32, 0x4du32, 0x6fu32, 0x72u32, 0x70u32, 0x68u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x67u32, 0x79u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x4du32, 0x6fu32, 0x72u32, 0x70u32, 0x68u32, 0x6fu32, 0x6cu32, 0x6fu32, 0x67u32, 0x79u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x6fu32, 0x66u32, 0x66u32, 0x73u32, 0x65u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x6fu32, 0x66u32, 0x66u32, 0x73u32, 0x65u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | feoffset | feOffset |
        let v = vec![0x66u32, 0x65u32, 0x4fu32, 0x66u32, 0x66u32, 0x73u32, 0x65u32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x4fu32, 0x66u32, 0x66u32, 0x73u32, 0x65u32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x70u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | fepointlight | fePointLight |
        let v = vec![0x66u32, 0x65u32, 0x50u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x50u32, 0x6fu32, 0x69u32, 0x6eu32, 0x74u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x73u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // | fespecularlighting | feSpecularLighting |
        let v = vec![0x66u32, 0x65u32, 0x53u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x53u32, 0x70u32, 0x65u32, 0x63u32, 0x75u32, 0x6cu32, 0x61u32, 0x72u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32, 0x69u32, 0x6eu32, 0x67u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x73u32, 0x70u32, 0x6fu32, 0x74u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x73u32, 0x70u32, 0x6fu32, 0x74u32, 0x6cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | fespotlight | feSpotLight |
        let v = vec![0x66u32, 0x65u32, 0x53u32, 0x70u32, 0x6fu32, 0x74u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x53u32, 0x70u32, 0x6fu32, 0x74u32, 0x4cu32, 0x69u32, 0x67u32, 0x68u32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x74u32, 0x69u32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x74u32, 0x69u32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | fetile | feTile |
        let v = vec![0x66u32, 0x65u32, 0x54u32, 0x69u32, 0x6cu32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x54u32, 0x69u32, 0x6cu32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x65u32, 0x74u32, 0x75u32, 0x72u32, 0x62u32, 0x75u32, 0x6cu32, 0x65u32, 0x6eu32, 0x63u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x65u32, 0x74u32, 0x75u32, 0x72u32, 0x62u32, 0x75u32, 0x6cu32, 0x65u32, 0x6eu32, 0x63u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | feturbulence | feTurbulence |
        let v = vec![0x66u32, 0x65u32, 0x54u32, 0x75u32, 0x72u32, 0x62u32, 0x75u32, 0x6cu32, 0x65u32, 0x6eu32, 0x63u32, 0x65u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x65u32, 0x54u32, 0x75u32, 0x72u32, 0x62u32, 0x75u32, 0x6cu32, 0x65u32, 0x6eu32, 0x63u32, 0x65u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x6fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x6fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | foreignobject | foreignObject |
        let v = vec![0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x4fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x66u32, 0x6fu32, 0x72u32, 0x65u32, 0x69u32, 0x67u32, 0x6eu32, 0x4fu32, 0x62u32, 0x6au32, 0x65u32, 0x63u32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x72u32, 0x65u32, 0x66u32];
    proof {
        assert(l@ =~= seq![0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x72u32, 0x65u32, 0x66u32]);
    }
    if u32s_eq(name, l) {
        // | glyphref | glyphRef |
        let v = vec![0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x52u32, 0x65u32, 0x66u32];
        proof {
            assert(v@ =~= seq![0x67u32, 0x6cu32, 0x79u32, 0x70u32, 0x68u32, 0x52u32, 0x65u32, 0x66u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x6cu32, 0x69u32, 0x6eu32, 0x65u32, 0x61u32, 0x72u32, 0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x6cu32, 0x69u32, 0x6eu32, 0x65u32, 0x61u32, 0x72u32, 0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | lineargradient | linearGradient |
        let v = vec![0x6cu32, 0x69u32, 0x6eu32, 0x65u32, 0x61u32, 0x72u32, 0x47u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x6cu32, 0x69u32, 0x6eu32, 0x65u32, 0x61u32, 0x72u32, 0x47u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x61u32, 0x6cu32, 0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32];
    proof {
        assert(l@ =~= seq![0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x61u32, 0x6cu32, 0x67u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32]);
    }
    if u32s_eq(name, l) {
        // | radialgradient | radialGradient |
        let v = vec![0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x61u32, 0x6cu32, 0x47u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32];
        proof {
            assert(v@ =~= seq![0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x61u32, 0x6cu32, 0x47u32, 0x72u32, 0x61u32, 0x64u32, 0x69u32, 0x65u32, 0x6eu32, 0x74u32]);
        }
        return Some(v);
    }
    let l: &[u32] = &[0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x70u32, 0x61u32, 0x74u32, 0x68u32];
    proof {
        assert(l@ =~= seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x70u32, 0x61u32, 0x74u32, 0x68u32]);
    }
    if u32s_eq(name, l) {
        // | textpath | textPath |
        let v = vec![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x50u32, 0x61u32, 0x74u32, 0x68u32];
        proof {
            assert(v@ =~= seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x50u32, 0x61u32, 0x74u32, 0x68u32]);
        }
        return Some(v);
    }
    None
}

/// The view of a row of the foreign attribute table.
pub open spec fn foreign_row_view(r: Option<(Option<Vec<u32>>, Vec<u32>, Namespace)>) -> Option<(Option<Seq<u32>>, Seq<u32>, Namespace)> {
    match r {
        Some((p, l, n)) => Some((clazel_dom::exec::opt_str_view(p), l@, n)),
        None => None,
    }
}

/// [`foreign_attribute`].
pub fn foreign_attribute_exec(name: &[u32]) -> (r: Option<(Option<Vec<u32>>, Vec<u32>, Namespace)>)
    ensures
        foreign_row_view(r) == foreign_attribute(name@),
{
    let l: &[u32] = &[0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x61u32, 0x63u32, 0x74u32, 0x75u32, 0x61u32, 0x74u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x61u32, 0x63u32, 0x74u32, 0x75u32, 0x61u32, 0x74u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | xlink:actuate | xlink | actuate | XLink namespace |
        let lv = vec![0x61u32, 0x63u32, 0x74u32, 0x75u32, 0x61u32, 0x74u32, 0x65u32];
        proof {
            assert(lv@ =~= seq![0x61u32, 0x63u32, 0x74u32, 0x75u32, 0x61u32, 0x74u32, 0x65u32]);
        }
        let pv = vec![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
        }
        return Some((Some(pv), lv, Namespace::XLink));
    }
    let l: &[u32] = &[0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x61u32, 0x72u32, 0x63u32, 0x72u32, 0x6fu32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x61u32, 0x72u32, 0x63u32, 0x72u32, 0x6fu32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | xlink:arcrole | xlink | arcrole | XLink namespace |
        let lv = vec![0x61u32, 0x72u32, 0x63u32, 0x72u32, 0x6fu32, 0x6cu32, 0x65u32];
        proof {
            assert(lv@ =~= seq![0x61u32, 0x72u32, 0x63u32, 0x72u32, 0x6fu32, 0x6cu32, 0x65u32]);
        }
        let pv = vec![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
        }
        return Some((Some(pv), lv, Namespace::XLink));
    }
    let l: &[u32] = &[0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x68u32, 0x72u32, 0x65u32, 0x66u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x68u32, 0x72u32, 0x65u32, 0x66u32]);
    }
    if u32s_eq(name, l) {
        // | xlink:href | xlink | href | XLink namespace |
        let lv = vec![0x68u32, 0x72u32, 0x65u32, 0x66u32];
        proof {
            assert(lv@ =~= seq![0x68u32, 0x72u32, 0x65u32, 0x66u32]);
        }
        let pv = vec![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
        }
        return Some((Some(pv), lv, Namespace::XLink));
    }
    let l: &[u32] = &[0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x72u32, 0x6fu32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x72u32, 0x6fu32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | xlink:role | xlink | role | XLink namespace |
        let lv = vec![0x72u32, 0x6fu32, 0x6cu32, 0x65u32];
        proof {
            assert(lv@ =~= seq![0x72u32, 0x6fu32, 0x6cu32, 0x65u32]);
        }
        let pv = vec![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
        }
        return Some((Some(pv), lv, Namespace::XLink));
    }
    let l: &[u32] = &[0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x73u32, 0x68u32, 0x6fu32, 0x77u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x73u32, 0x68u32, 0x6fu32, 0x77u32]);
    }
    if u32s_eq(name, l) {
        // | xlink:show | xlink | show | XLink namespace |
        let lv = vec![0x73u32, 0x68u32, 0x6fu32, 0x77u32];
        proof {
            assert(lv@ =~= seq![0x73u32, 0x68u32, 0x6fu32, 0x77u32]);
        }
        let pv = vec![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
        }
        return Some((Some(pv), lv, Namespace::XLink));
    }
    let l: &[u32] = &[0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x74u32, 0x69u32, 0x74u32, 0x6cu32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x74u32, 0x69u32, 0x74u32, 0x6cu32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | xlink:title | xlink | title | XLink namespace |
        let lv = vec![0x74u32, 0x69u32, 0x74u32, 0x6cu32, 0x65u32];
        proof {
            assert(lv@ =~= seq![0x74u32, 0x69u32, 0x74u32, 0x6cu32, 0x65u32]);
        }
        let pv = vec![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
        }
        return Some((Some(pv), lv, Namespace::XLink));
    }
    let l: &[u32] = &[0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x74u32, 0x79u32, 0x70u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32, 0x3au32, 0x74u32, 0x79u32, 0x70u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | xlink:type | xlink | type | XLink namespace |
        let lv = vec![0x74u32, 0x79u32, 0x70u32, 0x65u32];
        proof {
            assert(lv@ =~= seq![0x74u32, 0x79u32, 0x70u32, 0x65u32]);
        }
        let pv = vec![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
        }
        return Some((Some(pv), lv, Namespace::XLink));
    }
    let l: &[u32] = &[0x78u32, 0x6du32, 0x6cu32, 0x3au32, 0x6cu32, 0x61u32, 0x6eu32, 0x67u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6du32, 0x6cu32, 0x3au32, 0x6cu32, 0x61u32, 0x6eu32, 0x67u32]);
    }
    if u32s_eq(name, l) {
        // | xml:lang | xml | lang | XML namespace |
        let lv = vec![0x6cu32, 0x61u32, 0x6eu32, 0x67u32];
        proof {
            assert(lv@ =~= seq![0x6cu32, 0x61u32, 0x6eu32, 0x67u32]);
        }
        let pv = vec![0x78u32, 0x6du32, 0x6cu32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6du32, 0x6cu32]);
        }
        return Some((Some(pv), lv, Namespace::Xml));
    }
    let l: &[u32] = &[0x78u32, 0x6du32, 0x6cu32, 0x3au32, 0x73u32, 0x70u32, 0x61u32, 0x63u32, 0x65u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6du32, 0x6cu32, 0x3au32, 0x73u32, 0x70u32, 0x61u32, 0x63u32, 0x65u32]);
    }
    if u32s_eq(name, l) {
        // | xml:space | xml | space | XML namespace |
        let lv = vec![0x73u32, 0x70u32, 0x61u32, 0x63u32, 0x65u32];
        proof {
            assert(lv@ =~= seq![0x73u32, 0x70u32, 0x61u32, 0x63u32, 0x65u32]);
        }
        let pv = vec![0x78u32, 0x6du32, 0x6cu32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6du32, 0x6cu32]);
        }
        return Some((Some(pv), lv, Namespace::Xml));
    }
    let l: &[u32] = &[0x78u32, 0x6du32, 0x6cu32, 0x6eu32, 0x73u32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6du32, 0x6cu32, 0x6eu32, 0x73u32]);
    }
    if u32s_eq(name, l) {
        // | xmlns | (none) | xmlns | XMLNS namespace |
        let lv = vec![0x78u32, 0x6du32, 0x6cu32, 0x6eu32, 0x73u32];
        proof {
            assert(lv@ =~= seq![0x78u32, 0x6du32, 0x6cu32, 0x6eu32, 0x73u32]);
        }
        return Some((None, lv, Namespace::Xmlns));
    }
    let l: &[u32] = &[0x78u32, 0x6du32, 0x6cu32, 0x6eu32, 0x73u32, 0x3au32, 0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
    proof {
        assert(l@ =~= seq![0x78u32, 0x6du32, 0x6cu32, 0x6eu32, 0x73u32, 0x3au32, 0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
    }
    if u32s_eq(name, l) {
        // | xmlns:xlink | xmlns | xlink | XMLNS namespace |
        let lv = vec![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32];
        proof {
            assert(lv@ =~= seq![0x78u32, 0x6cu32, 0x69u32, 0x6eu32, 0x6bu32]);
        }
        let pv = vec![0x78u32, 0x6du32, 0x6cu32, 0x6eu32, 0x73u32];
        proof {
            assert(pv@ =~= seq![0x78u32, 0x6du32, 0x6cu32, 0x6eu32, 0x73u32]);
        }
        return Some((Some(pv), lv, Namespace::Xmlns));
    }
    None
}

} // verus!
