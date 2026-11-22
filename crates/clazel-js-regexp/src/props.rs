//! The names `\p{..}` may use (§22.2.1.1†, CharacterClassEscape and
//! UnicodePropertyValueExpression early errors; §22.2.2.9† UnicodeMatchProperty
//! and UnicodeMatchPropertyValue).
//!
//! What is checked here, as exact, case-sensitive names (no loose matching):
//!
//! - `General_Category` / `gc` values: every canonical name and alias in the
//!   Unicode Character Database's `PropertyValueAliases.txt` for `gc`;
//! - the binary properties of ECMA-262's table "Binary Unicode property
//!   aliases and their canonical property names" (`Any`, `ASCII` and
//!   `Assigned` are the standard's own);
//! - the binary properties of strings (`v` mode), from the table of the same
//!   kind for strings.
//!
//! `Script` / `Script_Extensions` values are not listed here: there are about
//! 170 and they change with every Unicode version, so they belong to the
//! generated tables of item 7.10's second half. [`Names::is_script`] is where
//! they plug in; [`SyntaxOnly`] accepts every syntactically valid value.
//! `tests/conformance_names.rs` checks the lists below against the vendored
//! UCD files.

/// What the parser asks of the Unicode tables.
pub trait Names {
    /// Whether `value` is a canonical script name or alias (a value of the
    /// `Script` property in `PropertyValueAliases.txt`), for `\p{sc=value}`
    /// and `\p{scx=value}`.
    fn is_script(&self, value: &str) -> bool;
}

/// Accepts every script name: the check is not done.
#[derive(Debug, Clone, Copy, Default)]
pub struct SyntaxOnly;

impl Names for SyntaxOnly {
    fn is_script(&self, _value: &str) -> bool {
        true
    }
}

/// A list of ASCII names as a constant, and the function that tests
/// membership as a `match` on the bytes: no loop, so a bounded model checker
/// needs no unwinding bound for it. The one list is the source of both.
macro_rules! names {
    ($(#[$doc:meta])* $list:ident, $test:ident, $($n:literal),* $(,)?) => {
        $(#[$doc])*
        pub const $list: &[&[u8]] = &[$($n),*];

        /// Whether `name` (ASCII bytes) is in the list of the same name,
        /// compared byte for byte.
        #[must_use]
        pub fn $test(name: &[u8]) -> bool {
            matches!(name, $($n)|*)
        }
    };
}

names! {
    /// `General_Category` values: canonical names and aliases.
    GENERAL_CATEGORY_VALUES, is_general_category,
    b"Cased_Letter", b"LC", b"Close_Punctuation", b"Pe", b"Connector_Punctuation", b"Pc", b"Control", b"Cc", b"cntrl", b"Currency_Symbol", b"Sc", b"Dash_Punctuation", b"Pd", b"Decimal_Number", b"Nd", b"digit", b"Enclosing_Mark", b"Me", b"Final_Punctuation", b"Pf", b"Format", b"Cf", b"Initial_Punctuation", b"Pi", b"Letter", b"L", b"Letter_Number", b"Nl", b"Line_Separator", b"Zl", b"Lowercase_Letter", b"Ll", b"Mark", b"M", b"Combining_Mark", b"Math_Symbol", b"Sm", b"Modifier_Letter", b"Lm", b"Modifier_Symbol", b"Sk", b"Nonspacing_Mark", b"Mn", b"Number", b"N", b"Open_Punctuation", b"Ps", b"Other", b"C", b"Other_Letter", b"Lo", b"Other_Number", b"No", b"Other_Punctuation", b"Po", b"Other_Symbol", b"So", b"Paragraph_Separator", b"Zp", b"Private_Use", b"Co", b"Punctuation", b"P", b"punct", b"Separator", b"Z", b"Space_Separator", b"Zs", b"Spacing_Mark", b"Mc", b"Surrogate", b"Cs", b"Symbol", b"S", b"Titlecase_Letter", b"Lt", b"Unassigned", b"Cn", b"Uppercase_Letter", b"Lu"
}

names! {
    /// The binary properties' names and aliases.
    BINARY_NAMES, is_binary_property,
    b"ASCII", b"ASCII_Hex_Digit", b"AHex", b"Alphabetic", b"Alpha", b"Any", b"Assigned", b"Bidi_Control", b"Bidi_C", b"Bidi_Mirrored", b"Bidi_M", b"Case_Ignorable", b"CI", b"Cased", b"Changes_When_Casefolded", b"CWCF", b"Changes_When_Casemapped", b"CWCM", b"Changes_When_Lowercased", b"CWL", b"Changes_When_NFKC_Casefolded", b"CWKCF", b"Changes_When_Titlecased", b"CWT", b"Changes_When_Uppercased", b"CWU", b"Dash", b"Default_Ignorable_Code_Point", b"DI", b"Deprecated", b"Dep", b"Diacritic", b"Dia", b"Emoji", b"Emoji_Component", b"EComp", b"Emoji_Modifier", b"EMod", b"Emoji_Modifier_Base", b"EBase", b"Emoji_Presentation", b"EPres", b"Extended_Pictographic", b"ExtPict", b"Extender", b"Ext", b"Grapheme_Base", b"Gr_Base", b"Grapheme_Extend", b"Gr_Ext", b"Hex_Digit", b"Hex", b"IDS_Binary_Operator", b"IDSB", b"IDS_Trinary_Operator", b"IDST", b"ID_Continue", b"IDC", b"ID_Start", b"IDS", b"Ideographic", b"Ideo", b"Join_Control", b"Join_C", b"Logical_Order_Exception", b"LOE", b"Lowercase", b"Lower", b"Math", b"Noncharacter_Code_Point", b"NChar", b"Pattern_Syntax", b"Pat_Syn", b"Pattern_White_Space", b"Pat_WS", b"Quotation_Mark", b"QMark", b"Radical", b"Regional_Indicator", b"RI", b"Sentence_Terminal", b"STerm", b"Soft_Dotted", b"SD", b"Terminal_Punctuation", b"Term", b"Unified_Ideograph", b"UIdeo", b"Uppercase", b"Upper", b"Variation_Selector", b"VS", b"White_Space", b"space", b"XID_Continue", b"XIDC", b"XID_Start", b"XIDS"
}

/// The binary properties: canonical name and alias (the same bytes if it has
/// none). Its names are [`BINARY_NAMES`].
pub const BINARY_PROPERTIES: &[(&[u8], &[u8])] = &[
    (b"ASCII", b"ASCII"),
    (b"ASCII_Hex_Digit", b"AHex"),
    (b"Alphabetic", b"Alpha"),
    (b"Any", b"Any"),
    (b"Assigned", b"Assigned"),
    (b"Bidi_Control", b"Bidi_C"),
    (b"Bidi_Mirrored", b"Bidi_M"),
    (b"Case_Ignorable", b"CI"),
    (b"Cased", b"Cased"),
    (b"Changes_When_Casefolded", b"CWCF"),
    (b"Changes_When_Casemapped", b"CWCM"),
    (b"Changes_When_Lowercased", b"CWL"),
    (b"Changes_When_NFKC_Casefolded", b"CWKCF"),
    (b"Changes_When_Titlecased", b"CWT"),
    (b"Changes_When_Uppercased", b"CWU"),
    (b"Dash", b"Dash"),
    (b"Default_Ignorable_Code_Point", b"DI"),
    (b"Deprecated", b"Dep"),
    (b"Diacritic", b"Dia"),
    (b"Emoji", b"Emoji"),
    (b"Emoji_Component", b"EComp"),
    (b"Emoji_Modifier", b"EMod"),
    (b"Emoji_Modifier_Base", b"EBase"),
    (b"Emoji_Presentation", b"EPres"),
    (b"Extended_Pictographic", b"ExtPict"),
    (b"Extender", b"Ext"),
    (b"Grapheme_Base", b"Gr_Base"),
    (b"Grapheme_Extend", b"Gr_Ext"),
    (b"Hex_Digit", b"Hex"),
    (b"IDS_Binary_Operator", b"IDSB"),
    (b"IDS_Trinary_Operator", b"IDST"),
    (b"ID_Continue", b"IDC"),
    (b"ID_Start", b"IDS"),
    (b"Ideographic", b"Ideo"),
    (b"Join_Control", b"Join_C"),
    (b"Logical_Order_Exception", b"LOE"),
    (b"Lowercase", b"Lower"),
    (b"Math", b"Math"),
    (b"Noncharacter_Code_Point", b"NChar"),
    (b"Pattern_Syntax", b"Pat_Syn"),
    (b"Pattern_White_Space", b"Pat_WS"),
    (b"Quotation_Mark", b"QMark"),
    (b"Radical", b"Radical"),
    (b"Regional_Indicator", b"RI"),
    (b"Sentence_Terminal", b"STerm"),
    (b"Soft_Dotted", b"SD"),
    (b"Terminal_Punctuation", b"Term"),
    (b"Unified_Ideograph", b"UIdeo"),
    (b"Uppercase", b"Upper"),
    (b"Variation_Selector", b"VS"),
    (b"White_Space", b"space"),
    (b"XID_Continue", b"XIDC"),
    (b"XID_Start", b"XIDS"),
];

names! {
    /// The binary properties of strings (`v` mode, `\p` only).
    STRING_PROPERTIES, is_string_property,
    b"Basic_Emoji", b"Emoji_Keycap_Sequence", b"RGI_Emoji_Modifier_Sequence", b"RGI_Emoji_Flag_Sequence", b"RGI_Emoji_Tag_Sequence", b"RGI_Emoji_ZWJ_Sequence", b"RGI_Emoji"
}
