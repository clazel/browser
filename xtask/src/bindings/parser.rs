//! The WebIDL parser: a recursive-descent reading of the grammar of WebIDL
//! §2 "Interface definition language"
//! (<https://webidl.spec.whatwg.org/#idl-grammar>). Each function names the
//! production it reads, in the standard's spelling.
//!
//! Modelling choices (the grammar is read, not extended):
//! - The forms of extended attribute of WebIDL §2.2 are parsed (no
//!   arguments, argument list, named argument list, identifier, identifier
//!   list), with literals and lists of literals as values too (HTML's
//!   `[ReflectRange=(0, 8)]` needs them); the grammar's catch-all
//!   `ExtendedAttributeRest` (free-form token sequences) is rejected, as it
//!   has no meaning to give.
//! - A keyword is an identifier the grammar spells as a terminal; one is
//!   accepted as a name only where the grammar says so (`ArgumentNameKeyword`,
//!   `AttributeNameKeyword`, `OperationNameKeyword`) or when written with a
//!   leading `_`.
//! - Which members a container takes (`PartialInterfaceMember`,
//!   `MixinMember`, `CallbackInterfaceMember`, `NamespaceMember`) is checked
//!   after the member is read, with the container named in the error.
//! - Semantic rules (WebIDL §2.5 and the per-feature rules) are not checked
//!   here; `resolve.rs` checks what the model needs (names, partials,
//!   includes, references).

use super::lexer::{Tok, Token, lex};
use super::model::{
    Argument, Attribute, Collection, Const, Definition, DictMember, ExtAttr, ExtValue, Iterable,
    Member, MemberKind, OpKind, Operation, Simple, Ty, TyKind, Value,
};

/// The terminals of the grammar that look like identifiers.
const KEYWORDS: &[&str] = &[
    "ArrayBuffer",
    "BigInt64Array",
    "BigUint64Array",
    "ByteString",
    "DOMString",
    "DataView",
    "Float16Array",
    "Float32Array",
    "Float64Array",
    "FrozenArray",
    "Infinity",
    "Int16Array",
    "Int32Array",
    "Int8Array",
    "NaN",
    "ObservableArray",
    "Promise",
    "SharedArrayBuffer",
    "USVString",
    "Uint16Array",
    "Uint32Array",
    "Uint8Array",
    "Uint8ClampedArray",
    "any",
    "async",
    "attribute",
    "bigint",
    "boolean",
    "byte",
    "callback",
    "const",
    "constructor",
    "deleter",
    "dictionary",
    "double",
    "enum",
    "false",
    "float",
    "getter",
    "includes",
    "inherit",
    "interface",
    "iterable",
    "long",
    "maplike",
    "mixin",
    "namespace",
    "null",
    "object",
    "octet",
    "optional",
    "or",
    "partial",
    "readonly",
    "record",
    "required",
    "sequence",
    "setlike",
    "setter",
    "short",
    "static",
    "stringifier",
    "symbol",
    "true",
    "typedef",
    "undefined",
    "unrestricted",
    "unsigned",
];

/// `ArgumentNameKeyword`.
const ARGUMENT_NAME_KEYWORDS: &[&str] = &[
    "async",
    "attribute",
    "callback",
    "const",
    "constructor",
    "deleter",
    "dictionary",
    "enum",
    "getter",
    "includes",
    "inherit",
    "interface",
    "iterable",
    "maplike",
    "mixin",
    "namespace",
    "partial",
    "readonly",
    "required",
    "setlike",
    "setter",
    "static",
    "stringifier",
    "typedef",
    "unrestricted",
];

/// `BufferRelatedType`.
const BUFFER_TYPES: &[&str] = &[
    "ArrayBuffer",
    "SharedArrayBuffer",
    "DataView",
    "Int8Array",
    "Int16Array",
    "Int32Array",
    "Uint8Array",
    "Uint16Array",
    "Uint32Array",
    "Uint8ClampedArray",
    "BigInt64Array",
    "BigUint64Array",
    "Float16Array",
    "Float32Array",
    "Float64Array",
];

/// Where a member is being read, for the `*Member` productions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Container {
    Interface,
    PartialInterface,
    Mixin,
    CallbackInterface,
    Namespace,
}

impl Container {
    fn name(self) -> &'static str {
        match self {
            Self::Interface => "interface",
            Self::PartialInterface => "partial interface",
            Self::Mixin => "interface mixin",
            Self::CallbackInterface => "callback interface",
            Self::Namespace => "namespace",
        }
    }
}

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    last_line: u32,
}

/// Parse one IDL file (`Definitions`).
pub fn parse(src: &str) -> Result<Vec<Definition>, String> {
    let toks = lex(src)?;
    let last_line = toks.last().map_or(1, |t| t.line);
    let mut p = Parser {
        toks,
        pos: 0,
        last_line,
    };
    p.definitions()
}

type R<T> = Result<T, String>;

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|t| &t.tok)
    }

    fn peek_at(&self, n: usize) -> Option<&Tok> {
        self.toks.get(self.pos.saturating_add(n)).map(|t| &t.tok)
    }

    fn line(&self) -> u32 {
        self.toks.get(self.pos).map_or(self.last_line, |t| t.line)
    }

    fn err<T>(&self, msg: &str) -> R<T> {
        let found = match self.peek() {
            Some(Tok::Ident { name, .. }) => format!("`{name}`"),
            Some(Tok::Integer(s) | Tok::Decimal(s)) => format!("`{s}`"),
            Some(Tok::Str(s)) => format!("\"{s}\""),
            Some(Tok::Ellipsis) => "`...`".to_owned(),
            Some(Tok::Punct(c)) => format!("`{c}`"),
            None => "end of file".to_owned(),
        };
        Err(format!("{}: {msg}, found {found}", self.line()))
    }

    fn advance(&mut self) {
        self.pos = self.pos.saturating_add(1);
    }

    fn kw_at(&self, n: usize, kw: &str) -> bool {
        matches!(self.peek_at(n), Some(Tok::Ident { name, escaped: false }) if name == kw)
    }

    fn is_kw(&self, kw: &str) -> bool {
        self.kw_at(0, kw)
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        let found = self.is_kw(kw);
        if found {
            self.advance();
        }
        found
    }

    fn expect_kw(&mut self, kw: &str) -> R<()> {
        if self.eat_kw(kw) {
            Ok(())
        } else {
            self.err(&format!("expected `{kw}`"))
        }
    }

    fn is_punct(&self, c: char) -> bool {
        self.peek() == Some(&Tok::Punct(c))
    }

    fn eat_punct(&mut self, c: char) -> bool {
        let found = self.is_punct(c);
        if found {
            self.advance();
        }
        found
    }

    fn expect_punct(&mut self, c: char) -> R<()> {
        if self.eat_punct(c) {
            Ok(())
        } else {
            self.err(&format!("expected `{c}`"))
        }
    }

    /// The token `identifier`: not a keyword, unless escaped.
    fn identifier(&mut self) -> R<String> {
        if let Some(Tok::Ident { name, escaped }) = self.peek()
            && (*escaped || !KEYWORDS.contains(&name.as_str()))
        {
            let name = name.clone();
            self.advance();
            return Ok(name);
        }
        self.err("expected an identifier")
    }

    /// An identifier, or one of the keywords `allowed`.
    fn identifier_or(&mut self, allowed: &[&str]) -> R<String> {
        if let Some(Tok::Ident {
            name,
            escaped: false,
        }) = self.peek()
            && allowed.contains(&name.as_str())
        {
            let name = name.clone();
            self.advance();
            return Ok(name);
        }
        self.identifier()
    }

    /// Any identifier token, keyword or not (extended attribute names and
    /// values, which the standard's per-attribute grammar defines).
    fn any_ident(&mut self) -> R<String> {
        if let Some(Tok::Ident { name, .. }) = self.peek() {
            let name = name.clone();
            self.advance();
            return Ok(name);
        }
        self.err("expected an identifier")
    }

    fn string(&mut self) -> R<String> {
        if let Some(Tok::Str(s)) = self.peek() {
            let s = s.clone();
            self.advance();
            return Ok(s);
        }
        self.err("expected a string")
    }

    // ---- Definitions ----

    /// `Definitions`.
    fn definitions(&mut self) -> R<Vec<Definition>> {
        let mut out = Vec::new();
        while self.peek().is_some() {
            let ext = self.extended_attribute_list()?;
            out.push(self.definition(ext)?);
        }
        Ok(out)
    }

    /// `Definition`.
    fn definition(&mut self, ext: Vec<ExtAttr>) -> R<Definition> {
        if self.eat_kw("callback") {
            return self.callback_rest_or_interface(ext);
        }
        if self.eat_kw("interface") {
            return self.interface_or_mixin(ext, false);
        }
        if self.eat_kw("partial") {
            return self.partial_definition(ext);
        }
        if self.is_kw("namespace") {
            return self.namespace(ext, false);
        }
        if self.is_kw("dictionary") {
            return self.dictionary(ext, false);
        }
        if self.eat_kw("enum") {
            return self.enumeration(ext);
        }
        if self.eat_kw("typedef") {
            let ty = self.type_with_extended_attributes()?;
            let name = self.identifier()?;
            self.expect_punct(';')?;
            return Ok(Definition::Typedef { ext, name, ty });
        }
        // IncludesStatement ::= identifier includes identifier ;
        if matches!(self.peek(), Some(Tok::Ident { .. })) && self.kw_at(1, "includes") {
            let target = self.identifier()?;
            self.expect_kw("includes")?;
            let mixin = self.identifier()?;
            self.expect_punct(';')?;
            if !ext.is_empty() {
                return self.err("an includes statement takes no extended attributes");
            }
            return Ok(Definition::Includes { target, mixin });
        }
        self.err("expected a definition")
    }

    /// `CallbackOrInterfaceOrMixin ::= callback CallbackRestOrInterface`,
    /// after `callback`.
    fn callback_rest_or_interface(&mut self, ext: Vec<ExtAttr>) -> R<Definition> {
        if self.eat_kw("interface") {
            // callback interface identifier { CallbackInterfaceMembers } ;
            let name = self.identifier()?;
            self.expect_punct('{')?;
            let members = self.members(Container::CallbackInterface)?;
            self.expect_punct(';')?;
            return Ok(Definition::Interface {
                ext,
                name,
                parent: None,
                partial: false,
                callback: true,
                members,
            });
        }
        // CallbackRest ::= identifier = Type ( ArgumentList ) ;
        let name = self.identifier()?;
        self.expect_punct('=')?;
        let ret = self.type_()?;
        self.expect_punct('(')?;
        let args = self.argument_list()?;
        self.expect_punct(')')?;
        self.expect_punct(';')?;
        Ok(Definition::Callback {
            ext,
            name,
            ret,
            args,
        })
    }

    /// `InterfaceOrMixin ::= InterfaceRest | MixinRest`, after `interface`
    /// (`PartialInterfaceOrPartialMixin` when `partial`).
    fn interface_or_mixin(&mut self, ext: Vec<ExtAttr>, partial: bool) -> R<Definition> {
        if self.eat_kw("mixin") {
            // MixinRest ::= mixin identifier { MixinMembers } ;
            let name = self.identifier()?;
            self.expect_punct('{')?;
            let members = self.members(Container::Mixin)?;
            self.expect_punct(';')?;
            return Ok(Definition::Mixin {
                ext,
                name,
                partial,
                members,
            });
        }
        // InterfaceRest ::= identifier Inheritance { InterfaceMembers } ;
        // PartialInterfaceRest ::= identifier { PartialInterfaceMembers } ;
        let name = self.identifier()?;
        let parent = if partial { None } else { self.inheritance()? };
        self.expect_punct('{')?;
        let container = if partial {
            Container::PartialInterface
        } else {
            Container::Interface
        };
        let members = self.members(container)?;
        self.expect_punct(';')?;
        Ok(Definition::Interface {
            ext,
            name,
            parent,
            partial,
            callback: false,
            members,
        })
    }

    /// `Partial ::= partial PartialDefinition`, after `partial`.
    fn partial_definition(&mut self, ext: Vec<ExtAttr>) -> R<Definition> {
        if self.eat_kw("interface") {
            return self.interface_or_mixin(ext, true);
        }
        if self.is_kw("dictionary") {
            return self.dictionary(ext, true);
        }
        if self.is_kw("namespace") {
            return self.namespace(ext, true);
        }
        self.err("expected `interface`, `dictionary` or `namespace` after `partial`")
    }

    /// `Inheritance ::= : identifier | ε`.
    fn inheritance(&mut self) -> R<Option<String>> {
        if self.eat_punct(':') {
            return Ok(Some(self.identifier()?));
        }
        Ok(None)
    }

    /// `Namespace ::= namespace identifier { NamespaceMembers } ;`.
    fn namespace(&mut self, ext: Vec<ExtAttr>, partial: bool) -> R<Definition> {
        self.expect_kw("namespace")?;
        let name = self.identifier()?;
        self.expect_punct('{')?;
        let members = self.members(Container::Namespace)?;
        self.expect_punct(';')?;
        Ok(Definition::Namespace {
            ext,
            name,
            partial,
            members,
        })
    }

    /// `Dictionary ::= dictionary identifier Inheritance { DictionaryMembers } ;`
    /// and `PartialDictionary`.
    fn dictionary(&mut self, ext: Vec<ExtAttr>, partial: bool) -> R<Definition> {
        self.expect_kw("dictionary")?;
        let name = self.identifier()?;
        let parent = if partial { None } else { self.inheritance()? };
        self.expect_punct('{')?;
        let mut members = Vec::new();
        while !self.eat_punct('}') {
            // DictionaryMember ::= ExtendedAttributeList DictionaryMemberRest
            let mext = self.extended_attribute_list()?;
            let required = self.eat_kw("required");
            let ty = if required {
                self.type_with_extended_attributes()?
            } else {
                self.type_()?
            };
            let mname = self.identifier()?;
            let default = self.default()?;
            self.expect_punct(';')?;
            members.push(DictMember {
                ext: mext,
                name: mname,
                ty,
                required,
                default,
            });
        }
        self.expect_punct(';')?;
        Ok(Definition::Dictionary {
            ext,
            name,
            parent,
            partial,
            members,
        })
    }

    /// `Enum ::= enum identifier { EnumValueList } ;`, after `enum`.
    fn enumeration(&mut self, ext: Vec<ExtAttr>) -> R<Definition> {
        let name = self.identifier()?;
        self.expect_punct('{')?;
        let mut values = vec![self.string()?];
        while self.eat_punct(',') {
            // EnumValueListComma allows a trailing comma.
            if self.is_punct('}') {
                break;
            }
            values.push(self.string()?);
        }
        self.expect_punct('}')?;
        self.expect_punct(';')?;
        Ok(Definition::Enum { ext, name, values })
    }

    // ---- Members ----

    /// The members of a container up to and including its `}`.
    fn members(&mut self, container: Container) -> R<Vec<Member>> {
        let mut out = Vec::new();
        while !self.eat_punct('}') {
            let ext = self.extended_attribute_list()?;
            let line = self.line();
            let kind = self.member(container)?;
            if !allowed(container, &kind) {
                return Err(format!(
                    "{line}: this kind of member is not allowed in a {}",
                    container.name()
                ));
            }
            out.push(Member {
                ext,
                kind,
                mixin: None,
            });
        }
        Ok(out)
    }

    /// `InterfaceMember`, and the other containers' member productions.
    fn member(&mut self, container: Container) -> R<MemberKind> {
        if self.eat_kw("const") {
            return self.constant();
        }
        // Constructor ::= constructor ( ArgumentList ) ;
        if self.is_kw("constructor") && matches!(self.peek_at(1), Some(Tok::Punct('('))) {
            self.advance();
            self.advance();
            let args = self.argument_list()?;
            self.expect_punct(')')?;
            self.expect_punct(';')?;
            return Ok(MemberKind::Constructor(args));
        }
        if self.eat_kw("stringifier") {
            // StringifierRest ::= OptionalReadOnly AttributeRest | ;
            if self.eat_punct(';') {
                return Ok(MemberKind::Operation(Operation {
                    name: None,
                    kind: OpKind::Stringifier,
                    ret: simple(Simple::DomString),
                    args: Vec::new(),
                }));
            }
            let readonly = self.eat_kw("readonly");
            return self.attribute_rest(readonly, false, false, true);
        }
        if self.eat_kw("static") {
            // StaticMemberRest ::= OptionalReadOnly AttributeRest | RegularOperation
            if self.is_kw("readonly") || self.is_kw("attribute") {
                let readonly = self.eat_kw("readonly");
                return self.attribute_rest(readonly, false, true, false);
            }
            return self.regular_operation(OpKind::Static);
        }
        if self.is_kw("iterable") || (self.is_kw("async") && self.kw_at(1, "iterable")) {
            return self.iterable();
        }
        if self.is_kw("maplike") || self.is_kw("setlike") {
            return self.maplike_setlike(false);
        }
        if self.eat_kw("readonly") {
            // ReadOnlyMember ::= readonly ReadOnlyMemberRest
            if self.is_kw("maplike") || self.is_kw("setlike") {
                return self.maplike_setlike(true);
            }
            return self.attribute_rest(true, false, false, false);
        }
        if self.eat_kw("inherit") {
            return self.attribute_rest(false, true, false, false);
        }
        if self.is_kw("attribute") {
            return self.attribute_rest(false, false, false, false);
        }
        // Special ::= getter | setter | deleter
        for (kw, kind) in [
            ("getter", OpKind::Getter),
            ("setter", OpKind::Setter),
            ("deleter", OpKind::Deleter),
        ] {
            if self.eat_kw(kw) {
                return self.regular_operation(kind);
            }
        }
        let _ = container;
        self.regular_operation(OpKind::Regular)
    }

    /// `Const ::= const ConstType identifier = ConstValue ;`, after `const`.
    fn constant(&mut self) -> R<MemberKind> {
        // ConstType ::= PrimitiveType | identifier
        let ty = if self.is_primitive_start() {
            self.distinguishable_type()?
        } else {
            let name = self.identifier()?;
            Ty {
                kind: TyKind::Named(name),
                nullable: false,
                ext: Vec::new(),
            }
        };
        let name = self.identifier()?;
        self.expect_punct('=')?;
        let value = self.const_value()?;
        self.expect_punct(';')?;
        Ok(MemberKind::Const(Const { name, ty, value }))
    }

    /// `AttributeRest ::= attribute TypeWithExtendedAttributes AttributeName ;`
    fn attribute_rest(
        &mut self,
        readonly: bool,
        inherit: bool,
        is_static: bool,
        stringifier: bool,
    ) -> R<MemberKind> {
        self.expect_kw("attribute")?;
        let ty = self.type_with_extended_attributes()?;
        // AttributeName ::= AttributeNameKeyword | identifier
        let name = self.identifier_or(&["async", "required"])?;
        self.expect_punct(';')?;
        Ok(MemberKind::Attribute(Attribute {
            name,
            ty,
            readonly,
            inherit,
            is_static,
            stringifier,
        }))
    }

    /// `RegularOperation ::= Type OperationRest`.
    fn regular_operation(&mut self, kind: OpKind) -> R<MemberKind> {
        let ret = self.type_()?;
        // OptionalOperationName ::= OperationName | ε
        let name = if self.is_punct('(') {
            None
        } else {
            Some(self.identifier_or(&["includes"])?)
        };
        self.expect_punct('(')?;
        let args = self.argument_list()?;
        self.expect_punct(')')?;
        self.expect_punct(';')?;
        Ok(MemberKind::Operation(Operation {
            name,
            kind,
            ret,
            args,
        }))
    }

    /// `Iterable` and `AsyncIterable`.
    fn iterable(&mut self) -> R<MemberKind> {
        let is_async = self.eat_kw("async");
        self.expect_kw("iterable")?;
        self.expect_punct('<')?;
        let first = self.type_with_extended_attributes()?;
        let (key, value) = if self.eat_punct(',') {
            (Some(first), self.type_with_extended_attributes()?)
        } else {
            (None, first)
        };
        self.expect_punct('>')?;
        let mut args = Vec::new();
        if is_async && self.eat_punct('(') {
            args = self.argument_list()?;
            self.expect_punct(')')?;
        }
        self.expect_punct(';')?;
        Ok(MemberKind::Iterable(Iterable {
            is_async,
            key,
            value,
            args,
        }))
    }

    /// `MaplikeRest` and `SetlikeRest`.
    fn maplike_setlike(&mut self, readonly: bool) -> R<MemberKind> {
        let is_map = self.is_kw("maplike");
        self.advance();
        self.expect_punct('<')?;
        let first = self.type_with_extended_attributes()?;
        let (key, value) = if is_map {
            self.expect_punct(',')?;
            (Some(first), self.type_with_extended_attributes()?)
        } else {
            (None, first)
        };
        self.expect_punct('>')?;
        self.expect_punct(';')?;
        Ok(MemberKind::Collection(Collection {
            is_map,
            readonly,
            key,
            value,
        }))
    }

    // ---- Arguments, values ----

    /// `ArgumentList`, up to but not including the `)`.
    fn argument_list(&mut self) -> R<Vec<Argument>> {
        let mut out = Vec::new();
        if self.is_punct(')') {
            return Ok(out);
        }
        loop {
            out.push(self.argument()?);
            if !self.eat_punct(',') {
                return Ok(out);
            }
        }
    }

    /// `Argument ::= ExtendedAttributeList ArgumentRest`.
    fn argument(&mut self) -> R<Argument> {
        let ext = self.extended_attribute_list()?;
        if self.eat_kw("optional") {
            let ty = self.type_with_extended_attributes()?;
            let name = self.identifier_or(ARGUMENT_NAME_KEYWORDS)?;
            let default = self.default()?;
            return Ok(Argument {
                ext,
                name,
                ty,
                optional: true,
                variadic: false,
                default,
            });
        }
        let ty = self.type_()?;
        let variadic = self.peek() == Some(&Tok::Ellipsis);
        if variadic {
            self.advance();
        }
        let name = self.identifier_or(ARGUMENT_NAME_KEYWORDS)?;
        Ok(Argument {
            ext,
            name,
            ty,
            optional: false,
            variadic,
            default: None,
        })
    }

    /// `Default ::= = DefaultValue | ε`.
    fn default(&mut self) -> R<Option<Value>> {
        if !self.eat_punct('=') {
            return Ok(None);
        }
        // DefaultValue ::= ConstValue | string | [ ] | { } | null | undefined
        if let Some(Tok::Str(s)) = self.peek() {
            let v = Value::Str(s.clone());
            self.advance();
            return Ok(Some(v));
        }
        if self.eat_punct('[') {
            self.expect_punct(']')?;
            return Ok(Some(Value::EmptySequence));
        }
        if self.eat_punct('{') {
            self.expect_punct('}')?;
            return Ok(Some(Value::EmptyDictionary));
        }
        if self.eat_kw("null") {
            return Ok(Some(Value::Null));
        }
        if self.eat_kw("undefined") {
            return Ok(Some(Value::Undefined));
        }
        Ok(Some(self.const_value()?))
    }

    /// `ConstValue ::= BooleanLiteral | FloatLiteral | integer`.
    fn const_value(&mut self) -> R<Value> {
        let v = match self.peek() {
            Some(Tok::Ident {
                name,
                escaped: false,
            }) => match name.as_str() {
                "true" => Value::Bool(true),
                "false" => Value::Bool(false),
                "Infinity" => Value::Infinity,
                "-Infinity" => Value::NegInfinity,
                "NaN" => Value::NaN,
                _ => return self.err("expected a constant value"),
            },
            Some(Tok::Decimal(s)) => Value::Decimal(s.clone()),
            Some(Tok::Integer(s)) => match integer_value(s) {
                Some(n) => Value::Integer(n),
                None => return self.err("integer out of range"),
            },
            _ => return self.err("expected a constant value"),
        };
        self.advance();
        Ok(v)
    }

    // ---- Extended attributes ----

    /// `ExtendedAttributeList ::= [ ExtendedAttribute ExtendedAttributes ] | ε`.
    fn extended_attribute_list(&mut self) -> R<Vec<ExtAttr>> {
        let mut out = Vec::new();
        if !self.eat_punct('[') {
            return Ok(out);
        }
        loop {
            out.push(self.extended_attribute()?);
            if self.eat_punct(',') {
                continue;
            }
            self.expect_punct(']')?;
            return Ok(out);
        }
    }

    /// `ExtendedAttribute`, in the five forms of WebIDL §2.2: no arguments,
    /// argument list, named argument list, identifier, identifier list
    /// (and the wildcard form of `[Exposed=*]`).
    fn extended_attribute(&mut self) -> R<ExtAttr> {
        let name = self.any_ident()?;
        let value = if self.eat_punct('=') {
            if self.eat_punct('*') {
                ExtValue::Wildcard
            } else if self.eat_punct('(') {
                self.ext_list_value()?
            } else if let Some(v) = self.literal() {
                ExtValue::Literal(v)
            } else {
                let value = self.any_ident()?;
                if self.eat_punct('(') {
                    let args = self.argument_list()?;
                    self.expect_punct(')')?;
                    ExtValue::NamedArgs(value, args)
                } else {
                    ExtValue::Ident(value)
                }
            }
        } else if self.eat_punct('(') {
            let args = self.argument_list()?;
            self.expect_punct(')')?;
            ExtValue::Args(args)
        } else {
            ExtValue::None
        };
        Ok(ExtAttr { name, value })
    }

    /// The inside of `[Name=( ... )]`, after the `(`: identifiers or
    /// literals, not mixed.
    fn ext_list_value(&mut self) -> R<ExtValue> {
        if matches!(self.peek(), Some(Tok::Ident { .. })) {
            let mut list = vec![self.any_ident()?];
            while self.eat_punct(',') {
                list.push(self.any_ident()?);
            }
            self.expect_punct(')')?;
            return Ok(ExtValue::IdentList(list));
        }
        let mut list = Vec::new();
        loop {
            match self.literal() {
                Some(v) => list.push(v),
                None => return self.err("expected an identifier or a literal"),
            }
            if !self.eat_punct(',') {
                break;
            }
        }
        self.expect_punct(')')?;
        Ok(ExtValue::LiteralList(list))
    }

    /// An `integer`, `decimal` or `string` token, consumed.
    fn literal(&mut self) -> Option<Value> {
        let v = match self.peek()? {
            Tok::Integer(s) => Value::Integer(integer_value(s)?),
            Tok::Decimal(s) => Value::Decimal(s.clone()),
            Tok::Str(s) => Value::Str(s.clone()),
            _ => return None,
        };
        self.advance();
        Some(v)
    }

    // ---- Types ----

    /// `TypeWithExtendedAttributes ::= ExtendedAttributeList Type`.
    fn type_with_extended_attributes(&mut self) -> R<Ty> {
        let ext = self.extended_attribute_list()?;
        let mut ty = self.type_()?;
        ty.ext = ext;
        Ok(ty)
    }

    /// `Type ::= SingleType | UnionType Null`.
    fn type_(&mut self) -> R<Ty> {
        if self.is_punct('(') {
            return self.union_type();
        }
        // SingleType ::= DistinguishableType | any | PromiseType
        if self.eat_kw("any") {
            return Ok(simple(Simple::Any));
        }
        if self.eat_kw("Promise") {
            self.expect_punct('<')?;
            let inner = self.type_()?;
            self.expect_punct('>')?;
            return Ok(Ty {
                kind: TyKind::Promise(Box::new(inner)),
                nullable: false,
                ext: Vec::new(),
            });
        }
        self.distinguishable_type()
    }

    /// `UnionType ::= ( UnionMemberType or UnionMemberType UnionMemberTypes )`
    /// followed by `Null`.
    fn union_type(&mut self) -> R<Ty> {
        self.expect_punct('(')?;
        let mut members = vec![self.union_member_type()?];
        self.expect_kw("or")?;
        members.push(self.union_member_type()?);
        while self.eat_kw("or") {
            members.push(self.union_member_type()?);
        }
        self.expect_punct(')')?;
        let nullable = self.eat_punct('?');
        Ok(Ty {
            kind: TyKind::Union(members),
            nullable,
            ext: Vec::new(),
        })
    }

    /// `UnionMemberType ::= ExtendedAttributeList DistinguishableType | UnionType Null`.
    fn union_member_type(&mut self) -> R<Ty> {
        let ext = self.extended_attribute_list()?;
        let mut ty = if self.is_punct('(') {
            self.union_type()?
        } else {
            self.distinguishable_type()?
        };
        ty.ext = ext;
        Ok(ty)
    }

    /// Whether a `PrimitiveType` starts here.
    fn is_primitive_start(&self) -> bool {
        [
            "unsigned",
            "unrestricted",
            "short",
            "long",
            "float",
            "double",
            "undefined",
            "boolean",
            "byte",
            "octet",
            "bigint",
        ]
        .iter()
        .any(|k| self.is_kw(k))
    }

    /// `DistinguishableType`.
    fn distinguishable_type(&mut self) -> R<Ty> {
        let kind = if let Some(s) = self.primitive_type()? {
            TyKind::Simple(s)
        } else if let Some(Tok::Ident {
            name,
            escaped: false,
        }) = self.peek().cloned()
        {
            match name.as_str() {
                "ByteString" => self.keyword_type(Simple::ByteString),
                "DOMString" => self.keyword_type(Simple::DomString),
                "USVString" => self.keyword_type(Simple::UsvString),
                "object" => self.keyword_type(Simple::Object),
                "symbol" => self.keyword_type(Simple::Symbol),
                "sequence" | "FrozenArray" | "ObservableArray" => {
                    self.advance();
                    self.expect_punct('<')?;
                    let inner = Box::new(self.type_with_extended_attributes()?);
                    self.expect_punct('>')?;
                    match name.as_str() {
                        "sequence" => TyKind::Sequence(inner),
                        "FrozenArray" => TyKind::FrozenArray(inner),
                        _ => TyKind::ObservableArray(inner),
                    }
                }
                "record" => {
                    self.advance();
                    self.expect_punct('<')?;
                    // RecordType ::= record < StringType , TypeWithExtendedAttributes >
                    let key = match self.peek() {
                        Some(Tok::Ident { name, .. })
                            if matches!(
                                name.as_str(),
                                "ByteString" | "DOMString" | "USVString"
                            ) =>
                        {
                            self.distinguishable_type_no_null()?
                        }
                        _ => return self.err("expected a string type as the record key"),
                    };
                    self.expect_punct(',')?;
                    let value = self.type_with_extended_attributes()?;
                    self.expect_punct('>')?;
                    TyKind::Record(Box::new(key), Box::new(value))
                }
                n if BUFFER_TYPES.contains(&n) => {
                    self.advance();
                    TyKind::Buffer(name.clone())
                }
                _ => TyKind::Named(self.identifier()?),
            }
        } else {
            return self.err("expected a type");
        };
        let nullable = self.eat_punct('?');
        Ok(Ty {
            kind,
            nullable,
            ext: Vec::new(),
        })
    }

    /// A `StringType` with no `Null` after it.
    fn distinguishable_type_no_null(&mut self) -> R<Ty> {
        let simple_kind = match self.peek() {
            Some(Tok::Ident { name, .. }) => match name.as_str() {
                "ByteString" => Simple::ByteString,
                "DOMString" => Simple::DomString,
                _ => Simple::UsvString,
            },
            _ => return self.err("expected a string type"),
        };
        self.advance();
        Ok(simple(simple_kind))
    }

    fn keyword_type(&mut self, s: Simple) -> TyKind {
        self.advance();
        TyKind::Simple(s)
    }

    /// `PrimitiveType`, if one starts here.
    fn primitive_type(&mut self) -> R<Option<Simple>> {
        let Some(Tok::Ident {
            name,
            escaped: false,
        }) = self.peek().cloned()
        else {
            return Ok(None);
        };
        let simple = match name.as_str() {
            "undefined" => {
                self.advance();
                Simple::Undefined
            }
            "boolean" => {
                self.advance();
                Simple::Boolean
            }
            "byte" => {
                self.advance();
                Simple::Byte
            }
            "octet" => {
                self.advance();
                Simple::Octet
            }
            "bigint" => {
                self.advance();
                Simple::Bigint
            }
            "unsigned" => {
                // UnsignedIntegerType ::= unsigned IntegerType
                self.advance();
                match self.integer_type()? {
                    Simple::Short => Simple::UnsignedShort,
                    Simple::Long => Simple::UnsignedLong,
                    _ => Simple::UnsignedLongLong,
                }
            }
            "short" | "long" => self.integer_type()?,
            "unrestricted" => {
                // UnrestrictedFloatType ::= unrestricted FloatType
                self.advance();
                if self.eat_kw("float") {
                    Simple::UnrestrictedFloat
                } else if self.eat_kw("double") {
                    Simple::UnrestrictedDouble
                } else {
                    return self.err("expected `float` or `double` after `unrestricted`");
                }
            }
            "float" => {
                self.advance();
                Simple::Float
            }
            "double" => {
                self.advance();
                Simple::Double
            }
            _ => return Ok(None),
        };
        Ok(Some(simple))
    }

    /// `IntegerType ::= short | long OptionalLong`; `Short`, `Long` or
    /// `LongLong`.
    fn integer_type(&mut self) -> R<Simple> {
        if self.eat_kw("short") {
            return Ok(Simple::Short);
        }
        if self.eat_kw("long") {
            return Ok(if self.eat_kw("long") {
                Simple::LongLong
            } else {
                Simple::Long
            });
        }
        self.err("expected `short` or `long`")
    }
}

fn simple(s: Simple) -> Ty {
    Ty {
        kind: TyKind::Simple(s),
        nullable: false,
        ext: Vec::new(),
    }
}

/// The value of an `integer` token: decimal, `0x` hexadecimal or `0` octal.
fn integer_value(s: &str) -> Option<i128> {
    let (neg, digits) = match s.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, s),
    };
    let magnitude = if let Some(hex) = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        i128::from_str_radix(hex, 16).ok()?
    } else if digits.len() > 1 && digits.starts_with('0') {
        i128::from_str_radix(digits, 8).ok()?
    } else {
        digits.parse::<i128>().ok()?
    };
    if neg {
        magnitude.checked_neg()
    } else {
        Some(magnitude)
    }
}

/// Whether `container`'s member production includes this kind of member.
fn allowed(container: Container, kind: &MemberKind) -> bool {
    match (container, kind) {
        (Container::Interface, _) => true,
        (Container::PartialInterface, MemberKind::Constructor(_)) => false,
        (Container::PartialInterface, _) => true,
        // MixinMember ::= Const | RegularOperation | Stringifier | OptionalReadOnly AttributeRest
        (Container::Mixin, MemberKind::Const(_)) => true,
        (Container::Mixin, MemberKind::Attribute(a)) => !a.is_static && !a.inherit,
        (Container::Mixin, MemberKind::Operation(o)) => {
            matches!(o.kind, OpKind::Regular | OpKind::Stringifier)
        }
        // CallbackInterfaceMember ::= Const | RegularOperation
        (Container::CallbackInterface, MemberKind::Const(_)) => true,
        (Container::CallbackInterface, MemberKind::Operation(o)) => o.kind == OpKind::Regular,
        // NamespaceMember ::= RegularOperation | readonly AttributeRest | Const
        (Container::Namespace, MemberKind::Const(_)) => true,
        (Container::Namespace, MemberKind::Attribute(a)) => {
            a.readonly && !a.is_static && !a.inherit && !a.stringifier
        }
        (Container::Namespace, MemberKind::Operation(o)) => o.kind == OpKind::Regular,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn one(src: &str) -> Result<Definition, String> {
        let mut defs = parse(src)?;
        if defs.len() == 1 {
            Ok(defs.remove(0))
        } else {
            Err(format!("{src:?}: {} definitions", defs.len()))
        }
    }

    /// The first attribute's type in `interface I { attribute <ty> a; };`.
    fn ty(src: &str) -> Ty {
        if let Ok(Definition::Interface { members, .. }) =
            one(&format!("interface I {{ attribute {src} a; }};"))
            && let Some(Member {
                kind: MemberKind::Attribute(a),
                ..
            }) = members.into_iter().next()
        {
            return a.ty;
        }
        simple(Simple::Any)
    }

    #[test]
    fn integer_and_float_types() {
        assert_eq!(ty("unsigned long long"), simple(Simple::UnsignedLongLong));
        assert_eq!(ty("long long"), simple(Simple::LongLong));
        assert_eq!(ty("unsigned short"), simple(Simple::UnsignedShort));
        assert_eq!(
            ty("unrestricted double"),
            simple(Simple::UnrestrictedDouble)
        );
        assert_eq!(ty("float"), simple(Simple::Float));
        assert!(parse("interface I { attribute unsigned float a; };").is_err());
        assert!(parse("interface I { attribute unrestricted long a; };").is_err());
    }

    #[test]
    fn nullable_unions_and_generics() -> Result<(), String> {
        let t = ty("(DOMString or sequence<(long or Node)?>)?");
        assert!(t.nullable);
        let TyKind::Union(members) = t.kind else {
            return Err("not a union".into());
        };
        assert_eq!(members.len(), 2);
        let Some(TyKind::Sequence(inner)) = members.get(1).map(|m| m.kind.clone()) else {
            return Err("not a sequence".into());
        };
        assert!(inner.nullable);
        assert!(matches!(inner.kind, TyKind::Union(ref m) if m.len() == 2));
        // A union takes at least two members.
        assert!(parse("interface I { attribute (long) a; };").is_err());
        Ok(())
    }

    #[test]
    fn record_promise_frozen_array_observable_array_buffers() {
        let t = ty("record<USVString, sequence<DOMString>>");
        assert!(
            matches!(t.kind, TyKind::Record(ref k, _) if k.kind == TyKind::Simple(Simple::UsvString))
        );
        assert!(parse("interface I { attribute record<long, long> a; };").is_err());
        let t = ty("Promise<undefined>");
        assert!(
            matches!(t.kind, TyKind::Promise(ref i) if i.kind == TyKind::Simple(Simple::Undefined))
        );
        assert!(matches!(
            ty("FrozenArray<DOMString>").kind,
            TyKind::FrozenArray(_)
        ));
        assert!(matches!(
            ty("ObservableArray<Foo>").kind,
            TyKind::ObservableArray(_)
        ));
        assert_eq!(
            ty("Uint8ClampedArray").kind,
            TyKind::Buffer("Uint8ClampedArray".into())
        );
        assert_eq!(ty("any").kind, TyKind::Simple(Simple::Any));
        assert!(ty("object?").nullable);
    }

    #[test]
    fn extended_attributes_in_every_form() -> Result<(), String> {
        let Definition::Interface { ext, .. } = one(
            "[Exposed=(Window,Worker), Global=Window, LegacyFactoryFunction=Image(unsigned long width), \
             Constructor(optional DOMString s = \"\"), Exposed=*, SecureContext] \
             interface I {};",
        )?
        else {
            return Err("not an interface".into());
        };
        let names: Vec<_> = ext.iter().map(|e| e.name.as_str()).collect();
        assert_eq!(
            names,
            [
                "Exposed",
                "Global",
                "LegacyFactoryFunction",
                "Constructor",
                "Exposed",
                "SecureContext"
            ]
        );
        assert_eq!(
            ext.first().map(|e| e.value.clone()),
            Some(ExtValue::IdentList(vec!["Window".into(), "Worker".into()]))
        );
        assert_eq!(
            ext.get(4).map(|e| e.value.clone()),
            Some(ExtValue::Wildcard)
        );
        assert!(matches!(
            ext.get(2).map(|e| &e.value),
            Some(ExtValue::NamedArgs(n, a)) if n == "Image" && a.len() == 1
        ));
        Ok(())
    }

    #[test]
    fn extended_attributes_on_types_and_arguments() -> Result<(), String> {
        let t = ty("[Clamp] long");
        assert_eq!(t.ext.len(), 1);
        let Definition::Interface { members, .. } = one(
            "interface I { undefined f([EnforceRange] unsigned long a, [AllowShared] BufferSource b); };",
        )?
        else {
            return Err("not an interface".into());
        };
        assert_eq!(members.len(), 1);
        Ok(())
    }

    #[test]
    fn keywords_as_names_and_escaped_identifiers() {
        // ArgumentNameKeyword, AttributeNameKeyword, OperationNameKeyword.
        assert!(parse("interface I { undefined includes(long required, long async, long interface); attribute long async; attribute long required; };").is_ok());
        // Not a keyword the grammar allows there.
        assert!(parse("interface I { attribute long long; };").is_err());
        assert!(parse("interface I { attribute long record; };").is_err());
        // An underscore escapes any keyword.
        assert!(parse("interface _interface { attribute long _record; };").is_ok());
        assert!(parse("interface I { undefined f(long sequence); };").is_err());
    }

    #[test]
    fn operations_specials_and_members() -> Result<(), String> {
        let src = "interface I : P {
            constructor();
            constructor(long a, optional long b = 1, DOMString... rest);
            getter any (DOMString name);
            setter undefined (DOMString name, any v);
            deleter undefined (DOMString name);
            stringifier;
            stringifier attribute USVString href;
            static undefined s();
            static readonly attribute long sa;
            inherit attribute DOMString ia;
            readonly attribute long ro;
            const unsigned short C = 0x1F;
            const double D = -Infinity;
            iterable<long>;
            async iterable<DOMString, long>(optional long x);
            maplike<DOMString, long>;
            readonly setlike<long>;
        };";
        let Definition::Interface {
            parent, members, ..
        } = one(src)?
        else {
            return Err("not an interface".into());
        };
        assert_eq!(parent.as_deref(), Some("P"));
        assert_eq!(members.len(), 17);
        assert!(matches!(
            members.get(1).map(|m| &m.kind),
            Some(MemberKind::Constructor(a)) if a.len() == 3
                && a.get(2).is_some_and(|x| x.variadic)
                && a.get(1).is_some_and(|x| x.default == Some(Value::Integer(1)))
        ));
        assert!(matches!(
            members.get(11).map(|m| &m.kind),
            Some(MemberKind::Const(c)) if c.value == Value::Integer(31)
        ));
        assert!(matches!(
            members.get(12).map(|m| &m.kind),
            Some(MemberKind::Const(c)) if c.value == Value::NegInfinity
        ));
        assert!(matches!(
            members.get(14).map(|m| &m.kind),
            Some(MemberKind::Iterable(i)) if i.is_async && i.key.is_some() && i.args.len() == 1
        ));
        assert!(matches!(
            members.get(16).map(|m| &m.kind),
            Some(MemberKind::Collection(c)) if !c.is_map && c.readonly
        ));
        Ok(())
    }

    #[test]
    fn containers_restrict_their_members() {
        assert!(parse("partial interface I { constructor(); };").is_err());
        assert!(parse("interface mixin M { constructor(); };").is_err());
        assert!(parse("interface mixin M { static undefined f(); };").is_err());
        assert!(parse("interface mixin M { getter any (DOMString n); };").is_err());
        assert!(parse("interface mixin M { readonly attribute long a; stringifier; const long C = 1; undefined f(); };").is_ok());
        assert!(parse("callback interface C { attribute long a; };").is_err());
        assert!(parse("callback interface C { const long K = 1; undefined f(); };").is_ok());
        assert!(parse("namespace N { attribute long a; };").is_err());
        assert!(
            parse("namespace N { readonly attribute long a; undefined f(); const long K = 1; };")
                .is_ok()
        );
        assert!(parse("interface I { iterable<long>; };").is_ok());
        assert!(parse("interface mixin M { iterable<long>; };").is_err());
    }

    #[test]
    fn dictionaries_enums_typedefs_callbacks_includes() {
        let defs = parse(
            "dictionary D : B { required long a; [Clamp] octet b = 1; DOMString c = \"x\"; sequence<long> d = []; E e = {}; any f = null; any g; unrestricted double h = NaN; double i = 1.5e3; boolean j = true; };
             partial dictionary D { long k; };
             enum E { \"a\", \"b-c\", \"\", };
             typedef (long or DOMString)? T;
             callback CB = undefined (long a, optional any b);
             callback interface CI { undefined f(); };
             namespace N { };
             partial namespace N { readonly attribute long x; };
             X includes M;
             interface mixin M { };
             partial interface mixin M { };",
        )
        .unwrap_or_default();
        assert_eq!(defs.len(), 11);
        assert!(matches!(
            defs.first(),
            Some(Definition::Dictionary { parent: Some(p), members, .. }) if p == "B" && members.len() == 10
        ));
        assert!(matches!(
            defs.get(2),
            Some(Definition::Enum { values, .. }) if values == &["a", "b-c", ""]
        ));
        assert!(matches!(defs.get(3), Some(Definition::Typedef { ty, .. }) if ty.nullable));
        assert!(
            matches!(defs.get(8), Some(Definition::Includes { target, mixin }) if target == "X" && mixin == "M")
        );
        assert!(matches!(
            defs.get(1),
            Some(Definition::Dictionary { partial: true, .. })
        ));
    }

    #[test]
    fn rejects_malformed_input_with_a_line() {
        let e = parse("interface I {\n  attribute long\n};")
            .err()
            .unwrap_or_default();
        assert!(e.starts_with("3: "), "{e}");
        assert!(parse("interface I { };").is_ok());
        assert!(parse("interface I { }").is_err());
        assert!(parse("enum E { };").is_err());
        assert!(parse("[Exposed=Window] X includes Y;").is_err());
        assert!(parse("partial enum E { \"a\" };").is_err());
    }
}
