//! The resolved WebIDL model as plain `'static` data (phase-7.md item 7.12).
//!
//! `cargo xtask bindings` (`xtask/src/bindings/`) parses the vendored IDL
//! with the grammar of WebIDL §2, merges partial interfaces, mixins and
//! `includes` (`xtask/src/bindings/resolve.rs` lists the rules), and writes
//! the result into [`crate::generated`] as values of these types. The types
//! hold no behaviour: the binding glue that the embedding API of `clazel-js`
//! (item 7.8) allows is generated from this data later.

/// An extended attribute: `[Name]`, `[Name=Ident]`, `[Name=(A, B)]`,
/// `[Name=*]`, `[Name(args)]`, `[Name=Ident(args)]` or `[Name=literal]`
/// (WebIDL §2.2).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ExtAttr {
    /// Its name.
    pub name: &'static str,
    /// What follows the name.
    pub value: ExtValue,
}

/// What follows an extended attribute's name.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExtValue {
    /// `[Name]`.
    None,
    /// `[Name=Ident]`.
    Ident(&'static str),
    /// `[Name=(A, B)]`.
    IdentList(&'static [&'static str]),
    /// `[Name=*]`.
    Wildcard,
    /// `[Name=1]`, `[Name=1.5]` or `[Name="s"]`.
    Literal(Value),
    /// `[Name=(0, 8)]`: literals.
    LiteralList(&'static [Value]),
    /// `[Name(args)]`.
    Args(&'static [Argument]),
    /// `[Name=Ident(args)]`.
    NamedArgs(&'static str, &'static [Argument]),
}

/// A type that the grammar spells with keywords alone.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Simple {
    /// `any`.
    Any,
    /// `undefined`.
    Undefined,
    /// `boolean`.
    Boolean,
    /// `byte`.
    Byte,
    /// `octet`.
    Octet,
    /// `bigint`.
    Bigint,
    /// `object`.
    Object,
    /// `symbol`.
    Symbol,
    /// `short`.
    Short,
    /// `unsigned short`.
    UnsignedShort,
    /// `long`.
    Long,
    /// `unsigned long`.
    UnsignedLong,
    /// `long long`.
    LongLong,
    /// `unsigned long long`.
    UnsignedLongLong,
    /// `float`.
    Float,
    /// `unrestricted float`.
    UnrestrictedFloat,
    /// `double`.
    Double,
    /// `unrestricted double`.
    UnrestrictedDouble,
    /// `ByteString`.
    ByteString,
    /// `DOMString`.
    DomString,
    /// `USVString`.
    UsvString,
}

/// A type without its nullability and extended attributes.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Type {
    /// A keyword type.
    Simple(Simple),
    /// A buffer-related type (`ArrayBuffer`, `Uint8Array`, ...), by name.
    Buffer(&'static str),
    /// An identifier: an interface, dictionary, enum, typedef or callback,
    /// or a name in [`crate::generated::EXTERNAL`].
    Named(&'static str),
    /// `sequence<T>`.
    Sequence(&'static TypeRef),
    /// `FrozenArray<T>`.
    FrozenArray(&'static TypeRef),
    /// `ObservableArray<T>`.
    ObservableArray(&'static TypeRef),
    /// `record<K, V>`.
    Record(&'static TypeRef, &'static TypeRef),
    /// `Promise<T>`.
    Promise(&'static TypeRef),
    /// `(A or B or ...)`.
    Union(&'static [TypeRef]),
}

/// A type with its nullability and the extended attributes written on it.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TypeRef {
    /// The type.
    pub ty: Type,
    /// Followed by `?`.
    pub nullable: bool,
    /// `[Clamp] long` and the like.
    pub ext_attrs: &'static [ExtAttr],
}

/// A literal: a constant's value or a default.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    /// `true` or `false`.
    Bool(bool),
    /// An integer, in the value its lexeme has (`0x10` is 16).
    Integer(i128),
    /// A decimal, as written.
    Decimal(&'static str),
    /// `Infinity`.
    Infinity,
    /// `-Infinity`.
    NegInfinity,
    /// `NaN`.
    NaN,
    /// A string, without the quotes.
    Str(&'static str),
    /// `[]`.
    EmptySequence,
    /// `{}`.
    EmptyDictionary,
    /// `null`.
    Null,
    /// `undefined`.
    Undefined,
}

/// An operation's or constructor's argument.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Argument {
    /// Its name.
    pub name: &'static str,
    /// Its type.
    pub ty: TypeRef,
    /// `optional`.
    pub optional: bool,
    /// `...`.
    pub variadic: bool,
    /// `= value`.
    pub default: Option<Value>,
    /// Extended attributes on the argument.
    pub ext_attrs: &'static [ExtAttr],
}

/// `const T NAME = value;`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Constant {
    /// Its name.
    pub name: &'static str,
    /// Its type.
    pub ty: TypeRef,
    /// Its value.
    pub value: Value,
    /// The mixin it came from, if it came through `includes`.
    pub mixin: Option<&'static str>,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
}

/// An attribute.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Attribute {
    /// Its name.
    pub name: &'static str,
    /// Its type.
    pub ty: TypeRef,
    /// `readonly`.
    pub readonly: bool,
    /// `inherit`.
    pub inherit: bool,
    /// `static`.
    pub is_static: bool,
    /// `stringifier attribute`.
    pub stringifier: bool,
    /// The mixin it came from, if it came through `includes`.
    pub mixin: Option<&'static str>,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
}

/// What kind of operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperationKind {
    /// A regular operation.
    Regular,
    /// `static`.
    Static,
    /// `getter`.
    Getter,
    /// `setter`.
    Setter,
    /// `deleter`.
    Deleter,
    /// `stringifier;`.
    Stringifier,
}

/// An operation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Operation {
    /// Its name; special operations may have none.
    pub name: Option<&'static str>,
    /// Its kind.
    pub kind: OperationKind,
    /// Its return type.
    pub ret: TypeRef,
    /// Its arguments.
    pub args: &'static [Argument],
    /// The mixin it came from, if it came through `includes`.
    pub mixin: Option<&'static str>,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
}

/// `constructor(...)`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Constructor {
    /// Its arguments.
    pub args: &'static [Argument],
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
}

/// `iterable<...>` or `async iterable<...>`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Iterable {
    /// `async iterable`.
    pub is_async: bool,
    /// The key type of the pair form.
    pub key: Option<TypeRef>,
    /// The value type.
    pub value: TypeRef,
    /// The arguments of `async iterable<...>(...)`.
    pub args: &'static [Argument],
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
}

/// `maplike<K, V>` or `setlike<T>`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Collection {
    /// `maplike` (else `setlike`).
    pub is_map: bool,
    /// `readonly`.
    pub readonly: bool,
    /// The key type of a maplike.
    pub key: Option<TypeRef>,
    /// The value type (the element type of a setlike).
    pub value: TypeRef,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
}

/// A resolved interface or callback interface: its own members, then those of
/// its partial interfaces, then those of the mixins it includes (each of
/// those marked with its mixin).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Interface {
    /// Its name.
    pub name: &'static str,
    /// The interface it inherits from.
    pub parent: Option<&'static str>,
    /// `callback interface`.
    pub callback: bool,
    /// Its own extended attributes.
    pub ext_attrs: &'static [ExtAttr],
    /// The mixins it includes, in order (a name in
    /// [`crate::generated::EXTERNAL`] has no members here).
    pub includes: &'static [&'static str],
    /// `constructor(...)` declarations.
    pub constructors: &'static [Constructor],
    /// Constants.
    pub constants: &'static [Constant],
    /// Attributes, static ones included.
    pub attributes: &'static [Attribute],
    /// Operations, special, static and stringifier ones included.
    pub operations: &'static [Operation],
    /// Its `iterable` or `async iterable`.
    pub iterable: Option<Iterable>,
    /// Its `maplike` or `setlike`.
    pub collection: Option<Collection>,
}

/// A resolved namespace.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Namespace {
    /// Its name.
    pub name: &'static str,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
    /// Constants.
    pub constants: &'static [Constant],
    /// Readonly attributes.
    pub attributes: &'static [Attribute],
    /// Operations.
    pub operations: &'static [Operation],
}

/// A dictionary member.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DictionaryMember {
    /// Its name.
    pub name: &'static str,
    /// Its type.
    pub ty: TypeRef,
    /// `required`.
    pub required: bool,
    /// `= value`.
    pub default: Option<Value>,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
}

/// A resolved dictionary: its own members, then those of its partials. The
/// members of its parent are not copied in.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Dictionary {
    /// Its name.
    pub name: &'static str,
    /// The dictionary it inherits from.
    pub parent: Option<&'static str>,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
    /// Its members.
    pub members: &'static [DictionaryMember],
}

/// An enum.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Enumeration {
    /// Its name.
    pub name: &'static str,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
    /// Its values, in order.
    pub values: &'static [&'static str],
}

/// A typedef.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Typedef {
    /// Its name.
    pub name: &'static str,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
    /// The type it names.
    pub ty: TypeRef,
}

/// A callback function type: `callback Name = Return (args);`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Callback {
    /// Its name.
    pub name: &'static str,
    /// Its extended attributes.
    pub ext_attrs: &'static [ExtAttr],
    /// Its return type.
    pub ret: TypeRef,
    /// Its arguments.
    pub args: &'static [Argument],
}

/// A name the IDL refers to that another standard defines, whose IDL is not
/// vendored.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct External {
    /// Its name.
    pub name: &'static str,
    /// The standard that defines it.
    pub defined_by: &'static str,
}

/// An `includes` statement whose interface another standard defines: the
/// statement is kept, the interface is not in the model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ForeignIncludes {
    /// The interface (in [`crate::generated::EXTERNAL`]).
    pub interface: &'static str,
    /// The mixin it includes.
    pub mixin: &'static str,
}

/// The first extended attribute named `name` in `attrs`.
#[must_use]
pub fn ext_attr(attrs: &'static [ExtAttr], name: &str) -> Option<&'static ExtAttr> {
    attrs.iter().find(|a| a.name == name)
}

/// Find the item named `name` in a table sorted by name.
fn find<T>(table: &'static [T], name: &str, key: impl Fn(&T) -> &str) -> Option<&'static T> {
    table
        .binary_search_by(|item| key(item).cmp(name))
        .ok()
        .and_then(|i| table.get(i))
}

/// The interface (or callback interface) named `name`.
#[must_use]
pub fn interface(name: &str) -> Option<&'static Interface> {
    find(crate::generated::INTERFACES, name, |i| i.name)
}

/// The namespace named `name`.
#[must_use]
pub fn namespace(name: &str) -> Option<&'static Namespace> {
    find(crate::generated::NAMESPACES, name, |i| i.name)
}

/// The dictionary named `name`.
#[must_use]
pub fn dictionary(name: &str) -> Option<&'static Dictionary> {
    find(crate::generated::DICTIONARIES, name, |i| i.name)
}

/// The enum named `name`.
#[must_use]
pub fn enumeration(name: &str) -> Option<&'static Enumeration> {
    find(crate::generated::ENUMS, name, |i| i.name)
}

/// The typedef named `name`.
#[must_use]
pub fn typedef(name: &str) -> Option<&'static Typedef> {
    find(crate::generated::TYPEDEFS, name, |i| i.name)
}

/// The callback function type named `name`.
#[must_use]
pub fn callback(name: &str) -> Option<&'static Callback> {
    find(crate::generated::CALLBACKS, name, |i| i.name)
}
