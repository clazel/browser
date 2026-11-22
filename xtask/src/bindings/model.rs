//! The IDL model: what the parser produces for one file and what the
//! resolver produces for all of them (`resolve.rs`). The crate's
//! `clazel-webidl/src/model.rs` holds the same shapes as `'static` data;
//! `emit.rs` maps one to the other.

/// An extended attribute (WebIDL §2.2 "Extended attributes"), in one of the
/// forms of that section.
#[derive(Debug, Clone, PartialEq)]
pub struct ExtAttr {
    /// Its name (`ExtendedAttributeNoArgs`'s identifier).
    pub name: String,
    /// What follows the name.
    pub value: ExtValue,
}

/// What follows an extended attribute's name.
#[derive(Debug, Clone, PartialEq)]
pub enum ExtValue {
    /// `[Name]`.
    None,
    /// `[Name=identifier]`.
    Ident(String),
    /// `[Name=(identifier, identifier)]`.
    IdentList(Vec<String>),
    /// `[Name=*]`.
    Wildcard,
    /// `[Name=1]`, `[Name=1.5]` or `[Name="s"]`.
    Literal(Value),
    /// `[Name=(0, 8)]`: a list of integer, decimal or string literals.
    LiteralList(Vec<Value>),
    /// `[Name(arguments)]`.
    Args(Vec<Argument>),
    /// `[Name=identifier(arguments)]`.
    NamedArgs(String, Vec<Argument>),
}

/// Types the grammar spells with keywords alone.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Simple {
    Any,
    Undefined,
    Boolean,
    Byte,
    Octet,
    Bigint,
    Object,
    Symbol,
    Short,
    UnsignedShort,
    Long,
    UnsignedLong,
    LongLong,
    UnsignedLongLong,
    Float,
    UnrestrictedFloat,
    Double,
    UnrestrictedDouble,
    ByteString,
    DomString,
    UsvString,
}

/// A type without its nullability and extended attributes.
#[derive(Debug, Clone, PartialEq)]
pub enum TyKind {
    /// A keyword type.
    Simple(Simple),
    /// A buffer-related type (`ArrayBuffer`, `Uint8Array`, ...), by name.
    Buffer(String),
    /// An identifier: an interface, dictionary, enum, typedef or callback.
    Named(String),
    /// `sequence<T>`.
    Sequence(Box<Ty>),
    /// `FrozenArray<T>`.
    FrozenArray(Box<Ty>),
    /// `ObservableArray<T>`.
    ObservableArray(Box<Ty>),
    /// `record<K, V>`.
    Record(Box<Ty>, Box<Ty>),
    /// `Promise<T>`.
    Promise(Box<Ty>),
    /// `(A or B or ...)`.
    Union(Vec<Ty>),
}

/// A type with its nullability and the extended attributes written on it.
#[derive(Debug, Clone, PartialEq)]
pub struct Ty {
    /// The type.
    pub kind: TyKind,
    /// Followed by `?`.
    pub nullable: bool,
    /// `[Clamp] long` and the like.
    pub ext: Vec<ExtAttr>,
}

/// A literal: a constant's value or a default.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// `true` or `false`.
    Bool(bool),
    /// An integer, in the value its lexeme has (`0x10` is 16).
    Integer(i128),
    /// A decimal, as written.
    Decimal(String),
    /// `Infinity`.
    Infinity,
    /// `-Infinity`.
    NegInfinity,
    /// `NaN`.
    NaN,
    /// A string, without the quotes.
    Str(String),
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
#[derive(Debug, Clone, PartialEq)]
pub struct Argument {
    /// Extended attributes before it.
    pub ext: Vec<ExtAttr>,
    /// Its name.
    pub name: String,
    /// Its type.
    pub ty: Ty,
    /// `optional`.
    pub optional: bool,
    /// `...`.
    pub variadic: bool,
    /// `= value`.
    pub default: Option<Value>,
}

/// `const T NAME = value;`.
#[derive(Debug, Clone, PartialEq)]
pub struct Const {
    /// Its name.
    pub name: String,
    /// Its type.
    pub ty: Ty,
    /// Its value.
    pub value: Value,
}

/// An attribute.
#[derive(Debug, Clone, PartialEq)]
pub struct Attribute {
    /// Its name.
    pub name: String,
    /// Its type.
    pub ty: Ty,
    /// `readonly`.
    pub readonly: bool,
    /// `inherit`.
    pub inherit: bool,
    /// `static`.
    pub is_static: bool,
    /// `stringifier`.
    pub stringifier: bool,
}

/// What kind of operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpKind {
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
#[derive(Debug, Clone, PartialEq)]
pub struct Operation {
    /// Its name, if it has one.
    pub name: Option<String>,
    /// Its kind.
    pub kind: OpKind,
    /// Its return type.
    pub ret: Ty,
    /// Its arguments.
    pub args: Vec<Argument>,
}

/// `iterable<...>` or `async iterable<...>`.
#[derive(Debug, Clone, PartialEq)]
pub struct Iterable {
    /// `async iterable`.
    pub is_async: bool,
    /// The key type of the pair form.
    pub key: Option<Ty>,
    /// The value type.
    pub value: Ty,
    /// The arguments of `async iterable<...>(...)`.
    pub args: Vec<Argument>,
}

/// `maplike<K, V>` or `setlike<T>`.
#[derive(Debug, Clone, PartialEq)]
pub struct Collection {
    /// `maplike` (else `setlike`).
    pub is_map: bool,
    /// `readonly`.
    pub readonly: bool,
    /// The key type of a maplike.
    pub key: Option<Ty>,
    /// The value type (the element of a setlike).
    pub value: Ty,
}

/// What a member is.
#[derive(Debug, Clone, PartialEq)]
pub enum MemberKind {
    /// A constant.
    Const(Const),
    /// An attribute.
    Attribute(Attribute),
    /// An operation.
    Operation(Operation),
    /// `constructor(...)`, with its arguments.
    Constructor(Vec<Argument>),
    /// An iterable or async iterable.
    Iterable(Iterable),
    /// A maplike or setlike.
    Collection(Collection),
}

/// A member of an interface, mixin, callback interface or namespace.
#[derive(Debug, Clone, PartialEq)]
pub struct Member {
    /// Its extended attributes (after resolution, with those a partial or
    /// mixin passes on, `resolve.rs`).
    pub ext: Vec<ExtAttr>,
    /// What it is.
    pub kind: MemberKind,
    /// The mixin it came from through `includes`; set by the resolver.
    pub mixin: Option<String>,
}

/// A dictionary member.
#[derive(Debug, Clone, PartialEq)]
pub struct DictMember {
    /// Its extended attributes.
    pub ext: Vec<ExtAttr>,
    /// Its name.
    pub name: String,
    /// Its type.
    pub ty: Ty,
    /// `required`.
    pub required: bool,
    /// `= value`.
    pub default: Option<Value>,
}

/// One top-level definition of a file (WebIDL §2 `Definition`).
#[derive(Debug, Clone, PartialEq)]
pub enum Definition {
    /// `interface`, `partial interface` and `callback interface`.
    Interface {
        /// Extended attributes.
        ext: Vec<ExtAttr>,
        /// Name.
        name: String,
        /// The `: Parent`.
        parent: Option<String>,
        /// `partial`.
        partial: bool,
        /// `callback interface`.
        callback: bool,
        /// Members.
        members: Vec<Member>,
    },
    /// `interface mixin` and `partial interface mixin`.
    Mixin {
        /// Extended attributes.
        ext: Vec<ExtAttr>,
        /// Name.
        name: String,
        /// `partial`.
        partial: bool,
        /// Members.
        members: Vec<Member>,
    },
    /// `namespace` and `partial namespace`.
    Namespace {
        /// Extended attributes.
        ext: Vec<ExtAttr>,
        /// Name.
        name: String,
        /// `partial`.
        partial: bool,
        /// Members.
        members: Vec<Member>,
    },
    /// `dictionary` and `partial dictionary`.
    Dictionary {
        /// Extended attributes.
        ext: Vec<ExtAttr>,
        /// Name.
        name: String,
        /// The `: Parent`.
        parent: Option<String>,
        /// `partial`.
        partial: bool,
        /// Members.
        members: Vec<DictMember>,
    },
    /// `enum`.
    Enum {
        /// Extended attributes.
        ext: Vec<ExtAttr>,
        /// Name.
        name: String,
        /// Values.
        values: Vec<String>,
    },
    /// `typedef`.
    Typedef {
        /// Extended attributes.
        ext: Vec<ExtAttr>,
        /// Name.
        name: String,
        /// The aliased type.
        ty: Ty,
    },
    /// `callback Name = Return (args);`.
    Callback {
        /// Extended attributes.
        ext: Vec<ExtAttr>,
        /// Name.
        name: String,
        /// Return type.
        ret: Ty,
        /// Arguments.
        args: Vec<Argument>,
    },
    /// `Target includes Mixin;`.
    Includes {
        /// The interface.
        target: String,
        /// The mixin.
        mixin: String,
    },
}
