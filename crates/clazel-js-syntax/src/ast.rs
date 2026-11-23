//! The arena AST of ECMAScript scripts and modules (phase-7.md item 7.3).
//!
//! An [`Ast`] is a `Vec` of [`Node`]s. A node names its children by index
//! into that `Vec` (a [`NodeId`]); the root is the last node, and every
//! child has a smaller index than its parent (the arena is built bottom-up,
//! as a parser finishes a production after its parts). So the tree needs no
//! pointers, no `Box` and no recursion to drop, and a walk can go forward or
//! backward over the arena without a stack. The checks that an `Ast` is a
//! well-formed arena are in `spec::ast_wf`, and what it takes for one to be
//! a parse of a source text is in `spec::is_parse`.
//!
//! # Shape
//!
//! Every node has a [`NodeKind`] named after the ECMA-262 production it is
//! an instance of, an [`Op`] and a `flag` for the few facts that a production
//! has alternatives for (the operator of `AdditiveExpression`, `var` against
//! `let` against `const`, `static` in a `ClassElement`), a span into the
//! source text, and an ordered list of children. The variant docs give each
//! kind's children layout; `spec::derives` is the normative statement, and
//! the two agree.
//!
//! - **A span** is `start..end` in code points of the source text: `start`
//!   is the first code point of the node's first token and `end` is one past
//!   the last code point of its last token (white space and comments between
//!   tokens are inside a node's span, and outside it at the ends). A node
//!   with no token has the empty span at the end of the token before it.
//! - **An absent optional symbol** (`Expression?`, `BindingIdentifier?`) is a
//!   child of kind [`NodeKind::Absent`], whose span is empty, so a kind's
//!   children layout has a fixed length where the production has fixed
//!   positions. A list (statements, arguments, properties) has one child
//!   per item.
//! - **Names, values and literal text** are not stored: they are the source
//!   text of a node's span, and a consumer asks the lexer for them (an
//!   identifier's code points, a string's value, a number's value). Nothing
//!   in the AST can disagree with the source text.
//! - **Cover grammars** (§13.2.5.1 and friends) are not in the AST: it holds
//!   the refined production the parse selected, for example an
//!   [`NodeKind::ObjectAssignmentPattern`] where the text is the left side of
//!   an `=`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The index of a node in [`Ast::nodes`].
pub type NodeId = u32;

/// The production a node is an instance of. A kind's doc comment gives the
/// ECMA-262 production(s) and the children layout.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NodeKind {
    // ----- Roots and statements (§16, §14) ---------------------------------
    /// §16.1 `Script`: `ScriptBody?`. Children: the `StatementListItem`s.
    Script,
    /// §16.2 `Module`: `ModuleBody?`. Children: the `ModuleItem`s.
    Module,
    /// §14.2 `Block`: `{ StatementList? }`. Children: the statements.
    BlockStatement,
    /// §14.3.2 `VariableStatement`: `var VariableDeclarationList ;`.
    /// Children: the `VariableDeclaration`s.
    VariableStatement,
    /// §14.3.2 `VariableDeclarationList` as the head of a `for ( var ...`
    /// statement: `var` and the declarations, without the `;`. The span
    /// starts at `var`. Children: the `VariableDeclaration`s.
    VariableDeclarationList,
    /// §14.3.2 `VariableDeclaration`: `BindingIdentifier Initializer?` or
    /// `BindingPattern Initializer`. Children: the target, the initializer
    /// (an `AssignmentExpression`) or [`NodeKind::Absent`].
    VariableDeclaration,
    /// §14.3.1 `LexicalDeclaration`: `LetOrConst BindingList ;`. [`Op`]
    /// `Let` or `Const`. Children: the `LexicalBinding`s.
    LexicalDeclaration,
    /// §14.3.1 `LexicalBinding`: as `VariableDeclaration`. Children: the
    /// target, the initializer or [`NodeKind::Absent`].
    LexicalBinding,
    /// §14.4 `EmptyStatement`: `;`. No children.
    EmptyStatement,
    /// §14.5 `ExpressionStatement`: `Expression ;`. Children: the expression.
    ExpressionStatement,
    /// §14.6 `IfStatement`. Children: the test, the consequent, the
    /// alternate or [`NodeKind::Absent`].
    IfStatement,
    /// §14.7.2 `DoWhileStatement`. Children: the body, the test.
    DoWhileStatement,
    /// §14.7.3 `WhileStatement`. Children: the test, the body.
    WhileStatement,
    /// §14.7.4 `ForStatement`. Children: the initializer (an `Expression`,
    /// a [`NodeKind::VariableDeclarationList`], a
    /// [`NodeKind::LexicalDeclaration`] or [`NodeKind::Absent`]), the test,
    /// the update (each an `Expression` or [`NodeKind::Absent`]), the body.
    ForStatement,
    /// §14.7.5 `for ( ... in ... )`. Children: the head (a
    /// [`NodeKind::ForDeclaration`] or a `LeftHandSideExpression` or
    /// assignment pattern), the expression, the body.
    ForInStatement,
    /// §14.7.5 `for ( ... of ... )` and `for await ( ... of ... )` (`flag`).
    /// Children: as `ForInStatement`.
    ForOfStatement,
    /// §14.7.5 `ForDeclaration`: `LetOrConst ForBinding`, and the `var
    /// ForBinding` of `for ( var ForBinding in ...`. [`Op`] `Var`, `Let` or
    /// `Const`. Children: the binding (a `BindingIdentifier` or
    /// `BindingPattern`), or, for Annex B.3.5's `for (var a = 1 in x)`, a
    /// [`NodeKind::VariableDeclaration`].
    ForDeclaration,
    /// §14.8 `ContinueStatement`. Children: the `LabelIdentifier` or
    /// [`NodeKind::Absent`].
    ContinueStatement,
    /// §14.9 `BreakStatement`. Children: the `LabelIdentifier` or
    /// [`NodeKind::Absent`].
    BreakStatement,
    /// §14.10 `ReturnStatement`. Children: the expression or
    /// [`NodeKind::Absent`].
    ReturnStatement,
    /// §14.11 `WithStatement`. Children: the object, the body.
    WithStatement,
    /// §14.12 `SwitchStatement`. Children: the discriminant, then the
    /// `CaseClause`s and `DefaultClause` of the `CaseBlock`, in order.
    SwitchStatement,
    /// §14.12 `CaseClause`: `case Expression : StatementList?`. Children:
    /// the test, then the statements.
    CaseClause,
    /// §14.12 `DefaultClause`: `default : StatementList?`. Children: the
    /// statements.
    DefaultClause,
    /// §14.13 `LabelledStatement`. Children: the `LabelIdentifier`, the
    /// body (a statement, or a function declaration under Annex B.3.2).
    LabelledStatement,
    /// §14.14 `ThrowStatement`. Children: the expression.
    ThrowStatement,
    /// §14.15 `TryStatement`. Children: the block, the `Catch` or
    /// [`NodeKind::Absent`], the `Finally` or [`NodeKind::Absent`].
    TryStatement,
    /// §14.15 `Catch`. Children: the parameter (a `CatchParameter`) or
    /// [`NodeKind::Absent`], the block.
    Catch,
    /// §14.15 `Finally`. Children: the block.
    Finally,
    /// §14.16 `DebuggerStatement`. No children.
    DebuggerStatement,

    // ----- Functions and classes (§15) ------------------------------------
    /// §15.2 `FunctionDeclaration`. Children: the `BindingIdentifier` (or
    /// [`NodeKind::Absent`] for `export default function`), the
    /// `FormalParameters`, the `FunctionBody`.
    FunctionDeclaration,
    /// §15.2 `FunctionExpression`. Children: as `FunctionDeclaration`.
    FunctionExpression,
    /// §15.5 `GeneratorDeclaration`. Children: as `FunctionDeclaration`.
    GeneratorDeclaration,
    /// §15.5 `GeneratorExpression`. Children: as `FunctionDeclaration`.
    GeneratorExpression,
    /// §15.8 `AsyncFunctionDeclaration`. Children: as `FunctionDeclaration`.
    AsyncFunctionDeclaration,
    /// §15.8 `AsyncFunctionExpression`. Children: as `FunctionDeclaration`.
    AsyncFunctionExpression,
    /// §15.6 `AsyncGeneratorDeclaration`. Children: as `FunctionDeclaration`.
    AsyncGeneratorDeclaration,
    /// §15.6 `AsyncGeneratorExpression`. Children: as `FunctionDeclaration`.
    AsyncGeneratorExpression,
    /// §15.1 `FormalParameters` (and `UniqueFormalParameters`,
    /// `ArrowFormalParameters`, `PropertySetParameterList`): its span runs
    /// from the `(` to the `)`, both included. Children: the `BindingElement`
    /// per parameter, then a `FunctionRestParameter` if any.
    FormalParameters,
    /// §15.1 `FunctionRestParameter`: `... BindingRestElement`. Children:
    /// the target (a `BindingIdentifier` or `BindingPattern`).
    FunctionRestParameter,
    /// §15.1 `FunctionBody` (and `GeneratorBody`, `AsyncFunctionBody`,
    /// `AsyncGeneratorBody`, `ConciseBody`'s braced form, `ClassStaticBlockBody`):
    /// its span runs from the `{` to the `}`, both included. Children: the
    /// statements.
    FunctionBody,
    /// §15.3 `ArrowFunction`. Children: the parameters (a `BindingIdentifier`
    /// or `FormalParameters`), the body (an `AssignmentExpression` or a
    /// `FunctionBody`).
    ArrowFunction,
    /// §15.9 `AsyncArrowFunction`. Children: as `ArrowFunction`.
    AsyncArrowFunction,
    /// §15.4 `MethodDefinition` (and `GeneratorMethod`, `AsyncMethod`,
    /// `AsyncGeneratorMethod`). [`Op`] `Method`, `Getter`, `Setter`,
    /// `GeneratorMethod`, `AsyncMethod` or `AsyncGeneratorMethod`; `flag` is
    /// `static` for a `ClassElement`. Children: the `ClassElementName` or
    /// `PropertyName`, the `FormalParameters`, the `FunctionBody`.
    MethodDefinition,
    /// §15.7 `ClassDeclaration`. Children: the `BindingIdentifier` (or
    /// [`NodeKind::Absent`] for `export default class`), the
    /// `ClassHeritage`'s `LeftHandSideExpression` or [`NodeKind::Absent`],
    /// the `ClassBody`.
    ClassDeclaration,
    /// §15.7 `ClassExpression`. Children: as `ClassDeclaration`.
    ClassExpression,
    /// §15.7 `ClassBody`: `{ ClassElementList? }`. Children: the
    /// `ClassElement`s that are not `;`: `MethodDefinition`,
    /// `FieldDefinition`, `ClassStaticBlock`.
    ClassBody,
    /// §15.7 `FieldDefinition` as a `ClassElement`: `static? FieldDefinition
    /// ;`. `flag` is `static`. Children: the `ClassElementName`, the
    /// initializer or [`NodeKind::Absent`].
    FieldDefinition,
    /// §15.7 `ClassStaticBlock`: `static { ClassStaticBlockBody }`.
    /// Children: the `FunctionBody` (the `ClassStaticBlockBody`).
    ClassStaticBlock,

    // ----- Patterns (§13.15.5, §14.3.3) --------------------------------------
    /// §14.3.3 `ObjectBindingPattern`. Children: the `BindingProperty`s, then
    /// a `BindingRestProperty` if any.
    ObjectBindingPattern,
    /// §14.3.3 `ArrayBindingPattern`. Children: the `BindingElement`s and
    /// [`NodeKind::Elision`]s, then a `BindingRestElement` if any.
    ArrayBindingPattern,
    /// §14.3.3 `BindingProperty`: `SingleNameBinding` or `PropertyName :
    /// BindingElement`. [`Op`] `Shorthand` (children: the `BindingElement`,
    /// whose target is a `BindingIdentifier`) or `KeyValue` (children: the
    /// `PropertyName`, the `BindingElement`).
    BindingProperty,
    /// §14.3.3 `BindingElement` (and `SingleNameBinding`). Children: the
    /// target (a `BindingIdentifier` or `BindingPattern`), the initializer or
    /// [`NodeKind::Absent`].
    BindingElement,
    /// §14.3.3 `BindingRestElement`: `... BindingIdentifier` or `...
    /// BindingPattern`. Children: the target.
    BindingRestElement,
    /// §14.3.3 `BindingRestProperty`: `... BindingIdentifier`. Children: the
    /// `BindingIdentifier`.
    BindingRestProperty,
    /// §13.15.5 `ObjectAssignmentPattern`. Children: the `AssignmentProperty`s,
    /// then an `AssignmentRestProperty` if any.
    ObjectAssignmentPattern,
    /// §13.15.5 `ArrayAssignmentPattern`. Children: the `AssignmentElement`s
    /// and [`NodeKind::Elision`]s, then an `AssignmentRestElement` if any.
    ArrayAssignmentPattern,
    /// §13.15.5 `AssignmentProperty`. [`Op`] `Shorthand` (children: the
    /// `IdentifierReference`, the initializer or [`NodeKind::Absent`]) or
    /// `KeyValue` (children: the `PropertyName`, the `AssignmentElement`).
    AssignmentProperty,
    /// §13.15.5 `AssignmentElement`: `DestructuringAssignmentTarget
    /// Initializer?`. Children: the target (a `LeftHandSideExpression` or an
    /// assignment pattern), the initializer or [`NodeKind::Absent`].
    AssignmentElement,
    /// §13.15.5 `AssignmentRestElement`: `... DestructuringAssignmentTarget`.
    /// Children: the target.
    AssignmentRestElement,
    /// §13.15.5 `AssignmentRestProperty`: `... DestructuringAssignmentTarget`.
    /// Children: the target.
    AssignmentRestProperty,
    /// §13.2.4 `Elision` for one hole, `,`: the span is that comma.
    Elision,

    // ----- Expressions (§13) -------------------------------------------------
    /// An optional symbol that is not there. The span is empty.
    Absent,
    /// §13.1 `IdentifierReference`. No children; the name is the source text.
    IdentifierReference,
    /// §13.1 `BindingIdentifier`.
    BindingIdentifier,
    /// §13.1 `LabelIdentifier`.
    LabelIdentifier,
    /// §12.7 `IdentifierName` in a `PropertyName`, a member access or an
    /// import/export name.
    IdentifierName,
    /// §12.7 `PrivateIdentifier`.
    PrivateIdentifier,
    /// §13.2.1 `this`.
    ThisExpression,
    /// §13.2.3 `NullLiteral`.
    NullLiteral,
    /// §13.2.3 `BooleanLiteral`.
    BooleanLiteral,
    /// §13.2.3 `NumericLiteral`.
    NumericLiteral,
    /// §13.2.3 `StringLiteral`.
    StringLiteral,
    /// §13.2.7 `RegularExpressionLiteral`.
    RegularExpressionLiteral,
    /// §13.2.8 `TemplateLiteral`: a `NoSubstitutionTemplate`, or a
    /// `TemplateHead`, the expressions and `TemplateMiddle`s, and a
    /// `TemplateTail`. Children: `TemplateElement`s and `Expression`s,
    /// alternating, starting and ending with a `TemplateElement`.
    TemplateLiteral,
    /// §13.2.8 one of `NoSubstitutionTemplate`, `TemplateHead`,
    /// `TemplateMiddle`, `TemplateTail`: the span includes its delimiters.
    TemplateElement,
    /// §13.2.4 `ArrayLiteral`. Children: `AssignmentExpression`s,
    /// `SpreadElement`s and [`NodeKind::Elision`]s.
    ArrayLiteral,
    /// §13.2.5 `ObjectLiteral`. Children: `PropertyDefinition`s,
    /// `CoverInitializedName`s and `MethodDefinition`s.
    ObjectLiteral,
    /// §13.2.5 `PropertyDefinition`. [`Op`] `Shorthand` (children: the
    /// `IdentifierReference`), `KeyValue` (children: the `PropertyName`, the
    /// `AssignmentExpression`) or `Spread` (children: the
    /// `AssignmentExpression`).
    PropertyDefinition,
    /// §13.2.5 `CoverInitializedName`: `IdentifierReference Initializer`.
    /// Children: the `IdentifierReference`, the initializer. Only an
    /// assignment pattern may contain it (§13.2.5.1's early error).
    CoverInitializedName,
    /// §13.2.5 `ComputedPropertyName`: `[ AssignmentExpression ]`. Children:
    /// the expression.
    ComputedPropertyName,
    /// §13.2.9 `CoverParenthesizedExpressionAndArrowParameterList` read as a
    /// `ParenthesizedExpression`. Children: the `Expression`.
    ParenthesizedExpression,
    /// §13.3.2 `MemberExpression . IdentifierName` and `[ Expression ]`, and
    /// `. PrivateIdentifier`. [`Op`] `Dot`, `Bracket` or `PrivateDot`.
    /// Children: the object, the property (an `IdentifierName`, an
    /// `Expression` or a `PrivateIdentifier`).
    MemberExpression,
    /// §13.3.7 `SuperProperty`. [`Op`] `Dot` or `Bracket`. Children: the
    /// property.
    SuperProperty,
    /// §13.3.7 `SuperCall`. Children: the `Arguments`.
    SuperCall,
    /// §13.3.10 `ImportCall`. Children: the specifier, the options or
    /// [`NodeKind::Absent`].
    ImportCall,
    /// §13.3.12 `ImportMeta`. No children.
    ImportMeta,
    /// §13.3.12 `NewTarget`. No children.
    NewTarget,
    /// §13.3.5 `NewExpression`: `new MemberExpression Arguments`, and `new
    /// NewExpression` (the arguments absent). Children: the callee, the
    /// `Arguments` or [`NodeKind::Absent`].
    NewExpression,
    /// §13.3.6 `CallExpression`. Children: the callee, the `Arguments`.
    CallExpression,
    /// §13.3.8 `Arguments`: its span runs from the `(` to the `)`. Children:
    /// `AssignmentExpression`s and `SpreadElement`s.
    Arguments,
    /// §13.3.11 `TaggedTemplate`: `MemberExpression TemplateLiteral[+Tagged]`.
    /// Children: the tag, the `TemplateLiteral`.
    TaggedTemplate,
    /// §13.3.9 `OptionalExpression`. Children: the base expression, then the
    /// `OptionalChain` links in order.
    OptionalExpression,
    /// §13.3.9 one link of an `OptionalChain`. [`Op`] `ChainDot`,
    /// `ChainBracket`, `ChainCall`, `ChainPrivateDot` or `ChainTemplate`;
    /// `flag` is true when the link starts with `?.`. Children: the
    /// `IdentifierName`, `Expression`, `Arguments`, `PrivateIdentifier` or
    /// `TemplateLiteral`.
    OptionalChain,
    /// §13.4 `UpdateExpression`. [`Op`] `PrefixIncrement`,
    /// `PrefixDecrement`, `PostfixIncrement` or `PostfixDecrement`. Children:
    /// the operand.
    UpdateExpression,
    /// §13.5 `UnaryExpression` (`delete void typeof + - ~ !`). [`Op`] names
    /// the operator. Children: the operand.
    UnaryExpression,
    /// §15.8 `AwaitExpression`. Children: the operand.
    AwaitExpression,
    /// §13.6 `ExponentiationExpression`: `UpdateExpression **
    /// ExponentiationExpression`. Children: left, right.
    ExponentiationExpression,
    /// §13.7 `MultiplicativeExpression`. [`Op`] `Mul`, `Div` or `Rem`.
    /// Children: left, right.
    MultiplicativeExpression,
    /// §13.8 `AdditiveExpression`. [`Op`] `Add` or `Sub`.
    AdditiveExpression,
    /// §13.9 `ShiftExpression`. [`Op`] `Shl`, `Shr` or `UShr`.
    ShiftExpression,
    /// §13.10 `RelationalExpression`. [`Op`] `Lt`, `Gt`, `Le`, `Ge`,
    /// `InstanceOf` or `In`; the left child may be a `PrivateIdentifier` for
    /// `#x in obj`.
    RelationalExpression,
    /// §13.11 `EqualityExpression`. [`Op`] `Eq`, `Ne`, `StrictEq` or
    /// `StrictNe`.
    EqualityExpression,
    /// §13.12 `BitwiseANDExpression`.
    BitwiseANDExpression,
    /// §13.12 `BitwiseXORExpression`.
    BitwiseXORExpression,
    /// §13.12 `BitwiseORExpression`.
    BitwiseORExpression,
    /// §13.13 `LogicalANDExpression`.
    LogicalANDExpression,
    /// §13.13 `LogicalORExpression`.
    LogicalORExpression,
    /// §13.13 `CoalesceExpression`.
    CoalesceExpression,
    /// §13.14 `ConditionalExpression`. Children: the test, the consequent,
    /// the alternate.
    ConditionalExpression,
    /// §13.15 `AssignmentExpression`. [`Op`] `Assign` or a compound
    /// assignment operator. Children: the target (a `LeftHandSideExpression`,
    /// or for `=` an assignment pattern), the value.
    AssignmentExpression,
    /// §15.5 `YieldExpression`. [`Op`] `YieldPlain` or `YieldDelegate`.
    /// Children: the operand or [`NodeKind::Absent`].
    YieldExpression,
    /// §13.16 `Expression`: `Expression , AssignmentExpression`. Children:
    /// two or more `AssignmentExpression`s.
    Expression,
    /// §13.2.4, §13.3.8 `SpreadElement`: `... AssignmentExpression`.
    /// Children: the expression.
    SpreadElement,

    // ----- Modules (§16.2) ---------------------------------------------------
    /// §16.2.2 `ImportDeclaration`. Children: the `ImportClause` or
    /// [`NodeKind::Absent`] (`import "m";`), the `ModuleSpecifier` (a
    /// `StringLiteral`), the `WithClause` or [`NodeKind::Absent`].
    ImportDeclaration,
    /// §16.2.2 `ImportClause`. Children: the `ImportedDefaultBinding` (a
    /// `BindingIdentifier`) or [`NodeKind::Absent`], then the
    /// `NameSpaceImport` or `NamedImports` or [`NodeKind::Absent`].
    ImportClause,
    /// §16.2.2 `NameSpaceImport`: `* as ImportedBinding`. Children: the
    /// `BindingIdentifier`.
    NameSpaceImport,
    /// §16.2.2 `NamedImports`. Children: the `ImportSpecifier`s.
    NamedImports,
    /// §16.2.2 `ImportSpecifier`. Children: the imported name (an
    /// `IdentifierName` or `StringLiteral`) or [`NodeKind::Absent`] when the
    /// binding is the name, the `BindingIdentifier`.
    ImportSpecifier,
    /// §16.2.2 `WithClause`: `with { WithEntries? }`. Children: the
    /// `ImportAttribute`s.
    WithClause,
    /// §16.2.2 `ImportAttribute`: `AttributeKey : StringLiteral`. Children:
    /// the key (an `IdentifierName` or `StringLiteral`), the `StringLiteral`.
    ImportAttribute,
    /// §16.2.3 `ExportDeclaration`. [`Op`] `ExportAll` (`export * from`;
    /// children: the specifier, the `WithClause` or [`NodeKind::Absent`]),
    /// `ExportAllAs` (`export * as n from`; children: the `ModuleExportName`,
    /// the specifier, the `WithClause`), `ExportFrom` (`export {..} from`;
    /// children: the `NamedExports`, the specifier, the `WithClause`),
    /// `ExportNamed` (`export {..};`; children: the `NamedExports`),
    /// `ExportVar`, `ExportDecl` (children: the `VariableStatement`,
    /// `Declaration`), `ExportDefaultHoistable` (`export default
    /// HoistableDeclaration`), `ExportDefaultClass`, `ExportDefaultExpression`
    /// (`export default AssignmentExpression ;`; children: the expression).
    ExportDeclaration,
    /// §16.2.3 `NamedExports`. Children: the `ExportSpecifier`s.
    NamedExports,
    /// §16.2.3 `ExportSpecifier`. Children: the local name (an
    /// `IdentifierName` or `StringLiteral`), the exported name or
    /// [`NodeKind::Absent`].
    ExportSpecifier,
}

/// The few facts a production's alternatives distinguish, shared by every
/// kind that has them. `None` for a kind that has no such fact.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Op {
    /// No operator or mode.
    None,
    // ----- UnaryExpression ----
    /// `delete`.
    Delete,
    /// `void`.
    Void,
    /// `typeof`.
    Typeof,
    /// Unary `+`.
    Plus,
    /// Unary `-`.
    Minus,
    /// `~`.
    BitNot,
    /// `!`.
    LogicalNot,
    // ----- UpdateExpression ----
    /// Prefix `++`.
    PrefixIncrement,
    /// Prefix `--`.
    PrefixDecrement,
    /// Postfix `++`.
    PostfixIncrement,
    /// Postfix `--`.
    PostfixDecrement,
    // ----- Binary operators ----
    /// `**`.
    Exp,
    /// `*`.
    Mul,
    /// `/`.
    Div,
    /// `%`.
    Rem,
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `<<`.
    Shl,
    /// `>>`.
    Shr,
    /// `>>>`.
    UShr,
    /// `<`.
    Lt,
    /// `>`.
    Gt,
    /// `<=`.
    Le,
    /// `>=`.
    Ge,
    /// `instanceof`.
    InstanceOf,
    /// `in`.
    In,
    /// `==`.
    Eq,
    /// `!=`.
    Ne,
    /// `===`.
    StrictEq,
    /// `!==`.
    StrictNe,
    /// `&`.
    BitAnd,
    /// `^`.
    BitXor,
    /// `|`.
    BitOr,
    /// `&&`.
    LogicalAnd,
    /// `||`.
    LogicalOr,
    /// `??`.
    Coalesce,
    // ----- AssignmentOperator ----
    /// `=`.
    Assign,
    /// `*=`.
    MulAssign,
    /// `/=`.
    DivAssign,
    /// `%=`.
    RemAssign,
    /// `+=`.
    AddAssign,
    /// `-=`.
    SubAssign,
    /// `<<=`.
    ShlAssign,
    /// `>>=`.
    ShrAssign,
    /// `>>>=`.
    UShrAssign,
    /// `&=`.
    BitAndAssign,
    /// `^=`.
    BitXorAssign,
    /// `|=`.
    BitOrAssign,
    /// `**=`.
    ExpAssign,
    /// `&&=`.
    LogicalAndAssign,
    /// `||=`.
    LogicalOrAssign,
    /// `??=`.
    CoalesceAssign,
    // ----- Member access ----
    /// `. IdentifierName`.
    Dot,
    /// `[ Expression ]`.
    Bracket,
    /// `. PrivateIdentifier`.
    PrivateDot,
    /// `?. IdentifierName` or `. IdentifierName` in a chain.
    ChainDot,
    /// `?. [ Expression ]` or `[ Expression ]` in a chain.
    ChainBracket,
    /// `?. Arguments` or `Arguments` in a chain.
    ChainCall,
    /// `?. PrivateIdentifier` or `. PrivateIdentifier` in a chain.
    ChainPrivateDot,
    /// `?. TemplateLiteral` or a `TemplateLiteral` in a chain: derived by the
    /// grammar, so that automatic semicolon insertion does not apply to it,
    /// and a Syntax Error always (§13.3.1.1).
    ChainTemplate,
    // ----- Declarations ----
    /// `var`.
    Var,
    /// `let`.
    Let,
    /// `const`.
    Const,
    // ----- MethodDefinition ----
    /// `PropertyName ( ... ) { ... }`.
    Method,
    /// `get PropertyName ( ) { ... }`.
    Getter,
    /// `set PropertyName ( PropertySetParameterList ) { ... }`.
    Setter,
    /// `* PropertyName ( ... ) { ... }`.
    GeneratorMethod,
    /// `async PropertyName ( ... ) { ... }`.
    AsyncMethod,
    /// `async * PropertyName ( ... ) { ... }`.
    AsyncGeneratorMethod,
    // ----- Properties and yield ----
    /// A shorthand property or binding.
    Shorthand,
    /// `PropertyName : value`.
    KeyValue,
    /// `... value`.
    Spread,
    /// `yield` with an optional operand.
    YieldPlain,
    /// `yield *` with an operand.
    YieldDelegate,
    // ----- ExportDeclaration ----
    /// `export * from "m";`.
    ExportAll,
    /// `export * as n from "m";`.
    ExportAllAs,
    /// `export { ... } from "m";`.
    ExportFrom,
    /// `export { ... };`.
    ExportNamed,
    /// `export VariableStatement`.
    ExportVar,
    /// `export Declaration`.
    ExportDecl,
    /// `export default HoistableDeclaration`.
    ExportDefaultHoistable,
    /// `export default ClassDeclaration`.
    ExportDefaultClass,
    /// `export default AssignmentExpression ;`.
    ExportDefaultExpression,
}

/// One node of the arena.
pub struct Node {
    /// The production.
    pub kind: NodeKind,
    /// The alternative of the production, where it has more than one fact.
    pub op: Op,
    /// A flag some kinds have: `static`, `await` of `for await`, `?.` of an
    /// optional chain link. False elsewhere.
    pub flag: bool,
    /// The first code point of the node's first token.
    pub start: usize,
    /// One past the last code point of the node's last token.
    pub end: usize,
    /// The children, in source order, each with a smaller index than this
    /// node's.
    pub children: Vec<NodeId>,
}

/// An arena AST: nodes, and the root's index.
pub struct Ast {
    /// The nodes. The root is `nodes[root]`, and is the last node.
    pub nodes: Vec<Node>,
    /// The root, a [`NodeKind::Script`] or [`NodeKind::Module`].
    pub root: NodeId,
}

/// The specification's view of a [`Node`]: the same facts as mathematical
/// values.
pub struct NodeV {
    /// See [`Node::kind`].
    pub kind: NodeKind,
    /// See [`Node::op`].
    pub op: Op,
    /// See [`Node::flag`].
    pub flag: bool,
    /// See [`Node::start`].
    pub start: int,
    /// See [`Node::end`].
    pub end: int,
    /// See [`Node::children`].
    pub children: Seq<int>,
}

/// The specification's view of an [`Ast`].
pub struct AstV {
    /// See [`Ast::nodes`].
    pub nodes: Seq<NodeV>,
    /// See [`Ast::root`].
    pub root: int,
}

impl View for Node {
    type V = NodeV;

    open spec fn view(&self) -> NodeV {
        NodeV {
            kind: self.kind,
            op: self.op,
            flag: self.flag,
            start: self.start as int,
            end: self.end as int,
            children: self.children@.map_values(|c: u32| c as int),
        }
    }
}

impl View for Ast {
    type V = AstV;

    open spec fn view(&self) -> AstV {
        AstV { nodes: self.nodes@.map_values(|n: Node| n@), root: self.root as int }
    }
}

} // verus!
