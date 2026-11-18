//! The shape of the AST for small programs, written out and checked by hand
//! against the productions of `spec.rs` (`d_stmt`, `d_expr`, ...): the layout of
//! each node's children, the operator, and the spans (the first token's start to
//! the last token's end; the empty span at the end of the token before, for an
//! absent symbol; a `;` that is inserted is in no span).

use clazel_js_syntax::ast::{Ast, NodeKind, Op};
use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;

fn kind_name(k: NodeKind) -> &'static str {
    match k {
        NodeKind::Script => "Script",
        NodeKind::Module => "Module",
        NodeKind::BlockStatement => "Block",
        NodeKind::VariableStatement => "Var",
        NodeKind::VariableDeclarationList => "VarList",
        NodeKind::VariableDeclaration => "VarDecl",
        NodeKind::LexicalDeclaration => "Lex",
        NodeKind::LexicalBinding => "LexBinding",
        NodeKind::EmptyStatement => "Empty",
        NodeKind::ExpressionStatement => "ExprStmt",
        NodeKind::IfStatement => "If",
        NodeKind::DoWhileStatement => "DoWhile",
        NodeKind::WhileStatement => "While",
        NodeKind::ForStatement => "For",
        NodeKind::ForInStatement => "ForIn",
        NodeKind::ForOfStatement => "ForOf",
        NodeKind::ForDeclaration => "ForDecl",
        NodeKind::BreakStatement => "Break",
        NodeKind::ReturnStatement => "Return",
        NodeKind::FunctionDeclaration => "FnDecl",
        NodeKind::FunctionExpression => "FnExpr",
        NodeKind::FormalParameters => "Params",
        NodeKind::FunctionBody => "Body",
        NodeKind::ArrowFunction => "Arrow",
        NodeKind::MethodDefinition => "Method",
        NodeKind::ClassDeclaration => "ClassDecl",
        NodeKind::ClassBody => "ClassBody",
        NodeKind::FieldDefinition => "Field",
        NodeKind::BindingElement => "BindingElem",
        NodeKind::ArrayBindingPattern => "ArrBinding",
        NodeKind::ObjectBindingPattern => "ObjBinding",
        NodeKind::BindingProperty => "BindingProp",
        NodeKind::ArrayAssignmentPattern => "ArrAssignPat",
        NodeKind::ObjectAssignmentPattern => "ObjAssignPat",
        NodeKind::AssignmentProperty => "AssignProp",
        NodeKind::AssignmentElement => "AssignElem",
        NodeKind::Elision => "Elision",
        NodeKind::Absent => "Absent",
        NodeKind::IdentifierReference => "Ref",
        NodeKind::BindingIdentifier => "Bind",
        NodeKind::IdentifierName => "Name",
        NodeKind::NumericLiteral => "Num",
        NodeKind::StringLiteral => "Str",
        NodeKind::TemplateLiteral => "Template",
        NodeKind::TemplateElement => "TplElem",
        NodeKind::ArrayLiteral => "Array",
        NodeKind::ObjectLiteral => "Object",
        NodeKind::PropertyDefinition => "Prop",
        NodeKind::ParenthesizedExpression => "Paren",
        NodeKind::MemberExpression => "Member",
        NodeKind::NewExpression => "New",
        NodeKind::CallExpression => "Call",
        NodeKind::Arguments => "Args",
        NodeKind::OptionalExpression => "Optional",
        NodeKind::OptionalChain => "Chain",
        NodeKind::UpdateExpression => "Update",
        NodeKind::UnaryExpression => "Unary",
        NodeKind::AdditiveExpression => "Add",
        NodeKind::MultiplicativeExpression => "Mul",
        NodeKind::LogicalORExpression => "Or",
        NodeKind::CoalesceExpression => "Coalesce",
        NodeKind::ConditionalExpression => "Cond",
        NodeKind::AssignmentExpression => "Assign",
        NodeKind::YieldExpression => "Yield",
        NodeKind::Expression => "Seq",
        NodeKind::SpreadElement => "Spread",
        NodeKind::ImportDeclaration => "Import",
        NodeKind::ImportClause => "ImportClause",
        NodeKind::ExportDeclaration => "Export",
        _ => "?",
    }
}

fn op_name(o: Op) -> &'static str {
    match o {
        Op::None => "",
        Op::Add => ":+",
        Op::Mul => ":*",
        Op::Assign => ":=",
        Op::Dot => ":.",
        Op::Bracket => ":[]",
        Op::PostfixIncrement => ":x++",
        Op::Let => ":let",
        Op::Const => ":const",
        Op::Var => ":var",
        Op::Shorthand => ":short",
        Op::KeyValue => ":kv",
        Op::ChainDot => ":?.",
        Op::Getter => ":get",
        Op::Method => ":method",
        Op::ExportDefaultExpression => ":default-expr",
        Op::Typeof => ":typeof",
        Op::LogicalOr => ":||",
        Op::Coalesce => ":??",
        Op::YieldPlain => ":yield",
        _ => ":?",
    }
}

fn dump_node(ast: &Ast, id: u32, out: &mut String) {
    let Some(n) = ast.nodes.get(id as usize) else { return };
    out.push_str(kind_name(n.kind));
    out.push_str(op_name(n.op));
    if n.flag {
        out.push('!');
    }
    out.push_str(&format!("({}..{})", n.start, n.end));
    if !n.children.is_empty() {
        out.push('[');
        for (i, c) in n.children.iter().enumerate() {
            if i > 0 {
                out.push(' ');
            }
            dump_node(ast, *c, out);
        }
        out.push(']');
    }
}

fn dump(src: &str, goal: SourceGoal) -> String {
    let cps: Vec<u32> = src.chars().map(u32::from).collect();
    match parse(&cps, goal) {
        Ok(ast) => {
            let mut s = String::new();
            dump_node(&ast, ast.root, &mut s);
            s
        }
        Err(_) => "ERROR".to_string(),
    }
}

fn script(src: &str) -> String {
    dump(src, SourceGoal::Script)
}

#[test]
fn statements() {
    // 14.5: the `;` is in the statement's span; an inserted one is not.
    assert_eq!(script("a;"), "Script(0..2)[ExprStmt(0..2)[Ref(0..1)]]");
    assert_eq!(script("a\nb"), "Script(0..3)[ExprStmt(0..1)[Ref(0..1)] ExprStmt(2..3)[Ref(2..3)]]");
    // 14.3.2, 14.3.1: declarations; the absent initializer is at the end of the target.
    assert_eq!(
        script("var a = 1, b;"),
        "Script(0..13)[Var(0..13)[VarDecl(4..9)[Bind(4..5) Num(8..9)] VarDecl(11..12)[Bind(11..12) Absent(12..12)]]]"
    );
    assert_eq!(
        script("let x = 1;"),
        "Script(0..10)[Lex:let(0..10)[LexBinding(4..9)[Bind(4..5) Num(8..9)]]]"
    );
    // 14.6: the absent `else` is at the end of the consequent.
    assert_eq!(
        script("if (a) b;"),
        "Script(0..9)[If(0..9)[Ref(4..5) ExprStmt(7..9)[Ref(7..8)] Absent(9..9)]]"
    );
    // 14.7.4: `for (;;)` has three absent symbols.
    assert_eq!(
        script("for (;;) ;"),
        "Script(0..10)[For(0..10)[Absent(5..5) Absent(6..6) Absent(7..7) Empty(9..10)]]"
    );
    // 14.9: `break;`.
    assert_ne!(script("a: for (;;) break a;"), "ERROR");
    assert_eq!(
        script("for (var a of b) ;"),
        "Script(0..18)[ForOf(0..18)[ForDecl:var(5..10)[Bind(9..10)] Ref(14..15) Empty(17..18)]]"
    );
    assert_eq!(
        script("for (let [a] in b) ;"),
        "Script(0..20)[ForIn(0..20)[ForDecl:let(5..12)[ArrBinding(9..12)[BindingElem(10..11)[Bind(10..11) Absent(11..11)]]] Ref(16..17) Empty(19..20)]]"
    );
}

#[test]
fn expressions() {
    // Left associative binary operators; `*` binds tighter than `+`.
    assert_eq!(
        script("a + b * c + d"),
        "Script(0..13)[ExprStmt(0..13)[Add:+(0..13)[Add:+(0..9)[Ref(0..1) Mul:*(4..9)[Ref(4..5) Ref(8..9)]] Ref(12..13)]]]"
    );
    // 13.3: member, call, new.
    assert_eq!(
        script("a.b[c](d)"),
        "Script(0..9)[ExprStmt(0..9)[Call(0..9)[Member:[](0..6)[Member:.(0..3)[Ref(0..1) Name(2..3)] Ref(4..5)] Args(6..9)[Ref(7..8)]]]]"
    );
    assert_eq!(
        script("new a"),
        "Script(0..5)[ExprStmt(0..5)[New(0..5)[Ref(4..5) Absent(5..5)]]]"
    );
    assert_eq!(
        script("new a(b).c"),
        "Script(0..10)[ExprStmt(0..10)[Member:.(0..10)[New(0..8)[Ref(4..5) Args(5..8)[Ref(6..7)]] Name(9..10)]]]"
    );
    // 13.3.9: an optional chain is one node with its links.
    assert_eq!(
        script("a?.b.c"),
        "Script(0..6)[ExprStmt(0..6)[Optional(0..6)[Ref(0..1) Chain:?.!(1..4)[Name(3..4)] Chain:?.(4..6)[Name(5..6)]]]]"
    );
    // 13.14, 13.15, 13.16.
    assert_eq!(
        script("a ? b : c"),
        "Script(0..9)[ExprStmt(0..9)[Cond(0..9)[Ref(0..1) Ref(4..5) Ref(8..9)]]]"
    );
    assert_eq!(
        script("a = b, c"),
        "Script(0..8)[ExprStmt(0..8)[Seq(0..8)[Assign:=(0..5)[Ref(0..1) Ref(4..5)] Ref(7..8)]]]"
    );
    assert_eq!(script("a ?? b"), "Script(0..6)[ExprStmt(0..6)[Coalesce:??(0..6)[Ref(0..1) Ref(5..6)]]]");
    assert_eq!(script("a++"), "Script(0..3)[ExprStmt(0..3)[Update:x++(0..3)[Ref(0..1)]]]");
    assert_eq!(script("typeof a"), "Script(0..8)[ExprStmt(0..8)[Unary:typeof(0..8)[Ref(7..8)]]]");
    // 13.2.9: parentheses are a node of their own.
    assert_eq!(script("(a)"), "Script(0..3)[ExprStmt(0..3)[Paren(0..3)[Ref(1..2)]]]");
    assert_eq!(script("(a, b)"), "Script(0..6)[ExprStmt(0..6)[Paren(0..6)[Seq(1..5)[Ref(1..2) Ref(4..5)]]]]");
    // 13.2.8: template elements and substitutions alternate.
    assert_eq!(
        script("`a${b}c`"),
        "Script(0..8)[ExprStmt(0..8)[Template(0..8)[TplElem(0..4) Ref(4..5) TplElem(5..8)]]]"
    );
}

#[test]
fn literals_and_patterns() {
    // 13.2.4: a hole is an `Elision` of one comma; a trailing comma is none.
    assert_eq!(
        script("[a,,b,]"),
        "Script(0..7)[ExprStmt(0..7)[Array(0..7)[Ref(1..2) Elision(3..4) Ref(4..5)]]]"
    );
    assert_eq!(
        script("({a, b: c, d() {}})"),
        "Script(0..19)[ExprStmt(0..19)[Paren(0..19)[Object(1..18)[Prop:short(2..3)[Ref(2..3)] Prop:kv(5..9)[Name(5..6) Ref(8..9)] Method:method(11..17)[Name(11..12) Params(12..14) Body(15..17)]]]]]"
    );
    // 13.15.5: the left side of `=` is read as an assignment pattern.
    assert_eq!(
        script("[a, b = 1] = c"),
        "Script(0..14)[ExprStmt(0..14)[Assign:=(0..14)[ArrAssignPat(0..10)[AssignElem(1..2)[Ref(1..2) Absent(2..2)] AssignElem(4..9)[Ref(4..5) Num(8..9)]] Ref(13..14)]]]"
    );
    assert_eq!(
        script("({a = 1} = b)"),
        "Script(0..13)[ExprStmt(0..13)[Paren(0..13)[Assign:=(1..12)[ObjAssignPat(1..8)[AssignProp:short(2..7)[Ref(2..3) Num(6..7)]] Ref(11..12)]]]]"
    );
    // 14.3.3: binding patterns.
    assert_eq!(
        script("var {a, b: [c]} = d;"),
        "Script(0..20)[Var(0..20)[VarDecl(4..19)[ObjBinding(4..15)[BindingProp:short(5..6)[BindingElem(5..6)[Bind(5..6) Absent(6..6)]] BindingProp:kv(8..14)[Name(8..9) BindingElem(11..14)[ArrBinding(11..14)[BindingElem(12..13)[Bind(12..13) Absent(13..13)]] Absent(14..14)]]] Ref(18..19)]]]"
    );
}

#[test]
fn functions_and_classes() {
    // 15.2: the name, `FormalParameters` from `(` to `)`, the body from `{` to `}`.
    assert_eq!(
        script("function f(a, b = 1) { }"),
        "Script(0..24)[FnDecl(0..24)[Bind(9..10) Params(10..20)[BindingElem(11..12)[Bind(11..12) Absent(12..12)] BindingElem(14..19)[Bind(14..15) Num(18..19)]] Body(21..24)]]"
    );
    // 15.3: an arrow function's parameters are read from the parenthesized cover.
    assert_eq!(
        script("(a) => a"),
        "Script(0..8)[ExprStmt(0..8)[Arrow(0..8)[Params(0..3)[BindingElem(1..2)[Bind(1..2) Absent(2..2)]] Ref(7..8)]]]"
    );
    assert_eq!(
        script("a => a"),
        "Script(0..6)[ExprStmt(0..6)[Arrow(0..6)[Bind(0..1) Ref(5..6)]]]"
    );
    // 15.7: a class element's span includes `static`; a field's includes its `;`.
    assert_eq!(
        script("class A { static x = 1; get y() { } }"),
        "Script(0..37)[ClassDecl(0..37)[Bind(6..7) Absent(7..7) ClassBody(8..37)[Field!(10..23)[Name(17..18) Num(21..22)] Method:get(24..35)[Name(28..29) Params(29..31) Body(32..35)]]]]"
    );
}

#[test]
fn modules() {
    assert_eq!(
        dump("export default a;", SourceGoal::Module),
        "Module(0..17)[Export:default-expr(0..17)[Ref(15..16)]]"
    );
    assert_eq!(
        dump("import a from 'm';", SourceGoal::Module),
        "Module(0..18)[Import(0..18)[ImportClause(7..8)[Bind(7..8) Absent(8..8)] Str(14..17) Absent(17..17)]]"
    );
}
