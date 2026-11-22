//! The parser's `import` and `export` declarations (ECMA-262 §16.2).

use crate::ast::{NodeKind as K, Op};
use crate::parser::{Cx, Parser, R, syn};
use clazel_js_lexer::spec::ElementKind;

impl<'a> Parser<'a> {
    /// A `ModuleItem`: an import or export declaration, or a `StatementListItem`.
    pub fn parse_module_item(&mut self, cx: Cx) -> R<u32> {
        if self.t.is_w("import") {
            let nx = self.peek()?;
            if !(nx.is_p("(") || nx.is_p(".")) {
                return self.parse_import(cx);
            }
        }
        if self.t.is_w("export") {
            return self.parse_export(cx);
        }
        self.parse_item(cx)
    }

    /// An `IdentifierName` or a `StringLiteral`: a `ModuleExportName`.
    fn parse_module_export_name(&mut self) -> R<u32> {
        let (s, e) = (self.t.start, self.t.end);
        if self.t.is_name() {
            self.bump()?;
            Ok(self.leaf(K::IdentifierName, s, e))
        } else if self.t.kind == ElementKind::StringLiteral && !self.t.eof {
            self.bump()?;
            Ok(self.leaf(K::StringLiteral, s, e))
        } else {
            syn()
        }
    }

    /// A `StringLiteral` (the `ModuleSpecifier`).
    fn parse_module_specifier(&mut self) -> R<u32> {
        if self.t.kind != ElementKind::StringLiteral || self.t.eof {
            return syn();
        }
        let (s, e) = (self.t.start, self.t.end);
        self.bump()?;
        Ok(self.leaf(K::StringLiteral, s, e))
    }

    /// `WithClause?`: `with { ... }`, or an absent one.
    fn parse_with_clause(&mut self) -> R<u32> {
        if !self.t.is_w("with") {
            return Ok(self.absent());
        }
        let start = self.t.start;
        self.bump()?;
        self.expect_p("{")?;
        let mut kids = Vec::new();
        while !self.t.is_p("}") {
            if self.t.eof {
                return syn();
            }
            let ks = self.t.start;
            let key = self.parse_module_export_name()?;
            self.expect_p(":")?;
            let v = self.parse_module_specifier()?;
            let e = self.en(v);
            kids.push(self.mk(K::ImportAttribute, Op::None, false, ks, e, vec![key, v]));
            if !self.eat_p(",")? && !self.t.is_p("}") {
                return syn();
            }
        }
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::WithClause, Op::None, false, start, end, kids))
    }

    /// `ImportDeclaration` (§16.2.2).
    fn parse_import(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        if self.t.kind == ElementKind::StringLiteral && !self.t.eof {
            let clause = self.absent();
            let spec = self.parse_module_specifier()?;
            let with = self.parse_with_clause()?;
            let end = self.semi()?;
            return Ok(self.mk(
                K::ImportDeclaration,
                Op::None,
                false,
                start,
                end,
                vec![clause, spec, with],
            ));
        }
        // The absent default binding is at the start of the clause, inside it
        // (`spec::span_ok` allows any point of the white space before the clause).
        let cs = self.t.start;
        let mut default = None;
        let mut named = None;
        if self.t.is_name() {
            default = Some(self.parse_ident(K::BindingIdentifier, cx)?);
            if self.eat_p(",")? {
                named = Some(self.parse_import_named_or_ns(cx)?);
            }
        } else {
            named = Some(self.parse_import_named_or_ns(cx)?);
        }
        let ce = self.prev_end;
        let d = match default {
            Some(d) => d,
            None => self.leaf(K::Absent, cs, cs),
        };
        let n = match named {
            Some(n) => n,
            None => self.leaf(K::Absent, ce, ce),
        };
        let clause = self.mk(K::ImportClause, Op::None, false, cs, ce, vec![d, n]);
        if !self.t.is_w("from") {
            return syn();
        }
        self.bump()?;
        let spec = self.parse_module_specifier()?;
        let with = self.parse_with_clause()?;
        let end = self.semi()?;
        Ok(self.mk(
            K::ImportDeclaration,
            Op::None,
            false,
            start,
            end,
            vec![clause, spec, with],
        ))
    }

    /// `NameSpaceImport` or `NamedImports`.
    fn parse_import_named_or_ns(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        if self.t.is_p("*") {
            self.bump()?;
            if !self.t.is_w("as") {
                return syn();
            }
            self.bump()?;
            let b = self.parse_ident(K::BindingIdentifier, cx)?;
            let end = self.en(b);
            return Ok(self.mk(K::NameSpaceImport, Op::None, false, start, end, vec![b]));
        }
        self.expect_p("{")?;
        let mut kids = Vec::new();
        while !self.t.is_p("}") {
            if self.t.eof {
                return syn();
            }
            let ss = self.t.start;
            let is_str = self.t.kind == ElementKind::StringLiteral;
            let name_tok = self.t.clone();
            let first = self.parse_module_export_name()?;
            if self.t.is_w("as") {
                self.bump()?;
                let b = self.parse_ident(K::BindingIdentifier, cx)?;
                let end = self.en(b);
                kids.push(self.mk(K::ImportSpecifier, Op::None, false, ss, end, vec![first, b]));
            } else {
                if is_str || !Self::name_ok(&name_tok.name, cx) {
                    return syn();
                }
                let (s, e) = (self.st(first), self.en(first));
                let b = self.leaf(K::BindingIdentifier, s, e);
                // At the start of the specifier, inside it (see `parse_import`).
                let a = self.leaf(K::Absent, s, s);
                kids.push(self.mk(K::ImportSpecifier, Op::None, false, ss, e, vec![a, b]));
            }
            if !self.eat_p(",")? && !self.t.is_p("}") {
                return syn();
            }
        }
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::NamedImports, Op::None, false, start, end, kids))
    }

    /// `NamedExports`: `{ ExportSpecifier, ... }`.
    fn parse_named_exports(&mut self) -> R<u32> {
        let start = self.t.start;
        self.expect_p("{")?;
        let mut kids = Vec::new();
        while !self.t.is_p("}") {
            if self.t.eof {
                return syn();
            }
            let ss = self.t.start;
            let local = self.parse_module_export_name()?;
            let (exported, end) = if self.t.is_w("as") {
                self.bump()?;
                let x = self.parse_module_export_name()?;
                (x, self.en(x))
            } else {
                let e = self.en(local);
                (self.leaf(K::Absent, e, e), e)
            };
            kids.push(self.mk(
                K::ExportSpecifier,
                Op::None,
                false,
                ss,
                end,
                vec![local, exported],
            ));
            if !self.eat_p(",")? && !self.t.is_p("}") {
                return syn();
            }
        }
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::NamedExports, Op::None, false, start, end, kids))
    }

    /// `ExportDeclaration` (§16.2.3).
    fn parse_export(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let mk = |p: &mut Self, op: Op, end: usize, kids: Vec<u32>| {
            p.mk(K::ExportDeclaration, op, false, start, end, kids)
        };
        if self.t.is_p("*") {
            self.bump()?;
            if self.t.is_w("as") {
                self.bump()?;
                let name = self.parse_module_export_name()?;
                if !self.t.is_w("from") {
                    return syn();
                }
                self.bump()?;
                let spec = self.parse_module_specifier()?;
                let with = self.parse_with_clause()?;
                let end = self.semi()?;
                return Ok(mk(self, Op::ExportAllAs, end, vec![name, spec, with]));
            }
            if !self.t.is_w("from") {
                return syn();
            }
            self.bump()?;
            let spec = self.parse_module_specifier()?;
            let with = self.parse_with_clause()?;
            let end = self.semi()?;
            return Ok(mk(self, Op::ExportAll, end, vec![spec, with]));
        }
        if self.t.is_p("{") {
            let ne = self.parse_named_exports()?;
            if self.t.is_w("from") {
                self.bump()?;
                let spec = self.parse_module_specifier()?;
                let with = self.parse_with_clause()?;
                let end = self.semi()?;
                return Ok(mk(self, Op::ExportFrom, end, vec![ne, spec, with]));
            }
            let end = self.semi()?;
            return Ok(mk(self, Op::ExportNamed, end, vec![ne]));
        }
        if self.t.is_w("var") {
            let v = self.parse_statement(cx)?;
            let end = self.en(v);
            return Ok(mk(self, Op::ExportVar, end, vec![v]));
        }
        if self.t.is_w("default") {
            self.bump()?;
            if self.t.is_w("function") {
                let d = self.parse_function(cx, None, false, true)?;
                let end = self.en(d);
                return Ok(mk(self, Op::ExportDefaultHoistable, end, vec![d]));
            }
            if self.t.is_w("async") {
                let nx = self.peek()?;
                if nx.is_w("function") && !nx.nl {
                    let s = self.t.start;
                    let d = self.parse_function(cx, Some(s), false, true)?;
                    let end = self.en(d);
                    return Ok(mk(self, Op::ExportDefaultHoistable, end, vec![d]));
                }
            }
            if self.t.is_w("class") {
                let d = self.parse_class(cx, false, true)?;
                let end = self.en(d);
                return Ok(mk(self, Op::ExportDefaultClass, end, vec![d]));
            }
            let e = self.parse_assign(cx.with_in(true))?;
            let end = self.semi()?;
            return Ok(mk(self, Op::ExportDefaultExpression, end, vec![e]));
        }
        // `export Declaration`.
        let is_decl = self.t.is_w("function")
            || self.t.is_w("class")
            || self.t.is_w("const")
            || (self.t.is_w("let") && self.let_starts_declaration()?)
            || (self.t.is_w("async") && {
                let nx = self.peek()?;
                nx.is_w("function") && !nx.nl
            });
        if !is_decl {
            return syn();
        }
        let d = self.parse_item(cx)?;
        let end = self.en(d);
        Ok(mk(self, Op::ExportDecl, end, vec![d]))
    }
}
