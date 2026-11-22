//! Export declarations (§16.2.3): what a module's body evaluates for each.
//!
//! Everything about modules that is static (the requests, the import and export
//! entries, the bindings of the module environment) is in the record
//! ([`crate::module`]); the body only runs the initializers. An `import`, an
//! `export { .. }`, an `export * from` and an `export default` of a function
//! declaration evaluate to nothing: the runtime linked them (§16.2.1.6.4†
//! InitializeEnvironment). The rest are the declaration they wrap, and
//! `export default` of an expression or an anonymous class, which initializes
//! the binding `*default*` (§16.2.3.7† ExportDeclaration : `export default`
//! AssignmentExpression `;`).

use super::*;

impl<'a> Cg<'a> {
    /// Evaluates the `ExportDeclaration` node `nd`.
    pub(super) fn export_declaration(&mut self, nd: &Node) -> R<()> {
        match nd.op {
            AOp::ExportAll
            | AOp::ExportAllAs
            | AOp::ExportFrom
            | AOp::ExportNamed
            | AOp::ExportDefaultHoistable => Ok(()),
            // `export var`, and `export` of a lexical declaration, a function
            // or a class: the declaration's own evaluation.
            AOp::ExportVar | AOp::ExportDecl => {
                let d = self.child(nd, 0)?;
                self.stmt(d, &[])
            }
            AOp::ExportDefaultClass => {
                let c = self.child(nd, 0)?;
                let cn = self.node(c)?;
                let name_node = self.child(cn, 0)?;
                if self.node(name_node)?.kind == NodeKind::BindingIdentifier {
                    return self.class_declaration(c);
                }
                // §16.2.3.7† ExportDeclaration : `export default` ClassDeclaration:
                // the class is named "default" (BindingClassDeclarationEvaluation
                // step 2), and `*default*` is initialized with it.
                let m = self.mark();
                let t = self.alloc()?;
                self.name_override = Some("default".encode_utf16().collect());
                self.class_definition(c, t)?;
                self.init_default(t, self.sp(c))?;
                self.release(m);
                Ok(())
            }
            AOp::ExportDefaultExpression => {
                let e = self.child(nd, 0)?;
                let m = self.mark();
                // "If IsAnonymousFunctionDefinition(AssignmentExpression) is true,
                // then Let value be ? NamedEvaluation of AssignmentExpression with
                // argument "default"."
                self.named(e, &"default".encode_utf16().collect::<Vec<u16>>())?;
                let v = self.expr_any(e)?;
                self.init_default(v, self.sp(e))?;
                self.release(m);
                Ok(())
            }
            _ => Err(CompileError::Internal("unknown export declaration")),
        }
    }

    /// "Perform ? env.InitializeBinding("*default*", value)".
    fn init_default(&mut self, src: Reg, sp: Span) -> R<()> {
        let b = self.an.default_binding;
        if b == NONE {
            return Err(CompileError::Internal("no *default* binding"));
        }
        self.init_binding(b, src, sp)
    }
}
