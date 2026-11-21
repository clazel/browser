//! The static record of a compiled module (phase-7.md item 7.7, fourth slice):
//! what ParseModule (§16.2.1.6.1†) produces from the source text, and what the
//! runtime (7.8) needs to link and evaluate it.
//!
//! # The shape
//!
//! [`ModuleProgram`] is the Source Text Module Record's static fields
//! (§16.2.1.6†) as data, with the compiled code:
//!
//! | Spec field | Here |
//! |---|---|
//! | `[[ECMAScriptCode]]`, `[[Context]]` | [`ModuleProgram::program`]: function 0 is the module body, run with the module environment as its callee environment and `this` undefined |
//! | `[[RequestedModules]]` | [`ModuleProgram::requested_modules`] |
//! | `[[ImportEntries]]` | [`ModuleProgram::import_entries`] |
//! | `[[LocalExportEntries]]` | [`ModuleProgram::local_export_entries`] |
//! | `[[IndirectExportEntries]]` | [`ModuleProgram::indirect_export_entries`] |
//! | `[[StarExportEntries]]` | [`ModuleProgram::star_export_entries`] |
//! | `[[HasTLA]]` | [`ModuleProgram::has_tla`] |
//! | (the module Environment Record's shape) | [`ModuleProgram::bindings`] and [`ModuleProgram::env_size`] |
//!
//! The Cyclic Module Record's dynamic fields (`[[Status]]`, `[[DFSIndex]]`,
//! `[[EvaluationError]]`, the async bookkeeping) and `[[ImportMeta]]` belong to
//! the runtime: this crate does not link or evaluate (7.8 does). The names
//! follow `clazel-js`'s `Module`, `ModuleRequest`, `ImportAttribute`
//! (the embedding API's contract): a request is the specifier and its
//! attributes in source order; a request that two declarations share is one
//! entry (§16.2.1.3† ModuleRequests: same specifier and the same set of
//! attributes), at the position of the first.
//!
//! # Strings
//!
//! Names and specifiers are UTF-16 code units, as the spec's Strings are. The
//! embedding API's `ModuleRequest` holds a Rust `String`: a specifier with a
//! lone surrogate cannot be written there, and [`ModuleRequest::specifier_lossy`]
//! is what the host sees in that one case.
//!
//! # The module environment
//!
//! The runtime creates the module Environment Record when it links the module
//! (InitializeEnvironment §16.2.1.6.4†) as an environment object of
//! [`ModuleProgram::env_size`] slots, and runs the body with it as the callee
//! environment of function 0 ([`crate::bytecode::Instr::GetCalleeEnv`]), so
//! the body and every closure in it reach a binding by its slot
//! ([`crate::bytecode::Instr::GetEnvSlot`]) and other modules reach an export
//! by the slot of its local name. Every binding of the module scope has a slot,
//! so that other modules can name it. Each entry of
//! [`ModuleProgram::bindings`] says what the runtime puts in the slot at
//! InitializeEnvironment time ([`ModuleBindingInit`]); slots that are in no
//! entry belong to the compiler (the module's `this` for its arrow functions)
//! and are written by the first ops of the body.
//!
//! # Where the standard is followed
//!
//! ParseModule steps 7 to 10 (§16.2.1.6.1†: requestedModules, importEntries,
//! the export entry partition), ImportEntries, ExportEntries and
//! ModuleRequests (§16.2.2.2†, §16.2.3.2†, §16.2.1.3†), and HasTLA / ContainsAwait.
//! Section numbers marked † are from memory (phase-7.md's convention).

use crate::bytecode::Program;
use crate::compile::CompileError;
use crate::literal;
use crate::scope::bound_idents;
use clazel_js_syntax::ast::{Ast, Node, NodeKind, Op as AOp};

/// An import attribute (`with { type: "json" }` is `("type", "json")`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ImportAttribute {
    /// The attribute's key.
    pub key: Vec<u16>,
    /// Its value.
    pub value: Vec<u16>,
}

/// ModuleRequest Record (§16.2.1.3†).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModuleRequest {
    /// The module specifier, as written.
    pub specifier: Vec<u16>,
    /// The attributes, in source order.
    pub attributes: Vec<ImportAttribute>,
}

impl ModuleRequest {
    /// The specifier as a Rust string, a lone surrogate becoming U+FFFD.
    pub fn specifier_lossy(&self) -> String {
        String::from_utf16_lossy(&self.specifier)
    }

    /// ModuleRequestsEqual (§16.2.1.3†): the same specifier and the same set of
    /// attributes, whatever their order.
    pub fn same_as(&self, other: &ModuleRequest) -> bool {
        self.specifier == other.specifier
            && self.attributes.len() == other.attributes.len()
            && self
                .attributes
                .iter()
                .all(|a| other.attributes.iter().any(|b| a == b))
    }
}

/// An ImportEntry's `[[ImportName]]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportName {
    /// A name the imported module exports (`default` for a default import).
    Name(Vec<u16>),
    /// `namespace-object`: the whole module (`import * as ns`).
    Namespace,
}

/// ImportEntry Record (§16.2.1.6†).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportEntry {
    /// `[[ModuleRequest]]`: an index into [`ModuleProgram::requested_modules`].
    pub module_request: u32,
    /// `[[ImportName]]`.
    pub import_name: ImportName,
    /// `[[LocalName]]`.
    pub local_name: Vec<u16>,
}

/// An ExportEntry's `[[ImportName]]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExportImportName {
    /// A name of the requested module.
    Name(Vec<u16>),
    /// `all`: the namespace object (`export * as n from`).
    All,
    /// `all-but-default`: every export but `default` (`export * from`).
    AllButDefault,
}

/// ExportEntry Record (§16.2.1.6†). Which of the fields are present depends on
/// the list the entry is in (local: `local_name`; indirect: `module_request` and
/// `import_name`; star: `module_request` and `import_name`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportEntry {
    /// `[[ExportName]]`: null for `export * from`.
    pub export_name: Option<Vec<u16>>,
    /// `[[ModuleRequest]]`: an index into [`ModuleProgram::requested_modules`],
    /// or null for a local export.
    pub module_request: Option<u32>,
    /// `[[ImportName]]`.
    pub import_name: Option<ExportImportName>,
    /// `[[LocalName]]`: a name in [`ModuleProgram::bindings`].
    pub local_name: Option<Vec<u16>>,
}

/// What the runtime puts in a slot of the module environment when it links the
/// module (InitializeEnvironment §16.2.1.6.4†).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModuleBindingInit {
    /// A `var` (step 24: "Perform ! env.InitializeBinding(dn, undefined)"): the
    /// value undefined.
    Undefined,
    /// A `let`, `const` or `class` (and `*default*` of `export default
    /// expression`), step 26: a binding in its temporal dead zone: the hole.
    Uninitialized,
    /// A function declaration (step 27): a closure of the template at this
    /// index of [`Program::functions`], over the module environment.
    Function(u32),
    /// A named or default import (step 8): an indirect binding to what
    /// ResolveExport finds for the entry at this index of
    /// [`ModuleProgram::import_entries`], read with
    /// [`crate::bytecode::Instr::GetImportBinding`].
    Import(u32),
    /// A namespace import (step 7): an immutable binding holding the namespace
    /// object of the module the entry at this index requests.
    Namespace(u32),
}

/// One binding of the module scope, with its slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleBinding {
    /// The name (`*default*` for the binding of an anonymous default export).
    pub name: Vec<u16>,
    /// The slot in the module environment object.
    pub slot: u32,
    /// What link time puts there.
    pub init: ModuleBindingInit,
}

/// A compiled module: see the module header.
#[derive(Clone, Debug, PartialEq)]
pub struct ModuleProgram {
    /// The code: function 0 is the module body, of kind
    /// [`crate::bytecode::FunctionKind::Module`], async if the module has
    /// top-level `await`.
    pub program: Program,
    /// `[[RequestedModules]]`, in order of first appearance.
    pub requested_modules: Vec<ModuleRequest>,
    /// `[[ImportEntries]]`.
    pub import_entries: Vec<ImportEntry>,
    /// `[[LocalExportEntries]]`.
    pub local_export_entries: Vec<ExportEntry>,
    /// `[[IndirectExportEntries]]`.
    pub indirect_export_entries: Vec<ExportEntry>,
    /// `[[StarExportEntries]]`.
    pub star_export_entries: Vec<ExportEntry>,
    /// `[[HasTLA]]`: the body contains `await` or `for await` outside any
    /// function, so it is evaluated as an async function body.
    pub has_tla: bool,
    /// The number of slots of the module environment object.
    pub env_size: u32,
    /// The user-visible bindings of the module environment.
    pub bindings: Vec<ModuleBinding>,
}

/// The static entries of a module, from the syntax alone.
pub(crate) struct Entries {
    pub requested: Vec<ModuleRequest>,
    pub imports: Vec<ImportEntry>,
    pub locals: Vec<ExportEntry>,
    pub indirects: Vec<ExportEntry>,
    pub stars: Vec<ExportEntry>,
}

/// The name of the `*default*` binding (§16.2.3.7†: BoundNames of an anonymous
/// default export).
pub(crate) const DEFAULT_LOCAL: &str = "*default*";

fn node(ast: &Ast, i: u32) -> Result<&Node, CompileError> {
    ast.nodes
        .get(i as usize)
        .ok_or(CompileError::Internal("node index out of range"))
}

fn child(nd: &Node, i: usize) -> Result<u32, CompileError> {
    nd.children
        .get(i)
        .copied()
        .ok_or(CompileError::Internal("missing child"))
}

/// The string value of a ModuleExportName, a ModuleSpecifier or an attribute key:
/// an IdentifierName (its StringValue) or a StringLiteral (its SV).
fn export_name_of(ast: &Ast, src: &[u32], n: u32) -> Result<Vec<u16>, CompileError> {
    let nd = node(ast, n)?;
    match nd.kind {
        NodeKind::StringLiteral => literal::string_at(src, nd.start),
        _ => literal::name_units_at(src, nd.start),
    }
}

/// Adds the request of a declaration (`spec`: its StringLiteral, `with`: its
/// WithClause or Absent) to `requested`, and returns its index.
fn request(
    ast: &Ast,
    src: &[u32],
    requested: &mut Vec<ModuleRequest>,
    spec: u32,
    with: u32,
) -> Result<u32, CompileError> {
    let sn = node(ast, spec)?;
    let mut attributes = Vec::new();
    let wn = node(ast, with)?;
    if wn.kind == NodeKind::WithClause {
        for &a in &wn.children {
            let an = node(ast, a)?;
            let key = export_name_of(ast, src, child(an, 0)?)?;
            let value = export_name_of(ast, src, child(an, 1)?)?;
            attributes.push(ImportAttribute { key, value });
        }
    }
    let req = ModuleRequest {
        specifier: literal::string_at(src, sn.start)?,
        attributes,
    };
    let idx = match requested.iter().position(|r| r.same_as(&req)) {
        Some(i) => i,
        None => {
            requested.push(req);
            requested.len().saturating_sub(1)
        }
    };
    u32::try_from(idx).map_err(|_| CompileError::TooLarge("module requests"))
}

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

/// The BoundNames of the declaration node `d` of an `export`: the names of a
/// variable statement, lexical declaration, function or class.
fn declared_names(ast: &Ast, src: &[u32], d: u32) -> Result<Vec<Vec<u16>>, CompileError> {
    let dn = node(ast, d)?;
    let mut targets: Vec<u32> = Vec::new();
    match dn.kind {
        NodeKind::VariableStatement
        | NodeKind::VariableDeclarationList
        | NodeKind::LexicalDeclaration => {
            for &b in &dn.children {
                targets.push(child(node(ast, b)?, 0)?);
            }
        }
        _ => targets.push(child(dn, 0)?),
    }
    let mut out = Vec::new();
    for t in targets {
        for id in bound_idents(ast, t)? {
            out.push(literal::name_units_at(src, node(ast, id)?.start)?);
        }
    }
    Ok(out)
}

/// ModuleRequests, ImportEntries and ExportEntries of the module body, and
/// ParseModule's partition of the export entries (§16.2.1.6.1† steps 8 to 10).
pub(crate) fn entries(ast: &Ast, src: &[u32]) -> Result<Entries, CompileError> {
    let root = node(ast, ast.root)?;
    let mut requested: Vec<ModuleRequest> = Vec::new();
    let mut imports: Vec<ImportEntry> = Vec::new();
    let mut exports: Vec<ExportEntry> = Vec::new();
    for &item in &root.children {
        let it = node(ast, item)?;
        match it.kind {
            NodeKind::ImportDeclaration => {
                let (clause, spec, with) = (child(it, 0)?, child(it, 1)?, child(it, 2)?);
                let r = request(ast, src, &mut requested, spec, with)?;
                let cn = node(ast, clause)?;
                if cn.kind != NodeKind::ImportClause {
                    continue;
                }
                let local_of = |b: u32| -> Result<Vec<u16>, CompileError> {
                    literal::name_units_at(src, node(ast, b)?.start)
                };
                let default = child(cn, 0)?;
                if node(ast, default)?.kind == NodeKind::BindingIdentifier {
                    imports.push(ImportEntry {
                        module_request: r,
                        import_name: ImportName::Name(units("default")),
                        local_name: local_of(default)?,
                    });
                }
                let named = child(cn, 1)?;
                let nn = node(ast, named)?;
                match nn.kind {
                    NodeKind::NameSpaceImport => {
                        imports.push(ImportEntry {
                            module_request: r,
                            import_name: ImportName::Namespace,
                            local_name: local_of(child(nn, 0)?)?,
                        });
                    }
                    NodeKind::NamedImports => {
                        for &s in &nn.children {
                            let sn = node(ast, s)?;
                            let (imported, binding) = (child(sn, 0)?, child(sn, 1)?);
                            let local = local_of(binding)?;
                            let name = if node(ast, imported)?.kind == NodeKind::Absent {
                                local.clone()
                            } else {
                                export_name_of(ast, src, imported)?
                            };
                            imports.push(ImportEntry {
                                module_request: r,
                                import_name: ImportName::Name(name),
                                local_name: local,
                            });
                        }
                    }
                    _ => {}
                }
            }
            NodeKind::ExportDeclaration => match it.op {
                AOp::ExportAll => {
                    let r = request(ast, src, &mut requested, child(it, 0)?, child(it, 1)?)?;
                    exports.push(ExportEntry {
                        export_name: None,
                        module_request: Some(r),
                        import_name: Some(ExportImportName::AllButDefault),
                        local_name: None,
                    });
                }
                AOp::ExportAllAs => {
                    let r = request(ast, src, &mut requested, child(it, 1)?, child(it, 2)?)?;
                    exports.push(ExportEntry {
                        export_name: Some(export_name_of(ast, src, child(it, 0)?)?),
                        module_request: Some(r),
                        import_name: Some(ExportImportName::All),
                        local_name: None,
                    });
                }
                AOp::ExportFrom => {
                    let r = request(ast, src, &mut requested, child(it, 1)?, child(it, 2)?)?;
                    let ne = node(ast, child(it, 0)?)?;
                    for &s in &ne.children {
                        let sn = node(ast, s)?;
                        let name = export_name_of(ast, src, child(sn, 0)?)?;
                        let exported = child(sn, 1)?;
                        let export_name = if node(ast, exported)?.kind == NodeKind::Absent {
                            name.clone()
                        } else {
                            export_name_of(ast, src, exported)?
                        };
                        exports.push(ExportEntry {
                            export_name: Some(export_name),
                            module_request: Some(r),
                            import_name: Some(ExportImportName::Name(name)),
                            local_name: None,
                        });
                    }
                }
                AOp::ExportNamed => {
                    let ne = node(ast, child(it, 0)?)?;
                    for &s in &ne.children {
                        let sn = node(ast, s)?;
                        let name = export_name_of(ast, src, child(sn, 0)?)?;
                        let exported = child(sn, 1)?;
                        let export_name = if node(ast, exported)?.kind == NodeKind::Absent {
                            name.clone()
                        } else {
                            export_name_of(ast, src, exported)?
                        };
                        exports.push(ExportEntry {
                            export_name: Some(export_name),
                            module_request: None,
                            import_name: None,
                            local_name: Some(name),
                        });
                    }
                }
                AOp::ExportVar | AOp::ExportDecl => {
                    for name in declared_names(ast, src, child(it, 0)?)? {
                        exports.push(ExportEntry {
                            export_name: Some(name.clone()),
                            module_request: None,
                            import_name: None,
                            local_name: Some(name),
                        });
                    }
                }
                AOp::ExportDefaultHoistable | AOp::ExportDefaultClass => {
                    let d = node(ast, child(it, 0)?)?;
                    let nm = child(d, 0)?;
                    let local = if node(ast, nm)?.kind == NodeKind::BindingIdentifier {
                        literal::name_units_at(src, node(ast, nm)?.start)?
                    } else {
                        units(DEFAULT_LOCAL)
                    };
                    exports.push(ExportEntry {
                        export_name: Some(units("default")),
                        module_request: None,
                        import_name: None,
                        local_name: Some(local),
                    });
                }
                AOp::ExportDefaultExpression => {
                    exports.push(ExportEntry {
                        export_name: Some(units("default")),
                        module_request: None,
                        import_name: None,
                        local_name: Some(units(DEFAULT_LOCAL)),
                    });
                }
                _ => return Err(CompileError::Internal("unknown export declaration")),
            },
            _ => {}
        }
    }
    // §16.2.1.6.1† steps 9 and 10: the partition.
    let mut locals = Vec::new();
    let mut indirects = Vec::new();
    let mut stars = Vec::new();
    for ee in exports {
        match ee.module_request {
            None => {
                let imported = imports
                    .iter()
                    .find(|ie| Some(&ie.local_name) == ee.local_name.as_ref());
                match imported {
                    None => locals.push(ee),
                    Some(ie) => match &ie.import_name {
                        // Re-exporting a namespace import is a local export of
                        // its (immutable) binding.
                        ImportName::Namespace => locals.push(ee),
                        ImportName::Name(n) => indirects.push(ExportEntry {
                            export_name: ee.export_name,
                            module_request: Some(ie.module_request),
                            import_name: Some(ExportImportName::Name(n.clone())),
                            local_name: None,
                        }),
                    },
                }
            }
            Some(_) => {
                if ee.import_name == Some(ExportImportName::AllButDefault) {
                    stars.push(ee);
                } else {
                    indirects.push(ee);
                }
            }
        }
    }
    Ok(Entries {
        requested,
        imports,
        locals,
        indirects,
        stars,
    })
}

/// The executable form of the record's consistency conditions, as
/// [`crate::bytecode::check_program`] is for the code: every request index is
/// in range, slots are below `env_size` and distinct, function and import-entry
/// references are in range, every local export names a binding, and the
/// body is function 0 of kind Module.
pub fn check_module(m: &ModuleProgram) -> Result<(), &'static str> {
    crate::bytecode::check_program(&m.program)?;
    if m.program.main != 0 {
        return Err("the module body is not function 0");
    }
    match m.program.functions.first() {
        Some(f) if f.kind == crate::bytecode::FunctionKind::Module => {}
        _ => return Err("function 0 is not a module body"),
    }
    let nreq = m.requested_modules.len();
    let req_ok = |r: u32| (r as usize) < nreq;
    for ie in &m.import_entries {
        if !req_ok(ie.module_request) {
            return Err("an import entry's request is out of range");
        }
    }
    for (i, a) in m.requested_modules.iter().enumerate() {
        if m.requested_modules
            .iter()
            .skip(i.saturating_add(1))
            .any(|b| a.same_as(b))
        {
            return Err("a module request is listed twice");
        }
    }
    let mut seen_slots = std::collections::HashSet::new();
    let mut seen_names = std::collections::HashSet::new();
    for b in &m.bindings {
        if b.slot >= m.env_size || !seen_slots.insert(b.slot) {
            return Err("a binding's slot is out of range or shared");
        }
        if !seen_names.insert(b.name.clone()) {
            return Err("a binding is listed twice");
        }
        match &b.init {
            ModuleBindingInit::Function(f) if (*f as usize) >= m.program.functions.len() => {
                return Err("a hoisted function is out of range");
            }
            ModuleBindingInit::Import(e) | ModuleBindingInit::Namespace(e)
                if (*e as usize) >= m.import_entries.len() =>
            {
                return Err("a binding's import entry is out of range");
            }
            _ => {}
        }
    }
    for e in &m.import_entries {
        if !m.bindings.iter().any(|b| b.name == e.local_name) {
            return Err("an import entry has no binding");
        }
    }
    for e in &m.local_export_entries {
        let ok = e.module_request.is_none()
            && e.export_name.is_some()
            && e.local_name
                .as_ref()
                .is_some_and(|n| m.bindings.iter().any(|b| &b.name == n));
        if !ok {
            return Err("a local export names no binding");
        }
    }
    for e in m
        .indirect_export_entries
        .iter()
        .chain(&m.star_export_entries)
    {
        let ok = e.module_request.is_some_and(req_ok)
            && e.import_name.is_some()
            && e.local_name.is_none();
        if !ok {
            return Err("an indirect or star export is malformed");
        }
    }
    for e in &m.star_export_entries {
        if e.export_name.is_some() || e.import_name != Some(ExportImportName::AllButDefault) {
            return Err("a star export is malformed");
        }
    }
    let mut exported = std::collections::HashSet::new();
    for e in m
        .local_export_entries
        .iter()
        .chain(&m.indirect_export_entries)
    {
        if let Some(n) = &e.export_name
            && !exported.insert(n.clone())
        {
            return Err("an export name is exported twice");
        }
    }
    Ok(())
}
