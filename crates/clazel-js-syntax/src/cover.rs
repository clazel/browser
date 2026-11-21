//! The cover grammars (ECMA-262 §13.2.9, §13.2.5.1, §13.15.5, §15.9), read as
//! the refined productions. The parser reads an `ObjectLiteral`, an
//! `ArrayLiteral` or a parenthesized list as an expression first; once the
//! `=` or `=>` that says what it is has been seen, these functions build the
//! pattern node for the same tokens (the standard: "the interpretation of
//! [the cover] is refined using the following grammar").

use crate::ast::{NodeKind as K, Op};
use crate::parser::{Parser, R, syn};

impl<'a> Parser<'a> {
    /// An absent optional symbol at `pos`.
    fn absent_at(&mut self, pos: usize) -> u32 {
        self.leaf(K::Absent, pos, pos)
    }

    /// The children of `id`.
    fn kids(&self, id: u32) -> Vec<u32> {
        self.node(id)
            .map(|n| n.children.clone())
            .unwrap_or_default()
    }

    /// `DestructuringAssignmentTarget`, and the target of `=`: a
    /// `LeftHandSideExpression` that is not an `ObjectLiteral` or an
    /// `ArrayLiteral`, or an assignment pattern read from one of them.
    pub fn as_assign_target(&mut self, id: u32) -> R<u32> {
        match self.kind(id) {
            K::ObjectLiteral => self.obj_to_assign(id),
            K::ArrayLiteral => self.arr_to_assign(id),
            K::ObjectAssignmentPattern | K::ArrayAssignmentPattern => Ok(id),
            _ => {
                if self.lvl(id) >= 14 {
                    Ok(id)
                } else {
                    syn()
                }
            }
        }
    }

    /// An `AssignmentElement`: a target with an optional initializer.
    fn as_assign_element(&mut self, c: u32) -> R<u32> {
        let (s, e) = (self.st(c), self.en(c));
        if self.kind(c) == K::AssignmentExpression && self.op(c) == Op::Assign {
            let (t, init) = (self.child(c, 0), self.child(c, 1));
            Ok(self.mk(K::AssignmentElement, Op::None, false, s, e, vec![t, init]))
        } else {
            let t = self.as_assign_target(c)?;
            let a = self.absent_at(e);
            Ok(self.mk(K::AssignmentElement, Op::None, false, s, e, vec![t, a]))
        }
    }

    /// §13.15.5 `ObjectAssignmentPattern` read from an `ObjectLiteral`.
    fn obj_to_assign(&mut self, id: u32) -> R<u32> {
        let kids = self.kids(id);
        let n = kids.len();
        let mut out = Vec::new();
        for (k, c) in kids.iter().copied().enumerate() {
            let last = k.saturating_add(1) == n;
            let (s, e) = (self.st(c), self.en(c));
            match (self.kind(c), self.op(c)) {
                (K::PropertyDefinition, Op::Shorthand) => {
                    let ident = self.child(c, 0);
                    let a = self.absent_at(e);
                    out.push(self.mk(
                        K::AssignmentProperty,
                        Op::Shorthand,
                        false,
                        s,
                        e,
                        vec![ident, a],
                    ));
                }
                (K::CoverInitializedName, _) => {
                    let (ident, init) = (self.child(c, 0), self.child(c, 1));
                    out.push(self.mk(
                        K::AssignmentProperty,
                        Op::Shorthand,
                        false,
                        s,
                        e,
                        vec![ident, init],
                    ));
                }
                (K::PropertyDefinition, Op::KeyValue) => {
                    let (name, v) = (self.child(c, 0), self.child(c, 1));
                    let el = self.as_assign_element(v)?;
                    out.push(self.mk(
                        K::AssignmentProperty,
                        Op::KeyValue,
                        false,
                        s,
                        e,
                        vec![name, el],
                    ));
                }
                (K::PropertyDefinition, Op::Spread) => {
                    if !last || self.rest_comma.contains(&id) {
                        return syn();
                    }
                    let x = self.child(c, 0);
                    if matches!(self.kind(x), K::ObjectLiteral | K::ArrayLiteral) {
                        return syn();
                    }
                    let t = self.as_assign_target(x)?;
                    out.push(self.mk(K::AssignmentRestProperty, Op::None, false, s, e, vec![t]));
                }
                _ => return syn(),
            }
        }
        let (s, e) = (self.st(id), self.en(id));
        Ok(self.mk(K::ObjectAssignmentPattern, Op::None, false, s, e, out))
    }

    /// §13.15.5 `ArrayAssignmentPattern` read from an `ArrayLiteral`.
    fn arr_to_assign(&mut self, id: u32) -> R<u32> {
        let kids = self.kids(id);
        let n = kids.len();
        let mut out = Vec::new();
        for (k, c) in kids.iter().copied().enumerate() {
            let last = k.saturating_add(1) == n;
            let (s, e) = (self.st(c), self.en(c));
            match self.kind(c) {
                K::Elision => out.push(c),
                K::SpreadElement => {
                    if !last || self.rest_comma.contains(&id) {
                        return syn();
                    }
                    let t = self.as_assign_target(self.child(c, 0))?;
                    out.push(self.mk(K::AssignmentRestElement, Op::None, false, s, e, vec![t]));
                }
                _ => out.push(self.as_assign_element(c)?),
            }
        }
        let (s, e) = (self.st(id), self.en(id));
        Ok(self.mk(K::ArrayAssignmentPattern, Op::None, false, s, e, out))
    }

    /// A `BindingIdentifier` or `BindingPattern` read from an expression or an
    /// assignment pattern (the parameters of an arrow function).
    pub fn as_binding_target(&mut self, id: u32) -> R<u32> {
        let (s, e) = (self.st(id), self.en(id));
        match self.kind(id) {
            K::IdentifierReference => Ok(self.leaf(K::BindingIdentifier, s, e)),
            K::BindingIdentifier | K::ObjectBindingPattern | K::ArrayBindingPattern => Ok(id),
            K::ObjectLiteral | K::ObjectAssignmentPattern => self.obj_to_binding(id),
            K::ArrayLiteral | K::ArrayAssignmentPattern => self.arr_to_binding(id),
            _ => syn(),
        }
    }

    /// A `BindingElement` read from an expression or an assignment element.
    pub fn as_binding_element(&mut self, id: u32) -> R<u32> {
        let (s, e) = (self.st(id), self.en(id));
        match (self.kind(id), self.op(id)) {
            (K::AssignmentExpression, Op::Assign) | (K::AssignmentElement, _) => {
                let (t, init) = (self.child(id, 0), self.child(id, 1));
                let bt = self.as_binding_target(t)?;
                Ok(self.mk(K::BindingElement, Op::None, false, s, e, vec![bt, init]))
            }
            _ => {
                let bt = self.as_binding_target(id)?;
                let a = self.absent_at(e);
                Ok(self.mk(K::BindingElement, Op::None, false, s, e, vec![bt, a]))
            }
        }
    }

    /// §14.3.3 `ObjectBindingPattern`.
    fn obj_to_binding(&mut self, id: u32) -> R<u32> {
        let kids = self.kids(id);
        let n = kids.len();
        let mut out = Vec::new();
        for (k, c) in kids.iter().copied().enumerate() {
            let last = k.saturating_add(1) == n;
            let (s, e) = (self.st(c), self.en(c));
            match (self.kind(c), self.op(c)) {
                (K::PropertyDefinition, Op::Shorthand) => {
                    let ident = self.child(c, 0);
                    let bi = self.as_binding_target(ident)?;
                    let a = self.absent_at(e);
                    let el = self.mk(K::BindingElement, Op::None, false, s, e, vec![bi, a]);
                    out.push(self.mk(K::BindingProperty, Op::Shorthand, false, s, e, vec![el]));
                }
                (K::CoverInitializedName, _) | (K::AssignmentProperty, Op::Shorthand) => {
                    let (ident, init) = (self.child(c, 0), self.child(c, 1));
                    let bi = self.as_binding_target(ident)?;
                    let el = self.mk(K::BindingElement, Op::None, false, s, e, vec![bi, init]);
                    out.push(self.mk(K::BindingProperty, Op::Shorthand, false, s, e, vec![el]));
                }
                (K::PropertyDefinition, Op::KeyValue) | (K::AssignmentProperty, Op::KeyValue) => {
                    let (name, v) = (self.child(c, 0), self.child(c, 1));
                    let el = self.as_binding_element(v)?;
                    out.push(self.mk(
                        K::BindingProperty,
                        Op::KeyValue,
                        false,
                        s,
                        e,
                        vec![name, el],
                    ));
                }
                (K::PropertyDefinition, Op::Spread) | (K::AssignmentRestProperty, _) => {
                    if !last || self.rest_comma.contains(&id) {
                        return syn();
                    }
                    let x = self.child(c, 0);
                    if !matches!(self.kind(x), K::IdentifierReference | K::BindingIdentifier) {
                        return syn();
                    }
                    let bi = self.as_binding_target(x)?;
                    out.push(self.mk(K::BindingRestProperty, Op::None, false, s, e, vec![bi]));
                }
                _ => return syn(),
            }
        }
        let (s, e) = (self.st(id), self.en(id));
        Ok(self.mk(K::ObjectBindingPattern, Op::None, false, s, e, out))
    }

    /// §14.3.3 `ArrayBindingPattern`.
    fn arr_to_binding(&mut self, id: u32) -> R<u32> {
        let kids = self.kids(id);
        let n = kids.len();
        let mut out = Vec::new();
        for (k, c) in kids.iter().copied().enumerate() {
            let last = k.saturating_add(1) == n;
            let (s, e) = (self.st(c), self.en(c));
            match self.kind(c) {
                K::Elision => out.push(c),
                K::SpreadElement | K::AssignmentRestElement => {
                    if !last || self.rest_comma.contains(&id) {
                        return syn();
                    }
                    let t = self.as_binding_target(self.child(c, 0))?;
                    out.push(self.mk(K::BindingRestElement, Op::None, false, s, e, vec![t]));
                }
                _ => out.push(self.as_binding_element(c)?),
            }
        }
        let (s, e) = (self.st(id), self.en(id));
        Ok(self.mk(K::ArrayBindingPattern, Op::None, false, s, e, out))
    }
}
