//! The cells the interpreter allocates in `clazel-js-heap`'s arena, and the
//! property operations on them (item 7.8, first slice).
//!
//! `clazel-js-heap` on `main` has the arena, strings, interned keys and
//! shapes, but no object type: the elements, symbols and collector slices are
//! open pull requests. This module is the VM's own cell type over the arena
//! (`spec::Cell`): a string, an ordinary object (properties by shape, a
//! prototype, and what kind of object it is) and a declarative environment.
//! It holds only data properties; accessors, elements and exotic objects come
//! with the later slices. Nothing here is collected: the collector is item
//! 7.6.

use clazel_js_heap::arena::{Arena, Error as ArenaError};
use clazel_js_heap::shape::{Attrs, Error as ShapeError, ROOT, ShapeId, Shapes};
use clazel_js_heap::string::{Interner, JsString, Key, TooLong};
use clazel_js_heap::value::Value;

/// The longest prototype chain a lookup walks before it gives up (a cycle
/// cannot be built by this slice's handlers; the bound keeps a corrupt heap
/// from looping).
pub const MAX_PROTO_DEPTH: usize = 100_000;

/// What an object is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjKind {
    /// An ordinary object.
    Plain,
    /// A compiled function: its index in the VM's code table and its
    /// captured environment (`spec::FnInfo`): a heap reference, or
    /// `undefined`.
    Closure {
        /// The index of the function's code in the VM's table.
        code: u32,
        /// The captured environment.
        env: Value,
    },
    /// A native function: its index in the VM's native table.
    Native(u32),
    /// A bound function exotic object (§10.4.1†): its index in the VM's
    /// table of bound targets, `this` values and arguments.
    Bound(u32),
    /// An object with `[[ErrorData]]` (§20.5†): made by an `Error`
    /// constructor or thrown by the VM.
    Error,
    /// A Boolean, Number or String wrapper object: the object holds the
    /// primitive as `[[BooleanData]]`, `[[NumberData]]` or `[[StringData]]`
    /// (§20.3†, §21.1†, §22.1†).
    Primitive(Value),
}

/// An object: properties by shape, a prototype and a kind.
#[derive(Debug)]
pub struct Obj {
    /// The shape: the keys, slot indices and attributes of the properties.
    pub shape: ShapeId,
    /// The property values, by the shape's slot indices.
    pub slots: Vec<Value>,
    /// `[[Prototype]]`: an object reference or `null`.
    pub proto: Value,
    /// What the object is.
    pub kind: ObjKind,
}

/// A declarative environment (`spec::Class::Env`).
#[derive(Debug)]
pub struct Env {
    /// The enclosing environment, or `undefined` for the outermost.
    pub parent: Value,
    /// The bindings.
    pub slots: Vec<Value>,
}

/// A heap cell.
#[derive(Debug)]
pub enum Cell {
    /// A String value.
    Str(JsString),
    /// An object.
    Object(Obj),
    /// An environment.
    Env(Env),
}

/// Why a heap operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeapError {
    /// The arena is full.
    Full,
    /// A string would pass the length limit.
    TooLong,
    /// A reference is stale or out of range, or a cell is not what the
    /// operation needs: the heap invariants do not hold.
    Corrupt,
}

impl From<ArenaError> for HeapError {
    fn from(e: ArenaError) -> Self {
        match e {
            ArenaError::Full => HeapError::Full,
            _ => HeapError::Corrupt,
        }
    }
}

impl From<TooLong> for HeapError {
    fn from(_: TooLong) -> Self {
        HeapError::TooLong
    }
}

impl From<ShapeError> for HeapError {
    fn from(e: ShapeError) -> Self {
        match e {
            ShapeError::TooMany => HeapError::Full,
            _ => HeapError::Corrupt,
        }
    }
}

/// A property found on an object or its prototype chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Found {
    /// The object that has the property.
    pub holder: Value,
    /// The holder's shape.
    pub shape: ShapeId,
    /// The property's slot.
    pub slot: u32,
    /// Its attributes.
    pub attrs: Attrs,
    /// Whether the holder is the object the search started at.
    pub own: bool,
}

/// The heap: the arena of cells, the shape table and the key interner.
#[derive(Debug)]
pub struct Heap {
    arena: Arena<Cell>,
    shapes: Shapes,
    keys: Interner,
}

impl Heap {
    /// An empty heap whose arena holds at most `limit` cells.
    #[must_use]
    pub fn new(limit: usize) -> Self {
        Self {
            arena: Arena::with_limit(limit),
            shapes: Shapes::new(),
            keys: Interner::new(),
        }
    }

    /// The number of live cells.
    #[must_use]
    pub fn live(&self) -> usize {
        self.arena.live()
    }

    /// Allocates a cell and returns the reference to it as a value.
    ///
    /// # Errors
    /// [`HeapError::Full`] if the arena is full.
    pub fn alloc(&mut self, cell: Cell) -> Result<Value, HeapError> {
        let r = self.arena.alloc(cell)?;
        Ok(Value::heap_ref(r))
    }

    /// Allocates a string.
    ///
    /// # Errors
    /// [`HeapError::Full`] if the arena is full.
    pub fn new_string(&mut self, s: JsString) -> Result<Value, HeapError> {
        self.alloc(Cell::Str(s))
    }

    /// Allocates a string from a Rust string.
    ///
    /// # Errors
    /// [`HeapError::Full`] or [`HeapError::TooLong`].
    pub fn new_str(&mut self, s: &str) -> Result<Value, HeapError> {
        self.new_string(JsString::from_rust_str(s)?)
    }

    /// Allocates an ordinary object with `proto` as its prototype.
    ///
    /// # Errors
    /// [`HeapError::Full`] if the arena is full.
    pub fn new_object(&mut self, proto: Value, kind: ObjKind) -> Result<Value, HeapError> {
        self.alloc(Cell::Object(Obj {
            shape: ROOT,
            slots: Vec::new(),
            proto,
            kind,
        }))
    }

    /// The live cell a value refers to.
    #[must_use]
    pub fn cell(&self, v: Value) -> Option<&Cell> {
        self.arena.get(v.as_ref()?).ok()
    }

    fn cell_mut(&mut self, v: Value) -> Option<&mut Cell> {
        self.arena.get_mut(v.as_ref()?).ok()
    }

    /// The object a value refers to, if it refers to one.
    #[must_use]
    pub fn obj(&self, v: Value) -> Option<&Obj> {
        match self.cell(v)? {
            Cell::Object(o) => Some(o),
            _ => None,
        }
    }

    /// The object a value refers to, mutably.
    pub fn obj_mut(&mut self, v: Value) -> Option<&mut Obj> {
        match self.cell_mut(v)? {
            Cell::Object(o) => Some(o),
            _ => None,
        }
    }

    /// The string a value refers to, if it refers to one.
    #[must_use]
    pub fn string(&self, v: Value) -> Option<&JsString> {
        match self.cell(v)? {
            Cell::Str(s) => Some(s),
            _ => None,
        }
    }

    /// The environment a value refers to, if it refers to one.
    #[must_use]
    pub fn env(&self, v: Value) -> Option<&Env> {
        match self.cell(v)? {
            Cell::Env(e) => Some(e),
            _ => None,
        }
    }

    /// The environment a value refers to, mutably.
    pub fn env_mut(&mut self, v: Value) -> Option<&mut Env> {
        match self.cell_mut(v)? {
            Cell::Env(e) => Some(e),
            _ => None,
        }
    }

    /// Whether a value is a reference to a string.
    #[must_use]
    pub fn is_string(&self, v: Value) -> bool {
        self.string(v).is_some()
    }

    /// Whether a value is a reference to an object.
    #[must_use]
    pub fn is_object(&self, v: Value) -> bool {
        self.obj(v).is_some()
    }

    /// Whether a value is a reference to a callable object.
    #[must_use]
    pub fn is_callable(&self, v: Value) -> bool {
        self.obj(v).is_some_and(|o| {
            matches!(
                o.kind,
                ObjKind::Closure { .. } | ObjKind::Native(_) | ObjKind::Bound(_)
            )
        })
    }

    /// The interned key of a string.
    ///
    /// # Errors
    /// [`HeapError::TooLong`].
    pub fn intern(&mut self, s: &JsString) -> Result<Key, HeapError> {
        Ok(self.keys.intern(s)?)
    }

    /// The interned key of a Rust string.
    ///
    /// # Errors
    /// [`HeapError::TooLong`].
    pub fn intern_str(&mut self, s: &str) -> Result<Key, HeapError> {
        let js = JsString::from_rust_str(s)?;
        self.intern(&js)
    }

    /// The string a key stands for.
    #[must_use]
    pub fn key_string(&self, k: Key) -> Option<&JsString> {
        self.keys.resolve(k)
    }

    /// Searches `start` and its prototype chain for the own data property
    /// `key` (`[[GetOwnProperty]]` on each object, §10.1.5, then
    /// `[[Prototype]]`, §10.1.8.1 step 3).
    ///
    /// # Errors
    /// [`HeapError::Corrupt`] if the chain runs past [`MAX_PROTO_DEPTH`].
    pub fn find(&self, start: Value, key: Key) -> Result<Option<Found>, HeapError> {
        let mut cur = start;
        for depth in 0..MAX_PROTO_DEPTH {
            let Some(o) = self.obj(cur) else {
                return Ok(None);
            };
            if let Some((slot, attrs)) = self.shapes.lookup(o.shape, key) {
                return Ok(Some(Found {
                    holder: cur,
                    shape: o.shape,
                    slot,
                    attrs,
                    own: depth == 0,
                }));
            }
            cur = o.proto;
        }
        Err(HeapError::Corrupt)
    }

    /// The value in a slot of an object.
    #[must_use]
    pub fn slot(&self, holder: Value, slot: u32) -> Option<Value> {
        let i = usize::try_from(slot).ok()?;
        self.obj(holder)?.slots.get(i).copied()
    }

    /// Whether the shape is a dictionary shape, which an inline cache does not
    /// key on (its id stays the same as properties are added).
    #[must_use]
    pub fn is_dictionary(&self, shape: ShapeId) -> bool {
        self.shapes.is_dictionary(shape)
    }

    /// Defines or overwrites the own data property `key` of `obj`: a new
    /// property gets `attrs`; an existing one keeps its attributes and takes
    /// the value (`CreateDataProperty` on an extensible object, §10.1.6.3,
    /// for every case the first slice reaches).
    ///
    /// # Errors
    /// [`HeapError::Corrupt`] if `obj` is not an object, [`HeapError::Full`]
    /// on overflow.
    pub fn define(
        &mut self,
        obj: Value,
        key: Key,
        value: Value,
        attrs: Attrs,
    ) -> Result<(), HeapError> {
        let shape = self.obj(obj).ok_or(HeapError::Corrupt)?.shape;
        if let Some((slot, _)) = self.shapes.lookup(shape, key) {
            return self.set_slot(obj, slot, value);
        }
        let (next, slot) = self.shapes.add_property(shape, key, attrs)?;
        let o = self.obj_mut(obj).ok_or(HeapError::Corrupt)?;
        let i = usize::try_from(slot).map_err(|_| HeapError::Full)?;
        if o.slots.len() != i {
            return Err(HeapError::Corrupt);
        }
        o.slots.push(value);
        o.shape = next;
        Ok(())
    }

    /// Stores into a slot of an object.
    ///
    /// # Errors
    /// [`HeapError::Corrupt`] if there is no such slot.
    pub fn set_slot(&mut self, obj: Value, slot: u32, value: Value) -> Result<(), HeapError> {
        let i = usize::try_from(slot).map_err(|_| HeapError::Corrupt)?;
        let s = self
            .obj_mut(obj)
            .and_then(|o| o.slots.get_mut(i))
            .ok_or(HeapError::Corrupt)?;
        *s = value;
        Ok(())
    }

    /// The own properties of an object in the order `[[OwnPropertyKeys]]`
    /// gives them (§10.1.11.1†): the array indices in ascending order, then
    /// the other string keys in the order they were created. (Symbols and
    /// exotic objects' keys come with the later slices.)
    #[must_use]
    pub fn own_properties(&self, obj: Value) -> Vec<(Key, Attrs, Value)> {
        let Some(o) = self.obj(obj) else {
            return Vec::new();
        };
        let mut indices: Vec<(u32, Key, Attrs, Value)> = Vec::new();
        let mut names: Vec<(Key, Attrs, Value)> = Vec::new();
        for (k, slot, a) in self.shapes.properties(o.shape) {
            let Some(v) = usize::try_from(slot)
                .ok()
                .and_then(|i| o.slots.get(i))
                .copied()
            else {
                continue;
            };
            match self.keys.resolve(k).and_then(canonical_index) {
                Some(i) => indices.push((i, k, a, v)),
                None => names.push((k, a, v)),
            }
        }
        indices.sort_by_key(|e| e.0);
        let mut out: Vec<(Key, Attrs, Value)> =
            indices.into_iter().map(|(_, k, a, v)| (k, a, v)).collect();
        out.extend(names);
        out
    }

    /// Changes the value and attributes of the own property `key` (adding it
    /// if there is none): the shape is rebuilt from the root with the same
    /// order, so the property keeps its place in the key order.
    ///
    /// # Errors
    /// [`HeapError::Corrupt`] if `obj` is not an object, [`HeapError::Full`]
    /// on overflow.
    pub fn redefine(
        &mut self,
        obj: Value,
        key: Key,
        value: Value,
        attrs: Attrs,
    ) -> Result<(), HeapError> {
        let o = self.obj(obj).ok_or(HeapError::Corrupt)?;
        let Some((slot, old)) = self.shapes.lookup(o.shape, key) else {
            return self.define(obj, key, value, attrs);
        };
        if old == attrs {
            return self.set_slot(obj, slot, value);
        }
        let props = self.shapes.properties(o.shape);
        let mut shape = ROOT;
        for (k, _, a) in props {
            let a = if k == key { attrs } else { a };
            let (next, _) = self.shapes.add_property(shape, k, a)?;
            shape = next;
        }
        self.set_slot(obj, slot, value)?;
        self.obj_mut(obj).ok_or(HeapError::Corrupt)?.shape = shape;
        Ok(())
    }

    /// Changes the `[[Prototype]]` of an object (no cycle check: the callers
    /// only pass fresh objects).
    ///
    /// # Errors
    /// [`HeapError::Corrupt`] if `obj` is not an object.
    pub fn set_proto(&mut self, obj: Value, proto: Value) -> Result<(), HeapError> {
        self.obj_mut(obj).ok_or(HeapError::Corrupt)?.proto = proto;
        Ok(())
    }

    /// The `[[Prototype]]` of an object.
    #[must_use]
    pub fn proto_of(&self, obj: Value) -> Option<Value> {
        self.obj(obj).map(|o| o.proto)
    }
}

/// The array index a string names (§6.1.7†): decimal digits, no leading
/// zero except `0` itself, below 2^32 - 1.
fn canonical_index(s: &JsString) -> Option<u32> {
    let mut n: u64 = 0;
    let mut len = 0usize;
    let mut first = 0u16;
    for u in s.units() {
        let d = u.checked_sub(u16::from(b'0')).filter(|d| *d < 10)?;
        if len == 0 {
            first = u;
        }
        n = n.checked_mul(10)?.checked_add(u64::from(d))?;
        len = len.checked_add(1)?;
    }
    if len == 0 || (len > 1 && first == u16::from(b'0')) || n >= 4_294_967_295 {
        return None;
    }
    u32::try_from(n).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn heap() -> Heap {
        Heap::new(1000)
    }

    #[test]
    fn properties_are_found_on_the_chain() -> Result<(), HeapError> {
        let mut h = heap();
        let proto = h.new_object(Value::NULL, ObjKind::Plain)?;
        let obj = h.new_object(proto, ObjKind::Plain)?;
        let (a, b) = (h.intern_str("a")?, h.intern_str("b")?);
        h.define(proto, a, Value::int32(1), Attrs::ALL)?;
        h.define(obj, b, Value::int32(2), Attrs::ALL)?;
        let fa = h.find(obj, a)?.ok_or(HeapError::Corrupt)?;
        assert!(!fa.own);
        assert_eq!(h.slot(fa.holder, fa.slot), Some(Value::int32(1)));
        let fb = h.find(obj, b)?.ok_or(HeapError::Corrupt)?;
        assert!(fb.own);
        assert_eq!(h.find(proto, b)?, None);
        h.define(obj, b, Value::int32(3), Attrs::ALL)?;
        assert_eq!(h.slot(obj, fb.slot), Some(Value::int32(3)));
        Ok(())
    }

    #[test]
    fn objects_that_gain_the_same_keys_share_a_shape() -> Result<(), HeapError> {
        let mut h = heap();
        let (x, y) = (
            h.new_object(Value::NULL, ObjKind::Plain)?,
            h.new_object(Value::NULL, ObjKind::Plain)?,
        );
        let k = h.intern_str("k")?;
        h.define(x, k, Value::TRUE, Attrs::ALL)?;
        h.define(y, k, Value::FALSE, Attrs::ALL)?;
        assert_eq!(h.obj(x).map(|o| o.shape), h.obj(y).map(|o| o.shape));
        Ok(())
    }

    #[test]
    fn own_properties_list_indices_first_and_redefine_keeps_order() -> Result<(), HeapError> {
        let mut h = heap();
        let o = h.new_object(Value::NULL, ObjKind::Plain)?;
        let names = ["b", "10", "a", "2"];
        for (i, n) in names.iter().enumerate() {
            let k = h.intern_str(n)?;
            h.define(
                o,
                k,
                Value::int32(i32::try_from(i).unwrap_or(0)),
                Attrs::ALL,
            )?;
        }
        let listed = |h: &Heap| -> Vec<String> {
            h.own_properties(o)
                .iter()
                .map(|(k, _, _)| {
                    h.key_string(*k)
                        .map(JsString::to_string_lossy)
                        .unwrap_or_default()
                })
                .collect()
        };
        assert_eq!(listed(&h), ["2", "10", "b", "a"]);
        let a = h.intern_str("a")?;
        h.redefine(o, a, Value::int32(9), Attrs(Attrs::WRITABLE))?;
        assert_eq!(listed(&h), ["2", "10", "b", "a"]);
        let found = h.find(o, a)?.ok_or(HeapError::Corrupt)?;
        assert_eq!(found.attrs, Attrs(Attrs::WRITABLE));
        assert_eq!(h.slot(o, found.slot), Some(Value::int32(9)));
        let b = h.intern_str("b")?;
        let fb = h.find(o, b)?.ok_or(HeapError::Corrupt)?;
        assert_eq!(h.slot(o, fb.slot), Some(Value::int32(0)));
        Ok(())
    }

    #[test]
    fn a_stale_or_wrong_reference_is_not_an_object() -> Result<(), HeapError> {
        let mut h = heap();
        let s = h.new_str("abc")?;
        assert!(h.is_string(s));
        assert!(!h.is_object(s));
        assert_eq!(h.obj(Value::int32(1)).map(|o| o.shape), None);
        Ok(())
    }
}
