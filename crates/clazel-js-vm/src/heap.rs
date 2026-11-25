//! The cells the interpreter allocates in `clazel-js-heap`'s arena, and the
//! property operations on them (item 7.8, first slice).
//!
//! `clazel-js-heap` on `main` has the arena, strings, interned keys and
//! shapes, but no object type: the elements, symbols and collector slices are
//! open pull requests. This module is the VM's own cell type over the arena
//! (`spec::Cell`): a string, a Symbol, an ordinary object (properties by
//! shape, a prototype, and what kind of object it is), a declarative
//! environment, and the iterator records of the iteration ops. It holds data
//! properties and accessor properties (an accessor's slot holds a
//! [`Cell::Accessor`] with its getter and setter, or a
//! [`Cell::LazyAccessor`] until they are first needed, and its attributes
//! carry [`ACCESSOR`]); elements and exotic objects come with the later
//! slices.
//! Nothing here is collected: the collector is item 7.6.
//!
//! A property key is a [`Key`]: an interned string, or a Symbol encoded by
//! `clazel-js-heap`'s symbol contract (Y4, [`encode`]), whose top bit is set.
//! The interner never hands out such a key (it would need 2^31 strings), so
//! the two never meet.

use clazel_js_heap::arena::{Arena, Error as ArenaError};
use clazel_js_heap::shape::{Attrs, Error as ShapeError, ROOT, ShapeId, Shapes};
use clazel_js_heap::string::{Interner, JsString, Key, TooLong};
use clazel_js_heap::symbol::SymbolId;
use clazel_js_heap::symbol::contract::{PropertyKey, decode, encode};
use clazel_js_heap::value::Value;

/// The longest prototype chain a lookup walks before it gives up (a cycle
/// cannot be built by this slice's handlers; the bound keeps a corrupt heap
/// from looping).
pub const MAX_PROTO_DEPTH: usize = 100_000;

/// The attribute bit of an accessor property (§6.1.7.1† Table 4): the
/// property's slot holds a [`Cell::Accessor`] (or a [`Cell::LazyAccessor`])
/// and not a value, and its `WRITABLE` bit is clear (an accessor property has no `[[Writable]]`).
/// `clazel-js-heap`'s shapes store the bits without reading them.
pub const ACCESSOR: u8 = 8;

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
    /// An Array exotic object (§10.4.2†). Its `length` is the first property
    /// (slot 0), made by [`Heap::new_array`] and never removed, so reading it
    /// is one slot access. The index properties are ordinary data properties
    /// in the shape, because `clazel-js-heap`'s elements (#211) are not on
    /// this base.
    Array,
    /// An Array Iterator (§23.1.5†): `[[IteratedArrayLike]]` (`undefined`
    /// once the iterator is done), `[[ArrayLikeNextIndex]]` and
    /// `[[ArrayLikeIterationKind]]`. (The standard's iterator is a generator
    /// closure, CreateArrayIterator §23.1.5.1†; these three slots are its
    /// state.)
    ArrayIterator {
        /// The array-like being iterated, or `undefined` when done.
        target: Value,
        /// The next index.
        next: u64,
        /// What each step gives.
        kind: IterKind,
    },
    /// A String Iterator (§22.1.5†): the string (`undefined` once done) and
    /// the code unit index of the next code point.
    StringIterator {
        /// The string being iterated, or `undefined` when done.
        target: Value,
        /// The index of the next code unit.
        next: u32,
    },
    /// An object with internal slots a built-in defines (`[[PromiseState]]`,
    /// `[[RegExpMatcher]]`, ...): its row in the VM's table of host objects
    /// (`crate::host`).
    Host(u32),
    /// An arguments exotic object (§10.4.4†, here always without a parameter
    /// map: see `crate::host`).
    Arguments,
}

/// `[[ArrayLikeIterationKind]]` of an Array Iterator (§23.1.5.1†).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IterKind {
    /// `key`: the indices.
    Keys,
    /// `value`: the elements.
    Values,
    /// `key+value`: `[index, element]` pairs.
    Entries,
}

/// A Symbol value (§6.1.5†): its id in the VM's symbol table (the
/// well-known symbols are ids 0 to 12, `clazel-js-heap`'s Y1) and its
/// `[[Description]]`, a string value or `undefined`. Each Symbol has exactly
/// one cell, so identity is equality of references.
#[derive(Clone, Copy, Debug)]
pub struct Sym {
    /// The id, which is also the property key's ([`Heap::symbol_key`]).
    pub id: SymbolId,
    /// `[[Description]]`: a string value or `undefined`.
    pub description: Value,
}

/// An Iterator Record (§7.4.1†) the iteration ops keep in a register:
/// `[[Iterator]]`, `[[NextMethod]]` and `[[Done]]`; or the state of a
/// `for`-`in` loop's iterator (EnumerateObjectProperties, §14.7.5.9†).
#[derive(Clone, Debug)]
pub enum IterRecord {
    /// An Iterator Record of the iterator protocol.
    Protocol {
        /// `[[Iterator]]`.
        iterator: Value,
        /// `[[NextMethod]]`.
        next: Value,
        /// `[[Done]]`.
        done: bool,
    },
    /// A `for`-`in` iterator: the object, the keys still to visit, in order,
    /// and the position.
    ForIn {
        /// The object whose keys are enumerated (`undefined` for a loop over
        /// `undefined` or `null`, which is done at once).
        object: Value,
        /// The enumerable string keys of the object and its prototype chain,
        /// each once, shadowed ones left out.
        keys: Vec<Key>,
        /// The index of the next key.
        pos: usize,
    },
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
    /// `[[Extensible]]` (§10.1.3†): false once `Object.preventExtensions`,
    /// `seal` or `freeze` ran. No property is added to such an object.
    pub extensible: bool,
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
    /// A Symbol value.
    Symbol(Sym),
    /// An iterator record (never reachable from JS: only registers hold it).
    Iter(IterRecord),
    /// The `[[Get]]` and `[[Set]]` of an accessor property (§6.1.7.1† Table
    /// 4): each a function object or `undefined`. Only an object's slot whose
    /// attributes carry [`ACCESSOR`] refers to one; it is never a language
    /// value.
    Accessor {
        /// `[[Get]]`.
        get: Value,
        /// `[[Set]]`.
        set: Value,
    },
    /// An accessor pair whose `[[Get]]` and `[[Set]]` function objects have
    /// not been made yet: the embedder's number for them
    /// (`Vm::define_lazy_accessor`). The first operation that needs either
    /// function has them made and turns this cell into a [`Cell::Accessor`]
    /// in place (`Vm::accessor_pair`), so the property's slot, and with it
    /// the identity of the functions from then on, never changes. Like an
    /// `Accessor`, it is never a language value.
    LazyAccessor(u32),
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

/// What one cell stands for in the heap's byte count (phase-7.md 7.19's heap
/// limit), before its payload: the arena slot, the enum and its tag.
pub const CELL_BYTES: u64 = 64;

/// What one own property added to an object stands for in the byte count:
/// its value slot and its share of the shape table (an estimate).
pub const PROPERTY_BYTES: u64 = 32;

/// The room past the byte limit that only [`Heap::set_reserve_open`] opens: the
/// `RangeError` that reports the limit must itself be allocated. Each report
/// takes a few hundred bytes of it, so a script that catches the error and
/// allocates again for ever uses the reserve up after some hundreds of
/// catches, and then ends in `OutOfMemory`, which it cannot catch.
pub const RESERVE_BYTES: u64 = 64 * 1024;

/// The heap: the arena of cells, the shape table and the key interner.
///
/// # The byte limit (phase-7.md 7.19)
///
/// Besides the arena's cell limit, the heap counts bytes: [`CELL_BYTES`] for
/// every cell, a string's code units (one byte each for a Latin-1 string, two
/// otherwise), eight bytes for every slot an object or environment is made
/// with, and [`PROPERTY_BYTES`] for every property added later. An
/// allocation that would pass [`Heap::set_byte_limit`] is
/// [`HeapError::Full`], which the interpreter reports as a `RangeError`. The
/// count is an estimate of the memory, not a measurement: the shape table
/// and the interned keys are counted only through [`PROPERTY_BYTES`], and the
/// `Vec`s' spare capacity not at all. Nothing is freed (the VM does not use
/// the collector of item 7.6 yet), so the count only grows.
#[derive(Debug)]
pub struct Heap {
    arena: Arena<Cell>,
    shapes: Shapes,
    keys: Interner,
    /// The interned `length`, which an array keeps in slot 0.
    length_key: Key,
    /// The bytes counted so far (see the type's docs).
    bytes: u64,
    /// The byte limit, `u64::MAX` for none.
    byte_limit: u64,
    /// Whether [`RESERVE_BYTES`] past the limit may be used now.
    reserve_open: bool,
}

/// The bytes a new cell counts for.
fn cell_bytes(cell: &Cell) -> u64 {
    let payload = match cell {
        Cell::Str(s) => {
            let len = u64::try_from(s.len()).unwrap_or(u64::MAX);
            if s.is_latin1() {
                len
            } else {
                len.saturating_mul(2)
            }
        }
        Cell::Object(o) => u64::try_from(o.slots.len())
            .unwrap_or(u64::MAX)
            .saturating_mul(8),
        Cell::Env(e) => u64::try_from(e.slots.len())
            .unwrap_or(u64::MAX)
            .saturating_mul(8),
        // A Symbol's description is a string cell of its own, counted there;
        // an iterator record holds a few values and no growing buffer.
        Cell::Symbol(_) | Cell::Iter(_) | Cell::Accessor { .. } | Cell::LazyAccessor(_) => 0,
    };
    CELL_BYTES.saturating_add(payload)
}

impl Heap {
    /// An empty heap whose arena holds at most `limit` cells.
    #[must_use]
    pub fn new(limit: usize) -> Self {
        let mut keys = Interner::new();
        // "length" is 6 code units: it fits the string limit, so the
        // interner cannot refuse it; the fallback key is never used.
        let length_key = JsString::from_rust_str("length")
            .ok()
            .and_then(|s| keys.intern(&s).ok())
            .unwrap_or(Key(0));
        Self {
            arena: Arena::with_limit(limit),
            shapes: Shapes::new(),
            keys,
            length_key,
            bytes: 0,
            byte_limit: u64::MAX,
            reserve_open: false,
        }
    }

    /// The number of live cells.
    #[must_use]
    pub fn live(&self) -> usize {
        self.arena.live()
    }

    /// The bytes counted so far (see the type's docs).
    #[must_use]
    pub fn bytes(&self) -> u64 {
        self.bytes
    }

    /// The byte limit.
    #[must_use]
    pub fn byte_limit(&self) -> u64 {
        self.byte_limit
    }

    /// Sets the byte limit. Bytes already counted stay counted: a limit below
    /// them makes every later allocation [`HeapError::Full`].
    pub fn set_byte_limit(&mut self, limit: u64) {
        self.byte_limit = limit;
    }

    /// Opens or closes the [`RESERVE_BYTES`] past the limit, for the error
    /// object that reports the limit, and returns whether it was open.
    pub fn set_reserve_open(&mut self, open: bool) -> bool {
        core::mem::replace(&mut self.reserve_open, open)
    }

    /// Counts `n` more bytes, or refuses if that passes the limit.
    fn charge(&mut self, n: u64) -> Result<(), HeapError> {
        let limit = if self.reserve_open {
            self.byte_limit.saturating_add(RESERVE_BYTES)
        } else {
            self.byte_limit
        };
        let next = self.bytes.checked_add(n).ok_or(HeapError::Full)?;
        if next > limit {
            return Err(HeapError::Full);
        }
        self.bytes = next;
        Ok(())
    }

    /// Allocates a cell and returns the reference to it as a value.
    ///
    /// # Errors
    /// [`HeapError::Full`] if the arena is full or the byte limit would be
    /// passed.
    pub fn alloc(&mut self, cell: Cell) -> Result<Value, HeapError> {
        let n = cell_bytes(&cell);
        self.charge(n)?;
        match self.arena.alloc(cell) {
            Ok(r) => Ok(Value::heap_ref(r)),
            Err(e) => {
                self.bytes = self.bytes.saturating_sub(n);
                Err(e.into())
            }
        }
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

    /// Allocates the getter and setter pair of an accessor property.
    ///
    /// # Errors
    /// [`HeapError::Full`] if the arena is full.
    pub fn new_accessor(&mut self, get: Value, set: Value) -> Result<Value, HeapError> {
        self.alloc(Cell::Accessor { get, set })
    }

    /// The getter and setter an accessor pair holds: `None` for a pair
    /// that is still lazy (`Vm::accessor_pair` makes its functions first).
    #[must_use]
    pub fn accessor(&self, v: Value) -> Option<(Value, Value)> {
        match self.cell(v)? {
            Cell::Accessor { get, set } => Some((*get, *set)),
            _ => None,
        }
    }

    /// Allocates an accessor pair whose functions the embedder makes when
    /// they are first needed; `id` is the embedder's number for them.
    ///
    /// # Errors
    /// [`HeapError::Full`] if the arena is full.
    pub fn new_lazy_accessor(&mut self, id: u32) -> Result<Value, HeapError> {
        self.alloc(Cell::LazyAccessor(id))
    }

    /// The embedder's number of a lazy accessor pair, if `v` is one.
    #[must_use]
    pub fn lazy_accessor(&self, v: Value) -> Option<u32> {
        match self.cell(v)? {
            Cell::LazyAccessor(id) => Some(*id),
            _ => None,
        }
    }

    /// Turns the lazy accessor pair `v` into the pair of `get` and `set`,
    /// in place.
    ///
    /// # Errors
    /// [`HeapError::Corrupt`] if `v` is not a lazy accessor pair.
    pub fn fill_lazy_accessor(
        &mut self,
        v: Value,
        get: Value,
        set: Value,
    ) -> Result<(), HeapError> {
        match self.cell_mut(v) {
            Some(cell @ Cell::LazyAccessor(_)) => {
                *cell = Cell::Accessor { get, set };
                Ok(())
            }
            _ => Err(HeapError::Corrupt),
        }
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
            extensible: true,
        }))
    }

    /// Allocates an Array exotic object whose `length` is `len`: the
    /// property is writable, not enumerable, not configurable
    /// (§10.4.2.2† ArrayCreate steps 6 to 8). `len` must already be checked
    /// against 2^32 - 1.
    ///
    /// # Errors
    /// [`HeapError::Full`] if the arena is full.
    pub fn new_array(&mut self, proto: Value, len: u32) -> Result<Value, HeapError> {
        let a = self.new_object(proto, ObjKind::Array)?;
        let k = self.length_key;
        self.define(a, k, length_value(len), Attrs(Attrs::WRITABLE))?;
        Ok(a)
    }

    /// The `length` of an Array exotic object, with whether it is writable.
    #[must_use]
    pub fn array_length(&self, arr: Value) -> Option<(u32, bool)> {
        let o = self.obj(arr)?;
        if !matches!(o.kind, ObjKind::Array) {
            return None;
        }
        let (slot, attrs) = self.shapes.lookup(o.shape, self.length_key)?;
        let v = o.slots.get(usize::try_from(slot).ok()?).copied()?;
        let d = crate::numeric::num(v)?.to_f64();
        let n = d as u32;
        (f64::from(n) == d).then_some((n, attrs.0 & Attrs::WRITABLE != 0))
    }

    /// Stores `len` as the `length` of an array (the caller has checked that
    /// the property is writable, or is applying a definition).
    ///
    /// # Errors
    /// [`HeapError::Corrupt`] if `arr` is not an array.
    pub fn set_array_length(&mut self, arr: Value, len: u32) -> Result<(), HeapError> {
        let o = self.obj(arr).ok_or(HeapError::Corrupt)?;
        let (slot, _) = self
            .shapes
            .lookup(o.shape, self.length_key)
            .ok_or(HeapError::Corrupt)?;
        self.set_slot(arr, slot, length_value(len))
    }

    /// Whether a value is an Array exotic object.
    #[must_use]
    pub fn is_array_object(&self, v: Value) -> bool {
        self.obj(v)
            .is_some_and(|o| matches!(o.kind, ObjKind::Array))
    }

    /// The array index a key names (§6.1.7†), if it names one.
    #[must_use]
    pub fn key_index(&self, k: Key) -> Option<u32> {
        self.key_string(k).and_then(canonical_index)
    }

    /// Removes the own properties `keys` of `obj` (a key it does not have is
    /// ignored): the shape is rebuilt from the root without them, so the
    /// others keep their order and get consecutive slots. A shared shape
    /// reuses its transitions; a dictionary shape (an object with more than
    /// 128 properties) gets a new dictionary shape each time, which stays in
    /// the shape table until the collector of #236 frees it.
    ///
    /// # Errors
    /// [`HeapError::Corrupt`] if `obj` is not an object, [`HeapError::Full`]
    /// on overflow.
    pub fn remove_properties(&mut self, obj: Value, keys: &[Key]) -> Result<(), HeapError> {
        let o = self.obj(obj).ok_or(HeapError::Corrupt)?;
        let props = self.shapes.properties(o.shape);
        if !props.iter().any(|(k, _, _)| keys.contains(k)) {
            return Ok(());
        }
        let old_slots = o.slots.clone();
        let mut shape = ROOT;
        let mut slots: Vec<Value> = Vec::with_capacity(props.len());
        for (k, slot, a) in props {
            if keys.contains(&k) {
                continue;
            }
            let v = usize::try_from(slot)
                .ok()
                .and_then(|i| old_slots.get(i))
                .copied()
                .ok_or(HeapError::Corrupt)?;
            let (next, new_slot) = self.shapes.add_property(shape, k, a)?;
            if usize::try_from(new_slot).ok() != Some(slots.len()) {
                return Err(HeapError::Corrupt);
            }
            shape = next;
            slots.push(v);
        }
        let o = self.obj_mut(obj).ok_or(HeapError::Corrupt)?;
        o.shape = shape;
        o.slots = slots;
        Ok(())
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

    /// The Symbol a value refers to, if it refers to one.
    #[must_use]
    pub fn symbol(&self, v: Value) -> Option<Sym> {
        match self.cell(v)? {
            Cell::Symbol(s) => Some(*s),
            _ => None,
        }
    }

    /// Whether a value is a Symbol.
    #[must_use]
    pub fn is_symbol(&self, v: Value) -> bool {
        self.symbol(v).is_some()
    }

    /// The iterator record a value refers to, mutably.
    pub fn iter_record_mut(&mut self, v: Value) -> Option<&mut IterRecord> {
        match self.cell_mut(v)? {
            Cell::Iter(r) => Some(r),
            _ => None,
        }
    }

    /// The iterator record a value refers to.
    #[must_use]
    pub fn iter_record(&self, v: Value) -> Option<&IterRecord> {
        match self.cell(v)? {
            Cell::Iter(r) => Some(r),
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

    /// The string a key stands for (`None` for a Symbol's key).
    #[must_use]
    pub fn key_string(&self, k: Key) -> Option<&JsString> {
        match decode(k) {
            PropertyKey::String(_) => self.keys.resolve(k),
            PropertyKey::Symbol(_) => None,
        }
    }

    /// The property key of Symbol `id` (`clazel-js-heap`'s Y4 encoding), or
    /// `None` past the encoding's 2^31 symbols.
    #[must_use]
    pub fn symbol_key(id: SymbolId) -> Option<Key> {
        encode(PropertyKey::Symbol(id))
    }

    /// The Symbol id a key stands for, if it is a Symbol's key.
    #[must_use]
    pub fn key_symbol(k: Key) -> Option<SymbolId> {
        match decode(k) {
            PropertyKey::Symbol(id) => Some(id),
            PropertyKey::String(_) => None,
        }
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
        self.charge(PROPERTY_BYTES)?;
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

    /// The own properties of an object whose keys are Strings, in the order
    /// `[[OwnPropertyKeys]]` gives them (§10.1.11.1† steps 2 and 3): the
    /// array indices in ascending order, then the other string keys in the
    /// order they were created. The Symbol-keyed ones (step 4) are
    /// [`Heap::own_symbol_properties`].
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
            if Self::key_symbol(k).is_some() {
                continue;
            }
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

    /// The own Symbol-keyed properties of an object, in the order they were
    /// created (§10.1.11.1† step 4).
    #[must_use]
    pub fn own_symbol_properties(&self, obj: Value) -> Vec<(Key, Attrs, Value)> {
        let Some(o) = self.obj(obj) else {
            return Vec::new();
        };
        self.shapes
            .properties(o.shape)
            .into_iter()
            .filter(|(k, _, _)| Self::key_symbol(*k).is_some())
            .filter_map(|(k, slot, a)| {
                let v = usize::try_from(slot)
                    .ok()
                    .and_then(|i| o.slots.get(i))
                    .copied()?;
                Some((k, a, v))
            })
            .collect()
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

    /// `[[Extensible]]` of an object (true for a non-object).
    #[must_use]
    pub fn is_extensible(&self, obj: Value) -> bool {
        self.obj(obj).is_none_or(|o| o.extensible)
    }

    /// The `[[Prototype]]` of an object.
    #[must_use]
    pub fn proto_of(&self, obj: Value) -> Option<Value> {
        self.obj(obj).map(|o| o.proto)
    }
}

/// A `length` value: an int32 when it fits, else a double.
#[must_use]
pub fn length_value(len: u32) -> Value {
    match i32::try_from(len) {
        Ok(i) => Value::int32(i),
        Err(_) => Value::double(f64::from(len)),
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
