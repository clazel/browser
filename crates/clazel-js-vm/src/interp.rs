//! The units.extend(key_text.units());nterpreter loop (phase-7.md item 7.8, first slice).
//!
//! [`Vm`] owns the frame region ([`crate::frame`]), the heap
//! ([`crate::heap`]) and the loaded code. [`Vm::run`] and [`Vm::call`] push a
//! frame and run the loop: it fetches an [`Instr`], runs it, and counts
//! function entries and loop back-edges for jit.md's tiering (J.10); neither
//! count is observable by JS, as `spec::step`'s state shows. Core ops and the
//! fast paths of guarded ops are in [`Vm::step`]; every other case calls a
//! handler of [`crate::handlers`], a plain method over the frame region and
//! the heap, which jit.md's exits will share.
//!
//! # What refines what
//!
//! `spec fn step` is the semantics: for each op, [`Vm::step`] computes
//! `fast_step` when the op is core or its `fast_path` holds, and the handler
//! (uninterpreted there) otherwise. The differential test
//! (`tests/differential.rs`) compares the two for straight-line programs, and
//! it is a test, not a proof: nothing ties this code to the spec.
//!
//! # Differences from the spec's `step`, all listed
//!
//! - **A call passes at most `nparams` arguments to the frame.** The header
//!   keeps the real argument count (`GetArgc`), but an argument past the
//!   parameters has no slot: `spec::pushed_region` copies only `argc <=
//!   nparams`, and the `arguments` object (`CreateUnmappedArguments`) is not
//!   implemented, so nothing can read it yet.
//! - **Constants.** A Number constant is loaded as an int32 when it is an
//!   integer in range other than `-0`, else as a double; the spec leaves the
//!   pool's encoding to the loader (`Code::consts`).
//! - **A step budget.** [`Vm::set_budget`] bounds the back-edges and calls a
//!   run may make, and ends the run as [`Abrupt::Terminated`] when it is
//!   spent: a host's deterministic form of the `Terminator`.
//! - **Limits (phase-7.md 7.19).** The heap's byte limit
//!   ([`Vm::set_heap_limit`]) and the region's slot limit make an op throw a
//!   `RangeError` where the spec has no limit, and so does one native call
//!   more than [`Vm::set_native_depth_limit`] allows. The heap-limit error
//!   comes without a collection first: the VM does not use the collector of
//!   item 7.6 yet.
//! - **No inline-cache entries for globals or prototype hits**, only own data
//!   properties of non-dictionary shapes, as `spec::IcEntry` models.
//!
//! # Unwinding
//!
//! A throw looks in the current function's exception table at the `pc` of
//! the op that threw; if no entry covers it, the frame is popped through its
//! return address and the search continues at the caller's call op, until a
//! frame whose return address is [`crate::frame::RET_NONE`] (the entry of
//! [`Vm::call`]) is left, which makes the throw the result of that call.

use crate::bytecode::{Const, FunctionCode, FunctionKind, Instr, Program, check_program};
use crate::frame::{
    FrameError, HDR_ARGC, HDR_CALLEE, HDR_RET, KIND_CONSTRUCT, KIND_PLAIN, RET_NONE, Region, Ret,
    enc_argc, frame_size, pack_ret, unpack_ret,
};
use crate::heap::{Heap, HeapError, ObjKind};
use crate::numeric::{self, Num, num};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::{JsString, Key};
use clazel_js_heap::symbol::SymbolId;
use clazel_js_heap::symbol::contract::WELL_KNOWN;
use clazel_js_heap::value::Value;
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

/// The shared termination flag (phase-7.md, "Limits and stopping"). A host
/// sets it from another thread; the loop reads it at every back-edge and call
/// and ends the run with [`Abrupt::Terminated`], which JS cannot catch. The
/// embedding API (`clazel-js`, an open pull request) will wrap this.
#[derive(Clone, Debug, Default)]
pub struct Terminator(Arc<AtomicBool>);

impl Terminator {
    /// A flag that is clear.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Asks the engine to stop.
    pub fn terminate(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    /// Clears the flag.
    pub fn reset(&self) {
        self.0.store(false, Ordering::Relaxed);
    }

    /// Whether the flag is set.
    #[must_use]
    pub fn is_set(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }
}

/// How a run ended other than by returning a value.
#[derive(Clone, Debug, PartialEq)]
pub enum Abrupt {
    /// A JS exception: the thrown value. Catchable by JS.
    Throw(Value),
    /// A construct this slice does not implement, named. Not catchable.
    NotYet(String),
    /// The [`Terminator`] was set, or the step budget ran out. Not catchable.
    Terminated,
    /// The heap's arena is full or a string is too long. Not catchable.
    OutOfMemory,
    /// An invariant of the VM does not hold (an unchecked program, a stale
    /// reference). Unreachable by construction; reported, not a panic.
    Internal(&'static str),
}

impl From<FrameError> for Abrupt {
    fn from(_: FrameError) -> Self {
        Abrupt::Internal("frame index out of the region")
    }
}

impl From<HeapError> for Abrupt {
    fn from(e: HeapError) -> Self {
        match e {
            HeapError::Corrupt => Abrupt::Internal("heap invariant"),
            _ => Abrupt::OutOfMemory,
        }
    }
}

/// A native function: `this`, the arguments, the result. While it runs,
/// [`Vm::active_function`] is its own function object and [`Vm::new_target`]
/// is `undefined` for a call and the constructor for a `new`.
pub type NativeFn = fn(&mut Vm, Value, &[Value]) -> Result<Value, Abrupt>;

/// Makes the `[[Get]]` and `[[Set]]` of a lazy accessor pair from the
/// embedder's number for it (`Vm::set_lazy_accessor_maker`).
pub type LazyAccessorMaker = fn(&mut Vm, u32) -> Result<(Value, Value), Abrupt>;

/// The objects a realm's built-ins share (§6.1.7.4† "Well-Known Intrinsic
/// Objects"). [`Vm::new`] makes the first two; `clazel-js-builtins` installs
/// the others with [`Vm::set_intrinsic`]. The VM reads them where the
/// standard names an intrinsic: the prototype of a thrown error, of a
/// wrapper object, of a primitive's property lookup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    /// `%Object.prototype%`.
    ObjectPrototype,
    /// `%Function.prototype%`.
    FunctionPrototype,
    /// `%Error.prototype%`.
    ErrorPrototype,
    /// `%TypeError.prototype%`.
    TypeErrorPrototype,
    /// `%RangeError.prototype%`.
    RangeErrorPrototype,
    /// `%SyntaxError.prototype%`.
    SyntaxErrorPrototype,
    /// `%ReferenceError.prototype%`.
    ReferenceErrorPrototype,
    /// `%Boolean.prototype%`.
    BooleanPrototype,
    /// `%Number.prototype%`.
    NumberPrototype,
    /// `%String.prototype%`.
    StringPrototype,
    /// `%Array.prototype%`.
    ArrayPrototype,
    /// `%Array%`.
    ArrayConstructor,
    /// `%Symbol.prototype%`.
    SymbolPrototype,
    /// `%Iterator.prototype%` (§27.1.2†).
    IteratorPrototype,
    /// `%ArrayIteratorPrototype%` (§23.1.5.2†).
    ArrayIteratorPrototype,
    /// `%StringIteratorPrototype%` (§22.1.5.1†).
    StringIteratorPrototype,
    /// Not an intrinsic of the standard: the GlobalSymbolRegistry List
    /// (§20.4.2.2.1†) of `Symbol.for`, kept as an object without a
    /// prototype that no script can reach (its keys are the registered
    /// strings, its values the Symbols).
    SymbolRegistry,
    /// `%Promise.prototype%` (§27.2.5†).
    PromisePrototype,
    /// `%Promise%` (§27.2.3†).
    PromiseConstructor,
    /// The built-in function of PromiseReactionJob (§27.2.2.1†): the callee
    /// of the job HostEnqueuePromiseJob queues for a reaction.
    PromiseReactionJob,
    /// The built-in function of PromiseResolveThenableJob (§27.2.2.2†).
    PromiseResolveThenableJob,
    /// `%RegExp.prototype%` (§22.2.6†).
    RegExpPrototype,
    /// `%RegExp%` (§22.2.4†): the constructor a regular expression literal
    /// runs (`NewRegExp`, RegExpCreate §22.2.3.1†).
    RegExpConstructor,
    /// `%RegExpStringIteratorPrototype%` (§22.2.9.1†).
    RegExpStringIteratorPrototype,
    /// `%AggregateError.prototype%` (§20.5.7†).
    AggregateErrorPrototype,
    /// `%Map.prototype%` (§24.1.3†).
    MapPrototype,
    /// `%MapIteratorPrototype%` (§24.1.5.2†).
    MapIteratorPrototype,
    /// `%Set.prototype%` (§24.2.4†).
    SetPrototype,
    /// `%SetIteratorPrototype%` (§24.2.6.2†).
    SetIteratorPrototype,
    /// `%WeakMap.prototype%` (§24.3.3†).
    WeakMapPrototype,
    /// `%WeakSet.prototype%` (§24.4.3†).
    WeakSetPrototype,
}

/// The most natives that may run one inside another, until
/// [`Vm::set_native_depth_limit`] says otherwise (and one more nested run of
/// the interpreter loop, see [`Vm::execute`]).
///
/// Both live on the host stack. Measured on aarch64 macOS (2026-11), one
/// level of JS calling a native that calls JS back (`forEach`, `map`,
/// `call`) takes about 40 KB of it in an unoptimised build and about 1.5 KB
/// in an optimised one. 32 levels is about 1.3 MB unoptimised, which a
/// 2 MiB thread (Rust's default, and what tests run on) holds with room for
/// its caller. An embedder on a larger stack may raise it.
pub const DEFAULT_NATIVE_DEPTH: u32 = 32;

/// The deepest nesting the VM's own recursive algorithms (`JSON.parse`,
/// `JSON.stringify`) take, until [`Vm::set_nesting_depth_limit`] says
/// otherwise: `clazel-json`'s own bound, so the default changes nothing.
pub const DEFAULT_NESTING_DEPTH: u32 = 512;

/// The RegExp backtrack stack's size in entries, until
/// [`Vm::set_regexp_backtrack_limit`] says otherwise (`clazel-js-regexp`'s own
/// default).
pub const DEFAULT_REGEXP_BACKTRACK: u64 = 1 << 20;

/// How many [`Intrinsic`]s there are.
const INTRINSICS: usize = 31;

/// The hint of ToPrimitive (§7.1.1†).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hint {
    /// `default`.
    Default,
    /// `number`.
    Number,
    /// `string`.
    String,
}

/// The state of a bound function exotic object (§10.4.1†):
/// `[[BoundTargetFunction]]`, `[[BoundThis]]`, `[[BoundArguments]]`.
#[derive(Clone, Debug)]
pub(crate) struct BoundFn {
    pub(crate) target: Value,
    pub(crate) this: Value,
    pub(crate) args: Vec<Value>,
}

/// A constant of a loaded function.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ConstVal {
    /// A value of the pool.
    Value(Value),
    /// A declaration record or other table the handler reads from the code.
    Record,
    /// A constant this slice cannot load.
    Unsupported(&'static str),
}

/// An inline-cache entry (`spec::IcEntry`): shape id 0 never hits.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct IcEntry {
    pub(crate) shape: u32,
    pub(crate) slot: u32,
}

/// A function, loaded into a VM.
#[derive(Debug)]
pub(crate) struct LoadedFn {
    pub(crate) code: FunctionCode,
    pub(crate) consts: Vec<ConstVal>,
    pub(crate) keys: Vec<Option<Key>>,
    /// The index in the VM's table of the first function of this function's
    /// program: `NewClosure::func` and the declarations are relative to it.
    pub(crate) base: u32,
    pub(crate) ics: Vec<IcEntry>,
    pub(crate) entries: u64,
    pub(crate) back_edges: u64,
    pub(crate) name_value: Option<Value>,
    /// Whether the function reads the arguments past its parameters
    /// (`arguments` or a rest parameter): a call then keeps its argument list
    /// for the op that makes the object (`crate::host`, "Arguments").
    pub(crate) needs_args: bool,
}

/// A script loaded into a VM.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Script {
    /// The index of the script's own function in the VM's code table.
    pub main: u32,
}

/// What the loop does after an op.
pub(crate) enum Flow {
    Continue,
    Done(Value),
}

/// The prototypes and strings the VM makes at the start.
#[derive(Debug)]
pub(crate) struct Atoms {
    pub(crate) object_proto: Value,
    pub(crate) function_proto: Value,
    pub(crate) undefined: Value,
    pub(crate) object: Value,
    pub(crate) boolean: Value,
    pub(crate) number: Value,
    pub(crate) string: Value,
    pub(crate) function: Value,
    pub(crate) symbol: Value,
    pub(crate) k_length: Key,
    pub(crate) k_name: Key,
    pub(crate) k_message: Key,
    pub(crate) k_prototype: Key,
    pub(crate) k_constructor: Key,
    pub(crate) k_next: Key,
    pub(crate) k_done: Key,
    pub(crate) k_value: Key,
    pub(crate) k_return: Key,
}

/// Limits of a [`Vm`].
#[derive(Clone, Copy, Debug)]
pub struct Config {
    /// The frame region's slot limit: the depth of JS calls.
    pub region_slots: usize,
    /// The arena's cell limit.
    pub heap_cells: usize,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            region_slots: 1 << 18,
            heap_cells: 1 << 24,
        }
    }
}

/// The virtual machine: region, heap, code, and the running frame.
#[derive(Debug)]
pub struct Vm {
    pub(crate) heap: Heap,
    pub(crate) region: Region,
    pub(crate) codes: Vec<LoadedFn>,
    pub(crate) fp: usize,
    pub(crate) pc: usize,
    pub(crate) cur: usize,
    /// The first slot after the running frame.
    pub(crate) top: usize,
    pub(crate) exception: Value,
    pub(crate) global: Value,
    /// The global declarative record: name, value (the hole until
    /// initialized), and whether it is a constant.
    pub(crate) global_lex: HashMap<Key, (Value, bool)>,
    /// The `VarNames` of the global environment record.
    pub(crate) var_names: HashSet<Key>,
    /// The native functions, and whether each has `[[Construct]]`.
    pub(crate) natives: Vec<(NativeFn, bool)>,
    pub(crate) bound: Vec<BoundFn>,
    /// The Symbol values, by id: the cell of each (the well-known symbols
    /// are ids 0 to 12).
    pub(crate) symbols: Vec<Value>,
    pub(crate) intrinsics: [Value; INTRINSICS],
    pub(crate) new_target: Value,
    pub(crate) active: Value,
    /// How many natives are running, one inside another (each re-enters the
    /// interpreter or another native on the host stack).
    pub(crate) native_depth: u32,
    /// How many runs of the interpreter loop are on the host stack (see
    /// [`Vm::execute`]).
    pub(crate) reentry_depth: u32,
    pub(crate) terminator: Terminator,
    pub(crate) budget: u64,
    /// The limits of phase-7.md 7.19 that the VM checks itself (see the
    /// setters).
    pub(crate) native_limit: u32,
    pub(crate) nesting_limit: u32,
    pub(crate) regexp_backtrack_limit: u64,
    pub(crate) atoms: Atoms,
    /// The embedder's state (`clazel-js`'s runtime), see [`Vm::set_embedder`].
    pub(crate) embedder: Option<Box<dyn Any + Send>>,
    /// Makes the functions of a lazy accessor pair, see
    /// [`Vm::set_lazy_accessor_maker`].
    pub(crate) lazy_accessor_maker: Option<LazyAccessorMaker>,
    /// Host objects, the slots of native functions and the job queue
    /// ([`crate::host`]).
    pub(crate) host: crate::host::HostState,
}

impl Vm {
    /// A VM with an empty global object.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`] if `config.heap_cells` is too small for the
    /// VM's own first cells.
    pub fn new(config: Config) -> Result<Self, Abrupt> {
        let mut heap = Heap::new(config.heap_cells);
        let object_proto = heap.new_object(Value::NULL, ObjKind::Plain)?;
        let function_proto = heap.new_object(object_proto, ObjKind::Plain)?;
        let global = heap.new_object(object_proto, ObjKind::Plain)?;
        let atoms = Atoms {
            object_proto,
            function_proto,
            undefined: heap.new_str("undefined")?,
            object: heap.new_str("object")?,
            boolean: heap.new_str("boolean")?,
            number: heap.new_str("number")?,
            string: heap.new_str("string")?,
            function: heap.new_str("function")?,
            symbol: heap.new_str("symbol")?,
            k_length: heap.intern_str("length")?,
            k_name: heap.intern_str("name")?,
            k_message: heap.intern_str("message")?,
            k_prototype: heap.intern_str("prototype")?,
            k_constructor: heap.intern_str("constructor")?,
            k_next: heap.intern_str("next")?,
            k_done: heap.intern_str("done")?,
            k_value: heap.intern_str("value")?,
            k_return: heap.intern_str("return")?,
        };
        // The well-known symbols (§6.1.5.1†, Table 1), ids 0 to 12 as
        // `clazel-js-heap`'s symbol contract numbers them (Y1); each
        // `[[Description]]` is "Symbol." and the name.
        let mut symbols = Vec::with_capacity(WELL_KNOWN.len());
        for (id, name) in (0u32..).zip(WELL_KNOWN) {
            let description = heap.new_str(&format!("Symbol.{name}"))?;
            symbols.push(heap.alloc(crate::heap::Cell::Symbol(crate::heap::Sym {
                id: SymbolId(id),
                description,
            }))?);
        }
        // §19.1 Value Properties of the Global Object: `undefined`, `NaN` and
        // `Infinity` are not writable, enumerable or configurable.
        for (name, v) in [
            ("undefined", Value::UNDEFINED),
            ("NaN", Value::double(f64::NAN)),
            ("Infinity", Value::double(f64::INFINITY)),
        ] {
            let k = heap.intern_str(name)?;
            heap.define(global, k, v, Attrs(0))?;
        }
        Ok(Self {
            heap,
            region: Region::new(config.region_slots),
            codes: Vec::new(),
            fp: 0,
            pc: 0,
            cur: 0,
            top: 0,
            exception: Value::UNDEFINED,
            global,
            global_lex: HashMap::new(),
            var_names: HashSet::new(),
            natives: Vec::new(),
            bound: Vec::new(),
            symbols,
            intrinsics: std::array::from_fn(|i| {
                if i == Intrinsic::ObjectPrototype as usize {
                    object_proto
                } else if i == Intrinsic::FunctionPrototype as usize {
                    function_proto
                } else {
                    Value::UNDEFINED
                }
            }),
            new_target: Value::UNDEFINED,
            active: Value::UNDEFINED,
            native_depth: 0,
            reentry_depth: 0,
            terminator: Terminator::new(),
            budget: u64::MAX,
            native_limit: DEFAULT_NATIVE_DEPTH,
            nesting_limit: DEFAULT_NESTING_DEPTH,
            regexp_backtrack_limit: DEFAULT_REGEXP_BACKTRACK,
            atoms,
            embedder: None,
            lazy_accessor_maker: None,
            host: crate::host::HostState::default(),
        })
    }

    /// The termination flag of this VM; setting it from another thread ends
    /// the run at its next back-edge or call.
    #[must_use]
    pub fn terminator(&self) -> Terminator {
        self.terminator.clone()
    }

    /// Stores the embedder's own state in the VM, replacing what was there.
    ///
    /// A [`NativeFn`] is a plain function pointer that gets only `&mut Vm`, so
    /// an embedder whose natives are closures (`clazel-js`) keeps the table of
    /// closures here and finds it again from inside the native. The VM never
    /// looks at it. Dropping the VM drops it.
    pub fn set_embedder<T: Any + Send>(&mut self, data: T) {
        self.embedder = Some(Box::new(data));
    }

    /// The embedder's state, if it is a `T`.
    #[must_use]
    pub fn embedder<T: Any>(&self) -> Option<&T> {
        self.embedder.as_deref().and_then(|e| e.downcast_ref::<T>())
    }

    /// The embedder's state, mutably, if it is a `T`.
    pub fn embedder_mut<T: Any>(&mut self) -> Option<&mut T> {
        self.embedder
            .as_deref_mut()
            .and_then(|e| e.downcast_mut::<T>())
    }

    /// Bounds the back-edges and calls the VM may still make; when spent, a
    /// run ends as [`Abrupt::Terminated`].
    pub fn set_budget(&mut self, steps: u64) {
        self.budget = steps;
    }

    // -----------------------------------------------------------------
    // Limits (phase-7.md 7.19). Each is the embedder's; the defaults are
    // the constants above.
    // -----------------------------------------------------------------

    /// Sets the heap's byte limit ([`crate::heap::Heap`]'s byte count). An
    /// allocation past it is a `RangeError`, made from a small reserve past
    /// the limit (see [`Vm::execute`]); bytes already counted stay counted.
    pub fn set_heap_limit(&mut self, bytes: u64) {
        self.heap.set_byte_limit(bytes);
    }

    /// Sets how many natives may run one inside another; one more is a
    /// `RangeError`. The host stack must hold that many re-entries of the
    /// interpreter: see [`DEFAULT_NATIVE_DEPTH`].
    pub fn set_native_depth_limit(&mut self, depth: u32) {
        self.native_limit = depth;
    }

    /// The nesting limit of the VM's recursive built-ins.
    #[must_use]
    pub fn nesting_depth_limit(&self) -> u32 {
        self.nesting_limit
    }

    /// Sets the nesting limit of the VM's recursive built-ins (`JSON.parse`,
    /// `JSON.stringify`); each also has a fixed bound of its own, and the
    /// smaller applies.
    pub fn set_nesting_depth_limit(&mut self, depth: u32) {
        self.nesting_limit = depth;
    }

    /// The RegExp backtrack stack's size in entries, for the RegExp
    /// built-ins.
    #[must_use]
    pub fn regexp_backtrack_limit(&self) -> u64 {
        self.regexp_backtrack_limit
    }

    /// Sets the RegExp backtrack stack's size in entries.
    pub fn set_regexp_backtrack_limit(&mut self, entries: u64) {
        self.regexp_backtrack_limit = entries;
    }

    /// The termination check for a native in a long loop of its own (one
    /// that calls no function, so the interpreter's checks at calls and
    /// back-edges do not see it).
    ///
    /// # Errors
    /// [`Abrupt::Terminated`] once the [`Terminator`] is set.
    pub fn check_terminated(&self) -> Result<(), Abrupt> {
        if self.terminator.is_set() {
            return Err(Abrupt::Terminated);
        }
        Ok(())
    }

    /// The `RangeError` that reports the heap limit, made from the reserve
    /// past it; [`Abrupt::OutOfMemory`] when even the reserve is spent.
    ///
    /// phase-7.md 7.19 asks for a full collection before the error. The VM
    /// does not use the collector of item 7.6 yet, so there is nothing to
    /// collect: the error comes at once.
    pub(crate) fn heap_limit_error(&mut self) -> Abrupt {
        let was = self.heap.set_reserve_open(true);
        let e = self.range_error("Out of memory: the heap limit was reached");
        self.heap.set_reserve_open(was);
        match e {
            Abrupt::Throw(v) => Abrupt::Throw(v),
            _ => Abrupt::OutOfMemory,
        }
    }

    /// `r`, with [`Abrupt::OutOfMemory`] turned into the `RangeError` that
    /// reports the heap limit ([`Vm::heap_limit_error`]).
    pub(crate) fn report_heap_limit<T>(&mut self, r: Result<T, Abrupt>) -> Result<T, Abrupt> {
        match r {
            Err(Abrupt::OutOfMemory) => Err(self.heap_limit_error()),
            other => other,
        }
    }

    /// The global object.
    #[must_use]
    pub fn global(&self) -> Value {
        self.global
    }

    /// The heap, for reading results.
    #[must_use]
    pub fn heap(&self) -> &Heap {
        &self.heap
    }

    /// A slot of the frame region, as the JIT reads it (`spec::State::region`).
    #[must_use]
    pub fn region_slot(&self, i: usize) -> Option<Value> {
        self.region.get(i).ok()
    }

    /// How many times function `code` was entered (jit.md J.10's counter).
    #[must_use]
    pub fn entries(&self, code: u32) -> Option<u64> {
        let i = usize::try_from(code).ok()?;
        self.codes.get(i).map(|f| f.entries)
    }

    /// How many back-edges function `code` took.
    #[must_use]
    pub fn back_edges(&self, code: u32) -> Option<u64> {
        let i = usize::try_from(code).ok()?;
        self.codes.get(i).map(|f| f.back_edges)
    }

    // -----------------------------------------------------------------
    // Loading
    // -----------------------------------------------------------------

    /// Loads a compiled script: checks it ([`check_program`]) and its
    /// constant pools become heap values.
    ///
    /// # Errors
    /// [`Abrupt::Internal`] if the program is ill-formed,
    /// [`Abrupt::OutOfMemory`] if the heap is full.
    pub fn load(&mut self, program: &Program) -> Result<Script, Abrupt> {
        check_program(program).map_err(Abrupt::Internal)?;
        let base = u32::try_from(self.codes.len()).map_err(|_| Abrupt::OutOfMemory)?;
        let main = base.checked_add(program.main).ok_or(Abrupt::OutOfMemory)?;
        for f in &program.functions {
            let loaded = self.load_function(f, base)?;
            self.codes.push(loaded);
        }
        Ok(Script { main })
    }

    fn load_function(&mut self, f: &FunctionCode, base: u32) -> Result<LoadedFn, Abrupt> {
        let mut consts = Vec::with_capacity(f.consts.len());
        let mut keys = Vec::with_capacity(f.consts.len());
        for c in &f.consts {
            let (cv, key) = match c {
                Const::Number(bits) => (
                    ConstVal::Value(number_constant(f64::from_bits(*bits))),
                    None,
                ),
                Const::String(units) => {
                    let s = JsString::from_units(units).map_err(|_| Abrupt::OutOfMemory)?;
                    let key = self.heap.intern(&s)?;
                    (ConstVal::Value(self.heap.new_string(s)?), Some(key))
                }
                Const::BigInt(_) => (ConstVal::Unsupported("BigInt literals"), None),
                Const::GlobalDeclarations(_)
                | Const::RegExp(_)
                | Const::Template(_)
                | Const::ArgumentsMap(_)
                | Const::EvalScope(_) => (ConstVal::Record, None),
            };
            consts.push(cv);
            keys.push(key);
        }
        let nics = usize::try_from(f.nics).map_err(|_| Abrupt::OutOfMemory)?;
        Ok(LoadedFn {
            code: f.clone(),
            consts,
            keys,
            base,
            ics: vec![IcEntry::default(); nics],
            entries: 0,
            back_edges: 0,
            name_value: None,
            needs_args: f.instrs.iter().any(|i| {
                matches!(
                    i,
                    Instr::CreateUnmappedArguments { .. }
                        | Instr::CreateMappedArguments { .. }
                        | Instr::CreateRestArray { .. }
                )
            }),
        })
    }

    /// Runs a loaded script with `this` the global object, and returns the
    /// value its function returns.
    ///
    /// # Errors
    /// The [`Abrupt`] the run ended with.
    pub fn run(&mut self, script: &Script) -> Result<Value, Abrupt> {
        let global = self.global;
        let main = usize::try_from(script.main).map_err(|_| Abrupt::Internal("script index"))?;
        let f = self.new_closure(main, Value::UNDEFINED)?;
        self.call(f, global, &[])
    }

    // -----------------------------------------------------------------
    // Calls and frames
    // -----------------------------------------------------------------

    /// Calls a function value: a native runs at once; a closure gets a frame
    /// on top of the running one and the loop runs until it returns. Natives
    /// call back into JS through this.
    ///
    /// # Errors
    /// The [`Abrupt`] the call ended with; a JS exception that escapes the
    /// function is [`Abrupt::Throw`].
    pub fn call(&mut self, callee: Value, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
        let kind = self.heap.obj(callee).map(|o| o.kind);
        match kind {
            Some(ObjKind::Native(i)) => {
                let r = self.invoke_native(i, callee, this, args, Value::UNDEFINED);
                self.report_heap_limit(r)
            }
            Some(ObjKind::Bound(i)) => {
                let b = self.bound_fn(i)?;
                let mut all = b.args;
                all.extend_from_slice(args);
                self.call(b.target, b.this, &all)
            }
            Some(ObjKind::Closure { code, .. }) => {
                let saved = (self.fp, self.pc, self.cur, self.top);
                let entered = self.enter_closure(callee, code, this, args, None, KIND_PLAIN);
                let result = match entered {
                    Ok(()) => self.execute(),
                    Err(e) => Err(e),
                };
                (self.fp, self.pc, self.cur, self.top) = saved;
                result
            }
            _ => Err(self.type_error("not a function")),
        }
    }

    pub(crate) fn native(&self, i: u32) -> Result<(NativeFn, bool), Abrupt> {
        usize::try_from(i)
            .ok()
            .and_then(|i| self.natives.get(i))
            .copied()
            .ok_or(Abrupt::Internal("native index"))
    }

    /// Runs native `i`, which is function object `callee`, with `new_target`
    /// the constructor for a `new` and `undefined` for a call; the previous
    /// active function and new target come back afterwards.
    pub(crate) fn invoke_native(
        &mut self,
        i: u32,
        callee: Value,
        this: Value,
        args: &[Value],
        new_target: Value,
    ) -> Result<Value, Abrupt> {
        let (f, _) = self.native(i)?;
        // Natives nest on the host stack (`join` of an array that holds
        // itself): a bound keeps that from overflowing it.
        if self.native_depth >= self.native_limit {
            return Err(self.range_error("Maximum call stack size exceeded"));
        }
        let saved = (self.active, self.new_target);
        (self.active, self.new_target) = (callee, new_target);
        self.native_depth = self.native_depth.saturating_add(1);
        let r = f(self, this, args);
        self.native_depth = self.native_depth.saturating_sub(1);
        (self.active, self.new_target) = saved;
        r
    }

    /// The function object of the running native: the callee a native does
    /// not otherwise know (one native serves several constructors).
    #[must_use]
    pub fn active_function(&self) -> Value {
        self.active
    }

    /// `NewTarget` of the running native: `undefined` when it was called, the
    /// constructor when it was constructed.
    #[must_use]
    pub fn new_target(&self) -> Value {
        self.new_target
    }

    /// An intrinsic of the realm, `undefined` until it is installed.
    #[must_use]
    pub fn intrinsic(&self, which: Intrinsic) -> Value {
        self.intrinsics
            .get(which as usize)
            .copied()
            .unwrap_or(Value::UNDEFINED)
    }

    /// Installs an intrinsic.
    pub fn set_intrinsic(&mut self, which: Intrinsic, v: Value) {
        if let Some(slot) = self.intrinsics.get_mut(which as usize) {
            *slot = v;
        }
    }

    pub(crate) fn code_of(&self, callee: Value) -> Result<usize, Abrupt> {
        match self.heap.obj(callee).map(|o| o.kind) {
            Some(ObjKind::Closure { code, .. }) => {
                usize::try_from(code).map_err(|_| Abrupt::Internal("code index"))
            }
            _ => Err(Abrupt::Internal("frame callee is not a closure")),
        }
    }

    pub(crate) fn bound_fn(&self, i: u32) -> Result<BoundFn, Abrupt> {
        usize::try_from(i)
            .ok()
            .and_then(|i| self.bound.get(i))
            .cloned()
            .ok_or(Abrupt::Internal("bound function index"))
    }

    fn func(&self, code: usize) -> Result<&LoadedFn, Abrupt> {
        self.codes.get(code).ok_or(Abrupt::Internal("code index"))
    }

    fn set_frame(&mut self, fp: usize, pc: usize, cur: usize) -> Result<(), Abrupt> {
        let f = self.func(cur)?;
        let size =
            frame_size(f.code.nparams, f.code.nregs).ok_or(Abrupt::Internal("frame size"))?;
        let top = fp.checked_add(size).ok_or(Abrupt::Internal("frame top"))?;
        (self.fp, self.pc, self.cur, self.top) = (fp, pc, cur, top);
        Ok(())
    }

    /// Pushes a frame for closure `callee` (code `code`) on top of the
    /// running frame (`spec::Op::Call`'s `pushed_region`), and makes it the
    /// running one. `ret` is the caller's call op, or `None` for an entry from
    /// outside the loop.
    pub(crate) fn enter_closure(
        &mut self,
        callee: Value,
        code: u32,
        this: Value,
        args: &[Value],
        ret: Option<usize>,
        frame_kind: u32,
    ) -> Result<(), Abrupt> {
        let code = usize::try_from(code).map_err(|_| Abrupt::Internal("code index"))?;
        let (kind, strict, nparams, nregs) = {
            let f = self.func(code)?;
            (f.code.kind, f.code.strict, f.code.nparams, f.code.nregs)
        };
        if frame_kind == KIND_PLAIN && matches!(kind, FunctionKind::Class | FunctionKind::Derived) {
            return Err(self.type_error("Class constructor cannot be invoked without 'new'"));
        }
        // §10.2.1.2 OrdinaryCallBindThis: a sloppy function's `this` is the
        // global object for undefined and null; a primitive's wrapper object
        // needs the wrapper constructors (not yet).
        let this = if strict || kind == FunctionKind::Arrow {
            this
        } else if matches!(
            this.decode(),
            clazel_js_heap::value::Decoded::Undefined | clazel_js_heap::value::Decoded::Null
        ) {
            self.global
        } else if self.heap.is_object(this) {
            this
        } else {
            // Step 6.b: ToObject(thisArgument), the wrapper object.
            self.to_object(this)?
        };
        self.charge()?;
        let size = frame_size(nparams, nregs).ok_or(Abrupt::Internal("frame size"))?;
        let ret_value = match ret {
            Some(pc) => pack_ret(self.fp, pc),
            None => Value::raw(RET_NONE),
        };
        let Some(ret_value) = ret_value else {
            return Err(self.range_error("Maximum call stack size exceeded"));
        };
        let argc = u32::try_from(args.len()).unwrap_or(u32::MAX >> 4);
        let argc_slot = enc_argc(argc.min(0x0FFF_FFFF), frame_kind)
            .ok_or(Abrupt::Internal("argument count"))?;
        let base = self.top;
        if self.codes.get(code).is_some_and(|f| f.needs_args) {
            self.host.entry_args.insert(base, args.to_vec());
        }
        let header = [callee, this, argc_slot, ret_value];
        if self.region.push_frame(base, size, header) == Err(FrameError::Overflow) {
            return Err(self.range_error("Maximum call stack size exceeded"));
        }
        for (i, a) in args
            .iter()
            .take(usize::try_from(nparams).unwrap_or(0))
            .enumerate()
        {
            let r = u32::try_from(i).map_err(|_| Abrupt::Internal("argument index"))?;
            self.region.set_reg(base, r, *a)?;
        }
        self.set_frame(base, 0, code)?;
        if let Some(f) = self.codes.get_mut(code) {
            f.entries = f.entries.saturating_add(1);
        }
        Ok(())
    }

    /// The termination check (phase-7.md, "Limits and stopping"): at every
    /// back-edge and call.
    pub(crate) fn charge(&mut self) -> Result<(), Abrupt> {
        if self.terminator.is_set() || self.budget == 0 {
            return Err(Abrupt::Terminated);
        }
        self.budget = self.budget.saturating_sub(1);
        Ok(())
    }

    // -----------------------------------------------------------------
    // The loop
    // -----------------------------------------------------------------

    /// Runs the running frame (which has no caller in the region) until it
    /// returns, unwinding exceptions through the frames above it.
    ///
    /// An op that runs out of heap ([`Abrupt::OutOfMemory`]: the byte or cell
    /// limit, or a string past its length limit) throws a `RangeError`
    /// instead, which a `catch` can see (phase-7.md 7.19); see
    /// [`Vm::heap_limit_error`].
    ///
    /// Every entry but the outermost is a re-entry from inside an op or a
    /// native (a callback of `forEach`, the `toString` that ToPrimitive
    /// calls), which takes host stack as a native does. The entries are
    /// counted, and one more than [`Vm::set_native_depth_limit`] allows is a
    /// `RangeError` (phase-7.md 7.19): so a native that calls back into JS
    /// can run at the limit, and a chain of calls through ops alone (`'' +
    /// o` in `o.toString`) is bounded too.
    pub(crate) fn execute(&mut self) -> Result<Value, Abrupt> {
        if self.reentry_depth > self.native_limit {
            return Err(self.range_error("Maximum call stack size exceeded"));
        }
        self.reentry_depth = self.reentry_depth.saturating_add(1);
        let r = self.execute_loop();
        self.reentry_depth = self.reentry_depth.saturating_sub(1);
        r
    }

    /// The loop of [`Vm::execute`].
    fn execute_loop(&mut self) -> Result<Value, Abrupt> {
        loop {
            let stepped = self.step();
            match self.report_heap_limit(stepped) {
                Ok(Flow::Continue) => {}
                Ok(Flow::Done(v)) => return Ok(v),
                Err(Abrupt::Throw(v)) => {
                    if !self.unwind(v)? {
                        return Err(Abrupt::Throw(v));
                    }
                }
                Err(e) => return Err(e),
            }
        }
    }

    /// Unwinds a thrown value: true if a handler caught it (the running frame
    /// and `pc` are now the handler's), false if it left the entry frame.
    fn unwind(&mut self, exc: Value) -> Result<bool, Abrupt> {
        loop {
            let pc = u32::try_from(self.pc).map_err(|_| Abrupt::Internal("pc"))?;
            let target = self
                .func(self.cur)?
                .code
                .handlers
                .iter()
                .find(|h| h.start <= pc && pc < h.end)
                .map(|h| h.target);
            if let Some(t) = target {
                self.exception = exc;
                let target = usize::try_from(t).map_err(|_| Abrupt::Internal("pc"))?;
                self.pc = target;
                return Ok(true);
            }
            match self.pop_frame()? {
                Some(()) => {}
                None => return Ok(false),
            }
        }
    }

    /// Pops the running frame to its caller, at the caller's call op. `None`
    /// if the frame has no caller in the region.
    fn pop_frame(&mut self) -> Result<Option<()>, Abrupt> {
        let ret = unpack_ret(self.region.header(self.fp, HDR_RET)?)
            .ok_or(Abrupt::Internal("return address"))?;
        match ret {
            Ret::None => Ok(None),
            Ret::Caller { base, pc } => {
                let callee = self.region.header(base, HDR_CALLEE)?;
                let code = self.code_of(callee)?;
                self.set_frame(base, pc, code)?;
                Ok(Some(()))
            }
        }
    }

    fn do_return(&mut self, v: Value) -> Result<Flow, Abrupt> {
        let (_, kind) = crate::frame::dec_argc(self.region.header(self.fp, HDR_ARGC)?)
            .ok_or(Abrupt::Internal("argument count slot"))?;
        // [[Construct]] §10.2.2 step 10 and 11: a base constructor's result is
        // the value returned if it is an object, else `this`.
        let v = match kind {
            KIND_PLAIN => v,
            KIND_CONSTRUCT if self.heap.is_object(v) => v,
            KIND_CONSTRUCT => self.region.header(self.fp, crate::frame::HDR_THIS)?,
            _ => {
                return Err(Abrupt::NotYet("return from a suspendable frame".into()));
            }
        };
        let ret = unpack_ret(self.region.header(self.fp, HDR_RET)?)
            .ok_or(Abrupt::Internal("return address"))?;
        match ret {
            Ret::None => Ok(Flow::Done(v)),
            Ret::Caller { base, pc } => {
                let callee = self.region.header(base, HDR_CALLEE)?;
                let code = self.code_of(callee)?;
                let dst = match self.func(code)?.code.instrs.get(pc) {
                    Some(
                        Instr::Call { dst, .. }
                        | Instr::New { dst, .. }
                        | Instr::CallSpread { dst, .. }
                        | Instr::NewSpread { dst, .. },
                    ) => *dst,
                    _ => return Err(Abrupt::Internal("return address is not a call op")),
                };
                self.region.set_reg(base, dst, v)?;
                self.set_frame(base, pc.saturating_add(1), code)?;
                Ok(Flow::Continue)
            }
        }
    }

    fn fetch(&self) -> Result<Instr, Abrupt> {
        self.func(self.cur)?
            .code
            .instrs
            .get(self.pc)
            .cloned()
            .ok_or(Abrupt::Internal("pc past the end of the function"))
    }

    pub(crate) fn r(&self, r: u32) -> Result<Value, Abrupt> {
        Ok(self.region.reg(self.fp, r)?)
    }

    pub(crate) fn w(&mut self, r: u32, v: Value) -> Result<(), Abrupt> {
        Ok(self.region.set_reg(self.fp, r, v)?)
    }

    pub(crate) fn konst(&self, k: u32) -> Result<ConstVal, Abrupt> {
        let i = usize::try_from(k).map_err(|_| Abrupt::Internal("constant index"))?;
        self.func(self.cur)?
            .consts
            .get(i)
            .copied()
            .ok_or(Abrupt::Internal("constant index"))
    }

    pub(crate) fn key_const(&self, k: u32) -> Result<Key, Abrupt> {
        let i = usize::try_from(k).map_err(|_| Abrupt::Internal("constant index"))?;
        self.func(self.cur)?
            .keys
            .get(i)
            .copied()
            .flatten()
            .ok_or(Abrupt::Internal("property name constant is not a string"))
    }

    pub(crate) fn strict(&self) -> bool {
        self.codes.get(self.cur).is_some_and(|f| f.code.strict)
    }

    /// The call of `Call` and `CallSpread`: `f` with `this` `t` and the
    /// arguments; the result goes to register `dst`. True if a closure's
    /// frame was entered (its return writes `dst`), false if the call
    /// finished.
    fn call_op(&mut self, dst: u32, f: Value, t: Value, vals: Vec<Value>) -> Result<bool, Abrupt> {
        let (mut f, mut t, mut vals) = (f, t, vals);
        // §10.4.1.1 [[Call]] of a bound function: the target, with the bound
        // `this` and the bound arguments first.
        while let Some(ObjKind::Bound(i)) = self.heap.obj(f).map(|o| o.kind) {
            let b = self.bound_fn(i)?;
            f = b.target;
            t = b.this;
            let mut all = b.args;
            all.extend_from_slice(&vals);
            vals = all;
        }
        match self.heap.obj(f).map(|o| o.kind) {
            Some(ObjKind::Closure { code, .. }) => {
                self.enter_closure(f, code, t, &vals, Some(self.pc), KIND_PLAIN)?;
                Ok(true)
            }
            Some(ObjKind::Native(i)) => {
                self.charge()?;
                let v = self.invoke_native(i, f, t, &vals, Value::UNDEFINED)?;
                self.w(dst, v)?;
                Ok(false)
            }
            _ => {
                let t = self.type_of(f);
                let t = self.string_text(t).unwrap_or_default();
                Err(self.type_error(&format!("{t} is not a function")))
            }
        }
    }

    /// Runs one op of the running frame.
    pub(crate) fn step(&mut self) -> Result<Flow, Abrupt> {
        let ins = self.fetch()?;
        let mut next = self.pc.saturating_add(1);
        macro_rules! target {
            ($t:expr) => {
                usize::try_from($t).map_err(|_| Abrupt::Internal("jump target"))?
            };
        }
        macro_rules! arith {
            ($dst:expr, $a:expr, $b:expr, $f:path, $op:expr) => {{
                let (x, y) = (self.r($a)?, self.r($b)?);
                let v = match (num(x), num(y)) {
                    (Some(p), Some(q)) => $f(p, q),
                    _ => self.arith_slow($op, x, y)?,
                };
                self.w($dst, v)?;
            }};
        }
        macro_rules! compare {
            ($dst:expr, $a:expr, $b:expr, $f:path, $op:expr) => {{
                let (x, y) = (self.r($a)?, self.r($b)?);
                let v = match (num(x), num(y)) {
                    (Some(p), Some(q)) => $f(p, q),
                    _ => self.relational($op, x, y)?,
                };
                self.w($dst, Value::boolean(v))?;
            }};
        }
        match ins {
            // --- Core ---
            Instr::Nop => {}
            Instr::Move { dst, src } => {
                let v = self.r(src)?;
                self.w(dst, v)?;
            }
            Instr::LoadConst { dst, k } => match self.konst(k)? {
                ConstVal::Value(v) => self.w(dst, v)?,
                ConstVal::Unsupported(what) => return Err(Abrupt::NotYet(what.into())),
                ConstVal::Record => return Err(Abrupt::Internal("LoadConst of a record")),
            },
            Instr::LoadInt { dst, imm } => self.w(dst, Value::int32(imm))?,
            Instr::LoadUndefined { dst } => self.w(dst, Value::UNDEFINED)?,
            Instr::LoadNull { dst } => self.w(dst, Value::NULL)?,
            Instr::LoadBool { dst, flag } => self.w(dst, Value::boolean(flag))?,
            Instr::LoadHole { dst } => self.w(dst, Value::HOLE)?,
            Instr::GetThis { dst } => {
                let v = self.region.header(self.fp, crate::frame::HDR_THIS)?;
                self.w(dst, v)?;
            }
            Instr::GetCallee { dst } => {
                let v = self.region.header(self.fp, HDR_CALLEE)?;
                self.w(dst, v)?;
            }
            Instr::GetArgc { dst } => {
                let (argc, _) = crate::frame::dec_argc(self.region.header(self.fp, HDR_ARGC)?)
                    .ok_or(Abrupt::Internal("argument count slot"))?;
                let argc = i32::try_from(argc).map_err(|_| Abrupt::Internal("argument count"))?;
                self.w(dst, Value::int32(argc))?;
            }
            Instr::GetException { dst } => {
                let v = self.exception;
                self.w(dst, v)?;
            }
            Instr::Jump { target } => next = target!(target),
            Instr::JumpIfUndefined { src, target } => {
                if self.r(src)? == Value::UNDEFINED {
                    next = target!(target);
                }
            }
            Instr::JumpIfNotUndefined { src, target } => {
                if self.r(src)? != Value::UNDEFINED {
                    next = target!(target);
                }
            }
            Instr::JumpIfNullish { src, target } => {
                let v = self.r(src)?;
                if v == Value::UNDEFINED || v == Value::NULL {
                    next = target!(target);
                }
            }
            Instr::JumpIfNotNullish { src, target } => {
                let v = self.r(src)?;
                if v != Value::UNDEFINED && v != Value::NULL {
                    next = target!(target);
                }
            }

            // --- Guarded: Numbers ---
            Instr::Add { dst, a, b } => {
                let (x, y) = (self.r(a)?, self.r(b)?);
                let v = match (num(x), num(y)) {
                    (Some(p), Some(q)) => numeric::add(p, q),
                    _ => self.add_slow(x, y)?,
                };
                self.w(dst, v)?;
            }
            Instr::Sub { dst, a, b } => arith!(dst, a, b, numeric::sub, ArithOp::Sub),
            Instr::Mul { dst, a, b } => arith!(dst, a, b, numeric::mul, ArithOp::Mul),
            Instr::Div { dst, a, b } => arith!(dst, a, b, numeric::div, ArithOp::Div),
            Instr::Mod { dst, a, b } => arith!(dst, a, b, numeric::rem, ArithOp::Mod),
            Instr::BitAnd { dst, a, b } => arith!(dst, a, b, numeric::bit_and, ArithOp::BitAnd),
            Instr::BitOr { dst, a, b } => arith!(dst, a, b, numeric::bit_or, ArithOp::BitOr),
            Instr::BitXor { dst, a, b } => arith!(dst, a, b, numeric::bit_xor, ArithOp::BitXor),
            Instr::Shl { dst, a, b } => arith!(dst, a, b, numeric::shl, ArithOp::Shl),
            Instr::Shr { dst, a, b } => arith!(dst, a, b, numeric::shr, ArithOp::Shr),
            Instr::UShr { dst, a, b } => arith!(dst, a, b, numeric::ushr, ArithOp::UShr),
            Instr::Exp { dst, a, b } => {
                let (x, y) = (self.r(a)?, self.r(b)?);
                let (p, q) = (self.coerce_number(x)?, self.coerce_number(y)?);
                self.w(
                    dst,
                    Value::double(numeric::exponentiate(p.to_f64(), q.to_f64())),
                )?;
            }
            Instr::Neg { dst, src } => {
                let n = self.number_in_reg(src)?;
                self.w(dst, numeric::neg(n))?;
            }
            Instr::Inc { dst, src } => {
                let n = self.number_in_reg(src)?;
                self.w(dst, numeric::inc(n))?;
            }
            Instr::Dec { dst, src } => {
                let n = self.number_in_reg(src)?;
                self.w(dst, numeric::dec(n))?;
            }
            Instr::BitNot { dst, src } => {
                let n = self.number_in_reg(src)?;
                self.w(dst, numeric::bit_not(n))?;
            }
            Instr::Lt { dst, a, b } => compare!(dst, a, b, numeric::lt, Rel::Lt),
            Instr::Le { dst, a, b } => compare!(dst, a, b, numeric::le, Rel::Le),
            Instr::Gt { dst, a, b } => compare!(dst, a, b, numeric::gt, Rel::Gt),
            Instr::Ge { dst, a, b } => compare!(dst, a, b, numeric::ge, Rel::Ge),
            Instr::StrictEq { dst, a, b } => {
                let (x, y) = (self.r(a)?, self.r(b)?);
                let v = self.strict_equals(x, y);
                self.w(dst, Value::boolean(v))?;
            }
            Instr::StrictNe { dst, a, b } => {
                let (x, y) = (self.r(a)?, self.r(b)?);
                let v = self.strict_equals(x, y);
                self.w(dst, Value::boolean(!v))?;
            }
            Instr::LooseEq { dst, a, b } => {
                let (x, y) = (self.r(a)?, self.r(b)?);
                let v = self.loose_equals(x, y)?;
                self.w(dst, Value::boolean(v))?;
            }
            Instr::LooseNe { dst, a, b } => {
                let (x, y) = (self.r(a)?, self.r(b)?);
                let v = self.loose_equals(x, y)?;
                self.w(dst, Value::boolean(!v))?;
            }
            Instr::Not { dst, src } => {
                let v = self.r(src)?;
                let t = self.to_boolean(v);
                self.w(dst, Value::boolean(!t))?;
            }
            Instr::ToNumeric { dst, src } | Instr::ToNumber { dst, src } => {
                let v = self.r(src)?;
                let n = self.coerce_number(v)?;
                let out = match n {
                    Num::I(i) => Value::int32(i),
                    Num::D(d) => Value::double(d),
                };
                self.w(dst, out)?;
            }
            Instr::JumpIfTrue { cond, target } => {
                let v = self.r(cond)?;
                if self.to_boolean(v) {
                    next = target!(target);
                }
            }
            Instr::JumpIfFalse { cond, target } => {
                let v = self.r(cond)?;
                if !self.to_boolean(v) {
                    next = target!(target);
                }
            }
            Instr::Loop { target } => {
                self.charge()?;
                if let Some(f) = self.codes.get_mut(self.cur) {
                    f.back_edges = f.back_edges.saturating_add(1);
                }
                next = target!(target);
            }
            Instr::ThrowIfHole { src } => {
                if self.r(src)? == Value::HOLE {
                    return Err(
                        self.reference_error("Cannot access a binding before initialization")
                    );
                }
            }

            // --- Properties ---
            Instr::GetProp { dst, obj, key, ic } => {
                let base = self.r(obj)?;
                let v = match self.ic_get(base, ic) {
                    Some(v) => v,
                    None => {
                        let key = self.key_const(key)?;
                        self.get_property(base, key, Some(ic))?
                    }
                };
                self.w(dst, v)?;
            }
            Instr::SetProp { obj, key, val, ic } => {
                let base = self.r(obj)?;
                let v = self.r(val)?;
                if !self.ic_set(base, ic, v) {
                    let key = self.key_const(key)?;
                    self.set_property(base, key, v, Some(ic))?;
                }
            }
            Instr::GetElem { dst, obj, idx } => {
                let (base, k) = (self.r(obj)?, self.r(idx)?);
                let v = self.get_element(base, k)?;
                self.w(dst, v)?;
            }
            Instr::SetElem { obj, idx, val } => {
                let (base, k, v) = (self.r(obj)?, self.r(idx)?, self.r(val)?);
                let key = self.coerce_property_key(k)?;
                self.set_property(base, key, v, None)?;
            }
            // CreateDataPropertyOrThrow (§7.3.7†): a class field named
            // `prototype` of a class, or a field of a frozen object, throws.
            Instr::DefineProp { obj, key, val } => {
                let (o, v) = (self.r(obj)?, self.r(val)?);
                let key = self.key_const(key)?;
                self.create_data_property_or_throw(o, key, v)?;
            }
            Instr::DefineElem { obj, idx, val } => {
                let (o, k, v) = (self.r(obj)?, self.r(idx)?, self.r(val)?);
                // An elision is the hole: no property.
                if v != Value::HOLE {
                    let key = self.coerce_property_key(k)?;
                    self.create_data_property_or_throw(o, key, v)?;
                }
            }
            // ArrayCreate(0), §10.4.2.2†: `len` is only a capacity hint (the
            // elements are ordinary properties of the shape).
            Instr::NewArray { dst, len: _ } => {
                let a = self.array_create(0.0, None)?;
                self.w(dst, a)?;
            }
            // `delete obj[idx]`, §13.5.1.2† step 5: ToObject(base), then
            // `[[Delete]]`; false is a TypeError in strict code.
            Instr::DeleteProp { dst, obj, idx } => {
                let (base, k) = (self.r(obj)?, self.r(idx)?);
                let o = self.to_object(base)?;
                let key = self.coerce_property_key(k)?;
                let ok = self.delete_property(o, key)?;
                if !ok && self.strict() {
                    let name = self.key_text(key);
                    return Err(self.type_error(&format!("Cannot delete property '{name}'")));
                }
                self.w(dst, Value::boolean(ok))?;
            }
            Instr::SetLiteralProto { obj, val } => {
                let (o, v) = (self.r(obj)?, self.r(val)?);
                if v == Value::NULL || self.heap.is_object(v) {
                    self.heap
                        .obj_mut(o)
                        .ok_or(Abrupt::Internal("SetLiteralProto on a non-object"))?
                        .proto = v;
                }
            }
            Instr::InstanceOf { dst, a, b } => {
                let (v, target) = (self.r(a)?, self.r(b)?);
                let r = self.instance_of(v, target)?;
                self.w(dst, Value::boolean(r))?;
            }
            Instr::HasProperty { dst, a, b } => {
                let (k, o) = (self.r(a)?, self.r(b)?);
                if !self.heap.is_object(o) {
                    return Err(
                        self.type_error("Cannot use 'in' operator to search in a non-object")
                    );
                }
                let key = self.coerce_property_key(k)?;
                let found = self.heap.find(o, key)?.is_some();
                self.w(dst, Value::boolean(found))?;
            }
            Instr::NewObject { dst } => {
                let proto = self.atoms.object_proto;
                let o = self.heap.new_object(proto, ObjKind::Plain)?;
                self.w(dst, o)?;
            }

            // --- Environments and closures ---
            Instr::NewEnv { dst, parent, size } => {
                let p = self.r(parent)?;
                let n = usize::try_from(size).map_err(|_| Abrupt::OutOfMemory)?;
                let e = self.heap.alloc(crate::heap::Cell::Env(crate::heap::Env {
                    parent: p,
                    slots: vec![Value::HOLE; n],
                }))?;
                self.w(dst, e)?;
            }
            Instr::GetEnvSlot { dst, env, idx } => {
                let e = self.r(env)?;
                let i = usize::try_from(idx).map_err(|_| Abrupt::Internal("env slot"))?;
                let v = self
                    .heap
                    .env(e)
                    .and_then(|e| e.slots.get(i))
                    .copied()
                    .ok_or(Abrupt::Internal("GetEnvSlot on a bad environment"))?;
                self.w(dst, v)?;
            }
            Instr::SetEnvSlot { env, idx, src } => {
                let (e, v) = (self.r(env)?, self.r(src)?);
                let i = usize::try_from(idx).map_err(|_| Abrupt::Internal("env slot"))?;
                *self
                    .heap
                    .env_mut(e)
                    .and_then(|e| e.slots.get_mut(i))
                    .ok_or(Abrupt::Internal("SetEnvSlot on a bad environment"))? = v;
            }
            Instr::GetEnvParent { dst, env } => {
                let e = self.r(env)?;
                let p = self
                    .heap
                    .env(e)
                    .map(|e| e.parent)
                    .ok_or(Abrupt::Internal("GetEnvParent on a bad environment"))?;
                self.w(dst, p)?;
            }
            Instr::GetCalleeEnv { dst } => {
                let callee = self.region.header(self.fp, HDR_CALLEE)?;
                let env = match self.heap.obj(callee).map(|o| o.kind) {
                    Some(ObjKind::Closure { env, .. }) => env,
                    _ => return Err(Abrupt::Internal("GetCalleeEnv without a closure")),
                };
                self.w(dst, env)?;
            }
            Instr::NewClosure { dst, func, env } => {
                let e = self.r(env)?;
                let base = self.func(self.cur)?.base;
                let code = base
                    .checked_add(func)
                    .ok_or(Abrupt::Internal("function index"))?;
                let code = usize::try_from(code).map_err(|_| Abrupt::Internal("function index"))?;
                let c = self.new_closure(code, e)?;
                self.w(dst, c)?;
            }

            // --- Calls ---
            Instr::Call {
                dst,
                callee,
                this,
                args,
                argc,
            } => {
                let f = self.r(callee)?;
                let t = self.r(this)?;
                let mut vals = Vec::with_capacity(usize::try_from(argc).unwrap_or(0));
                for i in 0..argc {
                    let reg = args
                        .checked_add(i)
                        .ok_or(Abrupt::Internal("argument register"))?;
                    vals.push(self.r(reg)?);
                }
                if self.call_op(dst, f, t, vals)? {
                    return Ok(Flow::Continue);
                }
            }
            // `f(...xs)`: the compiler collected the arguments in an array
            // (§13.3.8.1† ArgumentListEvaluation); then as `Call`.
            Instr::CallSpread {
                dst,
                callee,
                this,
                args,
            } => {
                let f = self.r(callee)?;
                let t = self.r(this)?;
                let arr = self.r(args)?;
                let vals = self.spread_arguments(arr)?;
                if self.call_op(dst, f, t, vals)? {
                    return Ok(Flow::Continue);
                }
            }
            // `new f(...xs)`: EvaluateNew §13.3.5.1.1† steps 5 and 6 with
            // the arguments of the array.
            Instr::NewSpread { dst, callee, args } => {
                let f = self.r(callee)?;
                let arr = self.r(args)?;
                let vals = self.spread_arguments(arr)?;
                match self.construct(f, &vals, Some(self.pc))? {
                    Some(v) => self.w(dst, v)?,
                    None => return Ok(Flow::Continue),
                }
            }
            // --- Iteration ---
            Instr::GetIterator { dst, src } => {
                let v = self.r(src)?;
                let rec = self.get_iterator(v)?;
                self.w(dst, rec)?;
            }
            Instr::IterNext { value, done, iter } => {
                let rec = self.r(iter)?;
                let step = self.iterator_step_value(rec)?;
                self.w(done, Value::boolean(step.is_none()))?;
                self.w(value, step.unwrap_or(Value::UNDEFINED))?;
            }
            Instr::IterClose { iter } => {
                let rec = self.r(iter)?;
                self.iterator_close(rec)?;
            }
            Instr::CopyDataProperties {
                obj,
                src,
                excl,
                nexcl,
            } => {
                let (target, source) = (self.r(obj)?, self.r(src)?);
                let mut excluded = Vec::new();
                for i in 0..nexcl {
                    let reg = excl
                        .checked_add(i)
                        .ok_or(Abrupt::Internal("excluded key register"))?;
                    let kv = self.r(reg)?;
                    excluded.push(self.coerce_property_key(kv)?);
                }
                self.copy_data_properties(target, source, &excluded)?;
            }
            Instr::ThrowIfNotObject { src } => {
                let v = self.r(src)?;
                if !self.heap.is_object(v) {
                    return Err(self.type_error("Iterator result is not an object"));
                }
            }
            Instr::ToObject { dst, src } => {
                let v = self.r(src)?;
                let o = self.to_object(v)?;
                self.w(dst, o)?;
            }
            Instr::ForInIterator { dst, src } => {
                let v = self.r(src)?;
                let rec = self.for_in_iterator(v)?;
                self.w(dst, rec)?;
            }
            Instr::New {
                dst,
                callee,
                args,
                argc,
            } => {
                let f = self.r(callee)?;
                let mut vals = Vec::with_capacity(usize::try_from(argc).unwrap_or(0));
                for i in 0..argc {
                    let reg = args
                        .checked_add(i)
                        .ok_or(Abrupt::Internal("argument register"))?;
                    vals.push(self.r(reg)?);
                }
                match self.construct(f, &vals, Some(self.pc))? {
                    // A native constructor finished at once.
                    Some(v) => self.w(dst, v)?,
                    // A frame was entered; its return writes `dst`.
                    None => return Ok(Flow::Continue),
                }
            }
            Instr::Return { src } => {
                let v = self.r(src)?;
                return self.do_return(v);
            }

            // --- Globals ---
            Instr::GetGlobal { dst, key, ic: _ } => {
                let key = self.key_const(key)?;
                let v = self.get_global(key, true)?;
                self.w(dst, v)?;
            }
            Instr::GetGlobalOrUndefined { dst, key } => {
                let key = self.key_const(key)?;
                let v = self.get_global(key, false)?;
                self.w(dst, v)?;
            }
            Instr::SetGlobal { key, src, ic: _ } => {
                let key = self.key_const(key)?;
                let v = self.r(src)?;
                self.set_global(key, v)?;
            }
            Instr::DeclareGlobals { k } => self.declare_globals(k)?,
            // MakeMethod (§10.2.7†) records [[HomeObject]], which `super`
            // property access reads (`GetSuperBase`).
            Instr::SetHomeObject { func, obj } => {
                let (f, o) = (self.r(func)?, self.r(obj)?);
                self.host.class.home_objects.insert(f, o);
            }
            Instr::ClassSetup {
                ctor,
                proto,
                heritage,
                derived,
            } => {
                let (c, h) = (self.r(ctor)?, self.r(heritage)?);
                let p = self.class_setup(c, h, derived)?;
                self.w(proto, p)?;
            }
            Instr::SetInstanceInit { ctor, init } => {
                let (c, i) = (self.r(ctor)?, self.r(init)?);
                self.host.class.instance_inits.insert(c, i);
            }
            Instr::InitInstance { obj, func } => {
                let (o, f) = (self.r(obj)?, self.r(func)?);
                self.initialize_instance(o, f)?;
            }
            Instr::SuperCall {
                dst,
                func,
                newtarget,
                this,
                args,
                argc,
            } => {
                let mut vals = Vec::with_capacity(usize::try_from(argc).unwrap_or(0));
                for i in 0..argc {
                    let reg = args
                        .checked_add(i)
                        .ok_or(Abrupt::Internal("argument register"))?;
                    vals.push(self.r(reg)?);
                }
                let (f, nt, t) = (self.r(func)?, self.r(newtarget)?, self.r(this)?);
                let v = self.super_call(f, nt, t, &vals)?;
                self.w(dst, v)?;
            }
            Instr::SuperCallSpread {
                dst,
                func,
                newtarget,
                this,
                args,
            } => {
                let arr = self.r(args)?;
                let vals = self.spread_arguments(arr)?;
                let (f, nt, t) = (self.r(func)?, self.r(newtarget)?, self.r(this)?);
                let v = self.super_call(f, nt, t, &vals)?;
                self.w(dst, v)?;
            }
            Instr::GetSuperBase { dst, func } => {
                let f = self.r(func)?;
                let v = self.super_base(f)?;
                self.w(dst, v)?;
            }
            Instr::GetSuper {
                dst,
                base,
                key,
                this,
            } => {
                let (b, k, t) = (self.r(base)?, self.r(key)?, self.r(this)?);
                let v = self.get_super(b, k, t)?;
                self.w(dst, v)?;
            }
            Instr::SetSuper {
                base,
                key,
                val,
                this,
            } => {
                let (b, k, v, t) = (self.r(base)?, self.r(key)?, self.r(val)?, self.r(this)?);
                self.set_super(b, k, v, t)?;
            }
            Instr::GetNewTarget { dst } => {
                let v = self.current_new_target()?;
                self.w(dst, v)?;
            }
            Instr::ConstructResult { dst, val, this } => {
                let (v, t) = (self.r(val)?, self.r(this)?);
                let r = self.construct_result(v, t)?;
                self.w(dst, r)?;
            }
            Instr::NewPrivateName { dst, k } => {
                let desc = match self.konst(k)? {
                    ConstVal::Value(v) => v,
                    _ => {
                        return Err(Abrupt::Internal(
                            "NewPrivateName of a constant that is no string",
                        ));
                    }
                };
                let n = self.new_private_name(desc)?;
                self.w(dst, n)?;
            }
            Instr::GetPrivate { dst, obj, name } => {
                let (o, n) = (self.r(obj)?, self.r(name)?);
                let v = self.private_get(o, n)?;
                self.w(dst, v)?;
            }
            Instr::SetPrivate { obj, name, val } => {
                let (o, n, v) = (self.r(obj)?, self.r(name)?, self.r(val)?);
                self.private_set(o, n, v)?;
            }
            Instr::DefinePrivate {
                obj,
                name,
                val,
                form,
            } => {
                let (o, n, v) = (self.r(obj)?, self.r(name)?, self.r(val)?);
                self.define_private(o, n, v, form)?;
            }
            Instr::HasPrivate { dst, name, obj } => {
                let (n, o) = (self.r(name)?, self.r(obj)?);
                let r = self.has_private(n, o)?;
                self.w(dst, Value::boolean(r))?;
            }
            // DefineMethodProperty (§15.4.5†) for a method (form 0):
            // SetFunctionName(closure, key), §10.2.9†, then
            // DefinePropertyOrThrow(homeObject, key, PropertyDescriptor {
            // [[Value]]: closure, [[Writable]]: true, [[Enumerable]]:
            // enumerable, [[Configurable]]: true }).
            Instr::DefineMethod {
                obj,
                key,
                func,
                form: 0,
                enumerable,
            } => {
                let (o, k, f) = (self.r(obj)?, self.r(key)?, self.r(func)?);
                let name = self.function_name_for_key(k)?;
                let pk = self.coerce_property_key(k)?;
                let kn = self.atoms.k_name;
                self.heap.define(f, kn, name, Attrs(Attrs::CONFIGURABLE))?;
                let desc = crate::props::PropDesc {
                    value: Some(f),
                    writable: Some(true),
                    enumerable: Some(enumerable),
                    configurable: Some(true),
                    ..crate::props::PropDesc::default()
                };
                self.define_property_or_throw(o, pk, &desc)?;
            }
            // The getter (form 1) and setter (form 2) of MethodDefinition
            // evaluation (§15.4.5†): SetFunctionName(closure, propKey, "get" or
            // "set") (§10.2.9† step 5), then DefinePropertyOrThrow(object,
            // propKey, PropertyDescriptor { [[Get]] or [[Set]]: closure,
            // [[Enumerable]]: enumerable, [[Configurable]]: true }).
            Instr::DefineMethod {
                obj,
                key,
                func,
                form: form @ (1 | 2),
                enumerable,
            } => {
                let (o, k, f) = (self.r(obj)?, self.r(key)?, self.r(func)?);
                let base_name = self.function_name_for_key(k)?;
                let pk = self.coerce_property_key(k)?;
                let base_units: Vec<u16> = match self.heap.string(base_name) {
                    Some(s) => s.units().collect(),
                    None => Vec::new(),
                };
                let mut units: Vec<u16> = if form == 1 { "get " } else { "set " }
                    .encode_utf16()
                    .collect();
                units.extend(base_units);
                let name = JsString::from_units(&units).map_err(|_| Abrupt::OutOfMemory)?;
                let name = self.heap.new_string(name)?;
                let kn = self.atoms.k_name;
                self.heap.define(f, kn, name, Attrs(Attrs::CONFIGURABLE))?;
                let desc = crate::props::PropDesc {
                    get: (form == 1).then_some(f),
                    set: (form == 2).then_some(f),
                    enumerable: Some(enumerable),
                    configurable: Some(true),
                    ..crate::props::PropDesc::default()
                };
                self.define_property_or_throw(o, pk, &desc)?;
            }
            Instr::InitGlobalLexical { key, src } => {
                let key = self.key_const(key)?;
                let v = self.r(src)?;
                match self.global_lex.get_mut(&key) {
                    Some(entry) => entry.0 = v,
                    None => {
                        return Err(Abrupt::Internal("InitGlobalLexical of an undeclared name"));
                    }
                }
            }

            // --- Conversions and the rest of the handler ops ---
            Instr::TypeOf { dst, src } => {
                let v = self.r(src)?;
                let s = self.type_of(v);
                self.w(dst, s)?;
            }
            Instr::ToPropertyKey { dst, src } => {
                let v = self.r(src)?;
                let s = self.property_key_value(v)?;
                self.w(dst, s)?;
            }
            Instr::ToString { dst, src } => {
                let v = self.r(src)?;
                let s = self.coerce_string_value(v)?;
                self.w(dst, s)?;
            }
            Instr::Throw { src } => {
                let v = self.r(src)?;
                return Err(Abrupt::Throw(v));
            }
            Instr::ThrowError { kind, msg } => {
                let text = match self.konst(msg)? {
                    ConstVal::Value(v) => self.heap.string(v).map(JsString::to_string_lossy),
                    _ => None,
                }
                .unwrap_or_default();
                return Err(self.throw_kind(kind, &text));
            }
            // RegExpCreate (§22.2.3.1†) for a regular expression literal
            // (§13.2.7.3† step 3): `%RegExp%` makes the object.
            Instr::NewRegExp { dst, k } => {
                let v = self.new_regexp(k)?;
                self.w(dst, v)?;
            }
            // CreateUnmappedArgumentsObject §10.4.4.6† and
            // CreateMappedArgumentsObject §10.4.4.7† (see `crate::host`),
            // and the rest parameter's array (§15.1.3† step 4.b).
            Instr::CreateUnmappedArguments { dst } => {
                let v = self.create_arguments_object(true)?;
                self.w(dst, v)?;
            }
            Instr::CreateMappedArguments { dst, .. } => {
                let v = self.create_arguments_object(false)?;
                self.w(dst, v)?;
            }
            Instr::CreateRestArray { dst, from } => {
                let v = self.create_rest_array(from)?;
                self.w(dst, v)?;
            }
            other => return Err(Abrupt::NotYet(op_name(&other))),
        }
        self.pc = next;
        Ok(Flow::Continue)
    }
}

/// The binary operators whose slow path is ToNumeric on both sides.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ArithOp {
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    UShr,
}

impl ArithOp {
    pub(crate) fn apply(self, a: Num, b: Num) -> Value {
        match self {
            ArithOp::Sub => numeric::sub(a, b),
            ArithOp::Mul => numeric::mul(a, b),
            ArithOp::Div => numeric::div(a, b),
            ArithOp::Mod => numeric::rem(a, b),
            ArithOp::BitAnd => numeric::bit_and(a, b),
            ArithOp::BitOr => numeric::bit_or(a, b),
            ArithOp::BitXor => numeric::bit_xor(a, b),
            ArithOp::Shl => numeric::shl(a, b),
            ArithOp::Shr => numeric::shr(a, b),
            ArithOp::UShr => numeric::ushr(a, b),
        }
    }
}

/// The relational operators.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Rel {
    Lt,
    Le,
    Gt,
    Ge,
}

/// The name of an op, for the "not yet implemented" error.
fn op_name(i: &Instr) -> String {
    let dbg = format!("{i:?}");
    dbg.split([' ', '{']).next().unwrap_or("op").to_string()
}

/// The value of a Number constant (see the module header).
fn number_constant(d: f64) -> Value {
    match crate::numeric::narrow(d) {
        Num::I(i) => Value::int32(i),
        Num::D(d) => Value::double(d),
    }
}
