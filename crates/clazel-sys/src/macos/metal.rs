//! Metal, for the GPU process's drawing (phase-5.md item 5.17b), on Apple silicon.
//!
//! Safe wrappers around the Metal, IOSurface and Objective-C runtime calls that
//! `clazel-gpu`'s Metal backend makes. Each wrapper does one Metal operation with
//! values `clazel-gpu` chose (pixel format, blend factors, sizes, shader source),
//! checks what the operation's documentation requires of them, and decides nothing
//! about what is drawn.
//!
//! Objective-C messages go through `objc_msgSend`, which Apple's documentation
//! says must be cast to a function pointer of the method's exact type before it is
//! called. It is declared once, with no parameters, and each signature is one
//! `const` holding one such cast (the dispatcher casts of `xtask/src/sys.rs`), named
//! for its signature, with every selector that uses it listed above it. Citations
//! are to Apple's developer documentation, written `docs <Framework>/<Class>/<member>`.
//!
//! # Modelling choices
//!
//! - **Apple silicon only** (`target_arch = "aarch64"`): `BOOL` is C `bool` there,
//!   and textures may use shared storage, so the CPU reads the target with
//!   `getBytes:` and no synchronisation blit. Intel Macs are not supported.
//! - **Every object held is owned** (+1): a method that returns an owned object
//!   (`alloc`, `new…`, `init…`) is kept as is, and one that returns an autoreleased
//!   object is retained first ([`Object::retained`]); [`Drop`] sends `release`.
//!   [`with_autorelease_pool`] drains what the autoreleasing methods leave.
//! - **The IOSurface's property keys are given as their string values**
//!   (`"IOSurfaceWidth"` and so on), because the `kIOSurface…` constants are data
//!   symbols, which the checker does not allow to be declared. The values are those
//!   of `<IOSurface/IOSurfaceRef.h>`; a wrong key would make `IOSurfaceCreate` or the
//!   texture on it fail, which the tests would show.
//! - **Encoders are scoped**: a render or blit encoder exists only inside the
//!   function that ends it, so none is left open when a command buffer is committed.
//! - **What the GPU reads is not checked here.** A draw's counts are whatever
//!   `clazel-gpu` passes; its fixed shaders bound their own reads. What is checked
//!   here is every CPU-side length, offset and rectangle a call takes.

use std::ffi::{CStr, c_char, c_void};
use std::fmt;
use std::ptr::NonNull;

/// An Objective-C object pointer (`id`).
type Id = *mut c_void;
/// A selector (`SEL`).
type Sel = *const c_void;

#[link(name = "objc", kind = "dylib")]
// SAFETY: docs ObjectiveC/objc_msgSend, docs ObjectiveC/objc_getClass and docs ObjectiveC/sel_registerName,
// from <objc/message.h> and <objc/runtime.h>:
// `objc_getClass(const char *name)` returns `id` (`Class`, a pointer) and
// `sel_registerName(const char *str)` returns `SEL` (a pointer); `c_char` and
// pointers match. `objc_msgSend` is declared here with no parameters, as
// <objc/message.h> does when OBJC_OLD_DISPATCH_PROTOTYPES is 0, because it is
// never called as declared, only cast to a typed pointer (below). libobjc is
// linked by name.
unsafe extern "C" {
    fn objc_msgSend();
    fn objc_getClass(name: *const c_char) -> Id;
    fn sel_registerName(name: *const c_char) -> Sel;
}

#[link(name = "Metal", kind = "framework")]
// SAFETY: docs Metal/MTLCreateSystemDefaultDevice, from <Metal/MTLDevice.h>:
// `id<MTLDevice> MTLCreateSystemDefaultDevice(void)`, returning an owned object or
// nil; the declaration matches (no parameters, a pointer back). Metal is linked as
// a framework.
unsafe extern "C" {
    fn MTLCreateSystemDefaultDevice() -> Id;
}

#[link(name = "IOSurface", kind = "framework")]
// SAFETY: docs IOSurface/IOSurfaceCreate, from <IOSurface/IOSurfaceRef.h>:
// `IOSurfaceRef IOSurfaceCreate(CFDictionaryRef properties)`, returning an owned
// surface (the Create rule) or NULL; both types are pointers, as declared.
unsafe extern "C" {
    fn IOSurfaceCreate(properties: Id) -> Id;
}

#[link(name = "CoreFoundation", kind = "framework")]
// SAFETY: docs CoreFoundation/CFRelease, from <CoreFoundation/CFBase.h>:
// `void CFRelease(CFTypeRef cf)`, `cf` not NULL; `CFTypeRef` is a pointer, as
// declared.
unsafe extern "C" {
    fn CFRelease(cf: Id);
}

#[link(name = "Foundation", kind = "framework")]
// SAFETY: docs Foundation (the framework): nothing is declared; the block links
// Foundation for the NSString, NSNumber, NSDictionary and NSAutoreleasePool
// classes this file finds by name with objc_getClass.
unsafe extern "C" {}

/// `MTLOrigin` (<Metal/MTLTypes.h>): three `NSUInteger`.
#[repr(C)]
#[derive(Clone, Copy)]
struct Origin {
    x: usize,
    y: usize,
    z: usize,
}

/// `MTLSize` (<Metal/MTLTypes.h>): three `NSUInteger`.
#[repr(C)]
#[derive(Clone, Copy)]
struct Size {
    width: usize,
    height: usize,
    depth: usize,
}

/// `MTLRegion` (<Metal/MTLTypes.h>): an origin and a size.
#[repr(C)]
#[derive(Clone, Copy)]
struct Region {
    origin: Origin,
    size: Size,
}

/// `MTLScissorRect` (<Metal/MTLRenderCommandEncoder.h>): four `NSUInteger`.
#[repr(C)]
#[derive(Clone, Copy)]
struct ScissorRect {
    x: usize,
    y: usize,
    width: usize,
    height: usize,
}

/// `MTLClearColor` (<Metal/MTLRenderPass.h>): four `double`.
#[repr(C)]
#[derive(Clone, Copy)]
struct ClearColor {
    red: f64,
    green: f64,
    blue: f64,
    alpha: f64,
}

// The dispatcher casts. Each has the receiver (`id`) and the selector (`SEL`)
// first, then the method's parameters, and its return type, exactly as the
// method is declared; `NSUInteger` is `usize` and `BOOL` is `bool` on Apple
// silicon, and every object parameter is `id`.

// SAFETY: docs ObjectiveC/objc_msgSend ("must be cast to an appropriate function
// pointer type before being called"). Methods `(id)m` returning `id`: docs
// ObjectiveC/NSObject/alloc, docs ObjectiveC/NSObject/init, docs
// ObjectiveC/NSObject/retain, docs Metal/MTLDevice/newCommandQueue, docs
// Metal/MTLCommandQueue/commandBuffer, docs Metal/MTLCommandBuffer/blitCommandEncoder,
// docs Metal/MTLRenderPassDescriptor/renderPassDescriptor (a class method, sent to
// the class), docs Metal/MTLRenderPassDescriptor/colorAttachments and docs
// Metal/MTLRenderPipelineDescriptor/colorAttachments.
const MSG_ID: unsafe extern "C" fn(Id, Sel) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(void)m`: docs ObjectiveC/NSObject/release, docs
// Foundation/NSAutoreleasePool/drain, docs Metal/MTLCommandBuffer/commit, docs
// Metal/MTLCommandBuffer/waitUntilCompleted and docs
// Metal/MTLCommandEncoder/endEncoding.
const MSG_VOID: unsafe extern "C" fn(Id, Sel) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(NSUInteger)m`: docs Metal/MTLCommandBuffer/status (`MTLCommandBufferStatus`,
// an `NSUInteger` enumeration) and docs Metal/MTLBuffer/length.
const MSG_USIZE: unsafe extern "C" fn(Id, Sel) -> usize =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(id)m:(id)a`: docs Metal/MTLLibrary/newFunctionWithName (an NSString name) and
// docs Metal/MTLCommandBuffer/renderCommandEncoderWithDescriptor.
const MSG_ID_ID: unsafe extern "C" fn(Id, Sel, Id) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(id)m:(NSUInteger)a`: docs
// Metal/MTLRenderPassColorAttachmentDescriptorArray/objectAtIndexedSubscript,
// docs Metal/MTLRenderPipelineColorAttachmentDescriptorArray/objectAtIndexedSubscript
// and docs Foundation/NSNumber/initWithUnsignedLong (`unsigned long`, 64 bits on
// Apple silicon, as `NSUInteger`).
const MSG_ID_USIZE: unsafe extern "C" fn(Id, Sel, usize) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(void)m:(id)a`: docs Metal/MTLRenderPipelineDescriptor/vertexFunction and
// fragmentFunction (their setters), docs
// Metal/MTLRenderCommandEncoder/setRenderPipelineState and docs
// Metal/MTLRenderPassAttachmentDescriptor/texture (its setter).
const MSG_VOID_ID: unsafe extern "C" fn(Id, Sel, Id) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(void)m:(NSUInteger)a`, each an `NSUInteger` property's setter or an
// `NSUInteger` enumeration: docs Metal/MTLTextureDescriptor/pixelFormat, width,
// height, usage and storageMode; docs
// Metal/MTLRenderPipelineColorAttachmentDescriptor/pixelFormat,
// sourceRGBBlendFactor, destinationRGBBlendFactor, sourceAlphaBlendFactor and
// destinationAlphaBlendFactor; docs Metal/MTLRenderPassAttachmentDescriptor/loadAction
// and storeAction.
const MSG_VOID_USIZE: unsafe extern "C" fn(Id, Sel, usize) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(void)setBlendingEnabled:(BOOL)a`: docs
// Metal/MTLRenderPipelineColorAttachmentDescriptor/isBlendingEnabled (its
// setter); `BOOL` is `bool` on Apple silicon.
const MSG_VOID_BOOL: unsafe extern "C" fn(Id, Sel, bool) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(id)newLibraryWithSource:(NSString *)s options:(MTLCompileOptions *)o
// error:(NSError **)e`: docs Metal/MTLDevice/newLibraryWithSource:options:error.
const MSG_ID_ID_ID_OUT: unsafe extern "C" fn(Id, Sel, Id, Id, *mut Id) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(id)newRenderPipelineStateWithDescriptor:(MTLRenderPipelineDescriptor *)d
// error:(NSError **)e`: docs Metal/MTLDevice/newRenderPipelineStateWithDescriptor:error.
const MSG_ID_ID_OUT: unsafe extern "C" fn(Id, Sel, Id, *mut Id) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(id)m:(const void *)p a:(NSUInteger)n b:(NSUInteger)k`: docs
// Metal/MTLDevice/newBufferWithBytes:length:options (`MTLResourceOptions`, an
// `NSUInteger` set) and docs Foundation/NSString/initWithBytes:length:encoding
// (`NSStringEncoding`, an `NSUInteger`).
const MSG_ID_PTR_USIZE_USIZE: unsafe extern "C" fn(Id, Sel, *const c_void, usize, usize) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(id)newBufferWithLength:(NSUInteger)n options:(MTLResourceOptions)o`: docs
// Metal/MTLDevice/newBufferWithLength:options.
const MSG_ID_USIZE_USIZE: unsafe extern "C" fn(Id, Sel, usize, usize) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(id)newTextureWithDescriptor:(MTLTextureDescriptor *)d
// iosurface:(IOSurfaceRef)s plane:(NSUInteger)p`: docs
// Metal/MTLDevice/newTextureWithDescriptor:iosurface:plane (an `IOSurfaceRef` is a
// pointer, passed as `id`).
const MSG_ID_ID_ID_USIZE: unsafe extern "C" fn(Id, Sel, Id, Id, usize) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(id)initWithObjects:(const id [])o forKeys:(const id [])k count:(NSUInteger)n`:
// docs Foundation/NSDictionary/initWithObjects:forKeys:count.
const MSG_ID_IDS_IDS_USIZE: unsafe extern "C" fn(Id, Sel, *const Id, *const Id, usize) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(void)copyFromBuffer:(id)s sourceOffset:(NSUInteger)a toBuffer:(id)d
// destinationOffset:(NSUInteger)b size:(NSUInteger)n`: docs
// Metal/MTLBlitCommandEncoder/copyFromBuffer:sourceOffset:toBuffer:destinationOffset:size.
const MSG_VOID_ID_USIZE_ID_USIZE_USIZE: unsafe extern "C" fn(Id, Sel, Id, usize, Id, usize, usize) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(void)m:(id)b offset:(NSUInteger)o atIndex:(NSUInteger)i`: docs
// Metal/MTLRenderCommandEncoder/setVertexBuffer:offset:atIndex and docs
// Metal/MTLRenderCommandEncoder/setFragmentBuffer:offset:atIndex.
const MSG_VOID_ID_USIZE_USIZE: unsafe extern "C" fn(Id, Sel, Id, usize, usize) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(void)m:(const void *)p length:(NSUInteger)n atIndex:(NSUInteger)i`: docs
// Metal/MTLRenderCommandEncoder/setVertexBytes:length:atIndex and docs
// Metal/MTLRenderCommandEncoder/setFragmentBytes:length:atIndex.
const MSG_VOID_PTR_USIZE_USIZE: unsafe extern "C" fn(Id, Sel, *const c_void, usize, usize) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(void)setScissorRect:(MTLScissorRect)r`: docs
// Metal/MTLRenderCommandEncoder/setScissorRect, the structure by value.
const MSG_VOID_SCISSOR: unsafe extern "C" fn(Id, Sel, ScissorRect) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(void)setClearColor:(MTLClearColor)c`: docs
// Metal/MTLRenderPassColorAttachmentDescriptor/clearColor (its setter), the
// structure by value.
const MSG_VOID_CLEAR: unsafe extern "C" fn(Id, Sel, ClearColor) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(void)drawPrimitives:(MTLPrimitiveType)t vertexStart:(NSUInteger)s
// vertexCount:(NSUInteger)n instanceCount:(NSUInteger)i baseInstance:(NSUInteger)b`:
// docs Metal/MTLRenderCommandEncoder/drawPrimitives:vertexStart:vertexCount:instanceCount:baseInstance
// (`MTLPrimitiveType` is an `NSUInteger` enumeration).
const MSG_VOID_USIZE_USIZE_USIZE_USIZE_USIZE: unsafe extern "C" fn(
    Id,
    Sel,
    usize,
    usize,
    usize,
    usize,
    usize,
) = unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(void)getBytes:(void *)p bytesPerRow:(NSUInteger)r fromRegion:(MTLRegion)g
// mipmapLevel:(NSUInteger)l`: docs
// Metal/MTLTexture/getBytes:bytesPerRow:fromRegion:mipmapLevel, the region by value.
const MSG_VOID_OUT_USIZE_REGION_USIZE: unsafe extern "C" fn(
    Id,
    Sel,
    *mut c_void,
    usize,
    Region,
    usize,
) = unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };

/// A Metal call failed: it returned nil, or a command buffer ended in error. The
/// GPU process ends; this crate decides nothing about it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MetalError {
    /// The method or function, or the check, that failed.
    pub what: &'static str,
    /// A status the API gave, or 0.
    pub code: i64,
}

impl fmt::Display for MetalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Metal: {} failed ({})", self.what, self.code)
    }
}

impl std::error::Error for MetalError {}

fn fail(what: &'static str) -> MetalError {
    MetalError { what, code: 0 }
}

/// The selector named `name`.
fn sel(name: &CStr) -> Sel {
    let p: *const c_char = name.as_ptr();
    // SAFETY: docs ObjectiveC/sel_registerName: takes a NUL-terminated C string and
    // returns its selector, registering it if new; it never returns NULL for a
    // valid string. `p` is the NUL-terminated buffer of `name`, borrowed for the
    // call. The declaration above matches `SEL sel_registerName(const char *)`.
    unsafe { sel_registerName(p) }
}

/// The class named `name`.
fn class(name: &'static CStr) -> Result<Id, MetalError> {
    let p: *const c_char = name.as_ptr();
    // SAFETY: docs ObjectiveC/objc_getClass: takes a NUL-terminated class name and
    // returns the class, or nil if none is registered. `p` is the NUL-terminated
    // buffer of a `'static` string. The declaration above matches
    // `Class objc_getClass(const char *)`. Classes are never released.
    let c = unsafe { objc_getClass(p) };
    if c.is_null() {
        return Err(fail("objc_getClass"));
    }
    Ok(c)
}

/// An object this process owns one reference to.
#[derive(Debug)]
struct Object(NonNull<c_void>);

impl Object {
    /// Take an owned reference (+1), as `alloc`, `new…` and `init…` give; nil is
    /// an error.
    fn owned(p: Id, what: &'static str) -> Result<Object, MetalError> {
        NonNull::new(p).map(Object).ok_or(fail(what))
    }

    /// Retain an object an autoreleasing method gave, so it is owned; nil is an
    /// error.
    fn retained(p: Id, what: &'static str) -> Result<Object, MetalError> {
        let o = NonNull::new(p).ok_or(fail(what))?;
        let s = sel(c"retain");
        let o_id: Id = o.as_ptr();
        // SAFETY: docs ObjectiveC/NSObject/retain: `(instancetype)retain`, which
        // adds one reference and returns the receiver. `o` is a live object just
        // returned by Metal or Foundation, and MSG_ID is `(id, SEL) -> id`.
        let r = unsafe { MSG_ID(o_id, s) };
        Object::owned(r, what)
    }

    fn ptr(&self) -> Id {
        self.0.as_ptr()
    }
}

impl Drop for Object {
    fn drop(&mut self) {
        let s = sel(c"release");
        let this_id: Id = self.ptr();
        // SAFETY: docs ObjectiveC/NSObject/release: `(oneway void)release` gives up
        // one reference. An `Object` holds exactly one, taken once and given up
        // here once, and MSG_VOID is `(id, SEL) -> void`.
        unsafe { MSG_VOID(this_id, s) }
    }
}

/// `[[class alloc] init]`: a new owned object.
fn new_object(name: &'static CStr) -> Result<Object, MetalError> {
    let c = class(name)?;
    let s_alloc = sel(c"alloc");
    // SAFETY: docs ObjectiveC/NSObject/alloc: `+(instancetype)alloc`, sent to a
    // class, returns an uninitialised owned instance or nil. `c` is a class from
    // objc_getClass; MSG_ID is `(id, SEL) -> id`.
    let a = unsafe { MSG_ID(c, s_alloc) };
    if a.is_null() {
        return Err(fail("alloc"));
    }
    let s_init = sel(c"init");
    // SAFETY: docs ObjectiveC/NSObject/init: `-(instancetype)init` consumes the
    // allocated instance and returns the initialised one (owned) or nil. `a` is the
    // instance `alloc` just returned and is used no more; MSG_ID is
    // `(id, SEL) -> id`.
    let o = unsafe { MSG_ID(a, s_init) };
    Object::owned(o, "init")
}

/// An owned `NSString` holding `text`.
fn ns_string(text: &str) -> Result<Object, MetalError> {
    let c = class(c"NSString")?;
    let s_alloc = sel(c"alloc");
    // SAFETY: docs ObjectiveC/NSObject/alloc, as in `new_object`.
    let a = unsafe { MSG_ID(c, s_alloc) };
    if a.is_null() {
        return Err(fail("alloc"));
    }
    let bytes: *const c_void = text.as_ptr().cast();
    let len = text.len();
    let s_init = sel(c"initWithBytes:length:encoding:");
    // SAFETY: docs Foundation/NSString/initWithBytes:length:encoding: reads `len`
    // bytes at `bytes` in the given encoding (NSUTF8StringEncoding, 4) and returns
    // an owned string or nil; it copies them. `bytes` and `len` are the pointer and
    // length of `text`, valid UTF-8 borrowed for the call. `a` is the instance
    // `alloc` returned; MSG_ID_PTR_USIZE_USIZE is `(id, SEL, const void *,
    // NSUInteger, NSUInteger) -> id`.
    let o = unsafe { MSG_ID_PTR_USIZE_USIZE(a, s_init, bytes, len, 4) };
    Object::owned(o, "initWithBytes:length:encoding:")
}

/// An owned `NSNumber` holding `value`.
fn ns_number(value: usize) -> Result<Object, MetalError> {
    let c = class(c"NSNumber")?;
    let s_alloc = sel(c"alloc");
    // SAFETY: docs ObjectiveC/NSObject/alloc, as in `new_object`.
    let a = unsafe { MSG_ID(c, s_alloc) };
    if a.is_null() {
        return Err(fail("alloc"));
    }
    let s_init = sel(c"initWithUnsignedLong:");
    // SAFETY: docs Foundation/NSNumber/initWithUnsignedLong: returns an owned
    // number or nil. `a` is the instance `alloc` returned; MSG_ID_USIZE is
    // `(id, SEL, NSUInteger) -> id`, and `unsigned long` is 64 bits like `usize`.
    let o = unsafe { MSG_ID_USIZE(a, s_init, value) };
    Object::owned(o, "initWithUnsignedLong:")
}

/// Run `f` inside an autorelease pool, which is drained when it returns. Objects
/// the wrappers hold are owned, so draining frees only what autoreleasing methods
/// left behind.
pub fn with_autorelease_pool<R>(f: impl FnOnce() -> R) -> Result<R, MetalError> {
    struct Pool(Id);
    impl Drop for Pool {
        fn drop(&mut self) {
            let s = sel(c"drain");
            // SAFETY: docs Foundation/NSAutoreleasePool/drain: releases the pool's
            // objects and the pool itself (it is not also released). `self.0` is the
            // pool `init` returned, drained once, here, on the thread that made it,
            // after every pool made inside `f` (each is scoped by this function).
            unsafe { MSG_VOID(self.0, s) }
        }
    }
    let c = class(c"NSAutoreleasePool")?;
    let s_alloc = sel(c"alloc");
    // SAFETY: docs ObjectiveC/NSObject/alloc, as in `new_object`.
    let a = unsafe { MSG_ID(c, s_alloc) };
    if a.is_null() {
        return Err(fail("alloc"));
    }
    let s_init = sel(c"init");
    // SAFETY: docs ObjectiveC/NSObject/init on an NSAutoreleasePool instance just
    // allocated; MSG_ID is `(id, SEL) -> id`.
    let p = unsafe { MSG_ID(a, s_init) };
    if p.is_null() {
        return Err(fail("NSAutoreleasePool init"));
    }
    let pool = Pool(p);
    let out = f();
    drop(pool);
    Ok(out)
}

/// `MTLPixelFormat`: the formats this crate makes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PixelFormat {
    /// `MTLPixelFormatRGBA8Unorm`, 70.
    Rgba8Unorm,
}

impl PixelFormat {
    fn raw(self) -> usize {
        match self {
            PixelFormat::Rgba8Unorm => 70,
        }
    }
}

/// `MTLBlendFactor`: the factors a pipeline may use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlendFactor {
    /// `MTLBlendFactorOne`, 1.
    One,
    /// `MTLBlendFactorOneMinusSourceAlpha`, 5.
    OneMinusSourceAlpha,
}

impl BlendFactor {
    fn raw(self) -> usize {
        match self {
            BlendFactor::One => 1,
            BlendFactor::OneMinusSourceAlpha => 5,
        }
    }
}

/// How a pipeline writes its one colour attachment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PipelineDesc<'a> {
    /// Metal Shading Language source.
    pub source: &'a str,
    /// The vertex function's name in it.
    pub vertex: &'a str,
    /// The fragment function's name in it.
    pub fragment: &'a str,
    /// The attachment's format.
    pub format: PixelFormat,
    /// Blending, source and destination factors for colour and alpha alike, or
    /// none.
    pub blend: Option<(BlendFactor, BlendFactor)>,
}

/// A GPU (`id<MTLDevice>`).
#[derive(Debug)]
pub struct Device(Object);

/// A command queue (`id<MTLCommandQueue>`).
#[derive(Debug)]
pub struct CommandQueue(Object);

/// A compiled render pipeline (`id<MTLRenderPipelineState>`).
#[derive(Debug)]
pub struct Pipeline(Object);

/// A buffer in shared storage (`id<MTLBuffer>`) and its length.
#[derive(Debug)]
pub struct Buffer {
    obj: Object,
    len: usize,
}

impl Buffer {
    /// Its length in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    /// It has no bytes (never: buffers are at least one byte).
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// The largest side of a surface or texture: 16,384, the limit of every Apple
/// silicon GPU (Metal feature set tables, "Maximum 2D texture width and height").
pub const MAX_SIDE: usize = 16_384;

/// An IOSurface of RGBA8 pixels, owned.
#[derive(Debug)]
pub struct Surface {
    ptr: NonNull<c_void>,
    width: usize,
    height: usize,
}

impl Drop for Surface {
    fn drop(&mut self) {
        let p: Id = self.ptr.as_ptr();
        // SAFETY: docs CoreFoundation/CFRelease: releases one reference; `cf` must
        // not be NULL. `p` is the surface IOSurfaceCreate returned (owned, the
        // Create rule), released once, here.
        unsafe { CFRelease(p) }
    }
}

impl Surface {
    /// A new surface of `width` × `height` RGBA8 pixels (`'RGBA'`, 4 bytes each),
    /// each side 1 to [`MAX_SIDE`].
    pub fn new(width: usize, height: usize) -> Result<Surface, MetalError> {
        if !(1..=MAX_SIDE).contains(&width) || !(1..=MAX_SIDE).contains(&height) {
            return Err(fail("surface size"));
        }
        let keys = [
            ns_string("IOSurfaceWidth")?,
            ns_string("IOSurfaceHeight")?,
            ns_string("IOSurfaceBytesPerElement")?,
            ns_string("IOSurfacePixelFormat")?,
        ];
        // 'RGBA' as a four-character code.
        let values = [
            ns_number(width)?,
            ns_number(height)?,
            ns_number(4)?,
            ns_number(0x5247_4241)?,
        ];
        let key_ptrs: [Id; 4] = [keys[0].ptr(), keys[1].ptr(), keys[2].ptr(), keys[3].ptr()];
        let value_ptrs: [Id; 4] = [
            values[0].ptr(),
            values[1].ptr(),
            values[2].ptr(),
            values[3].ptr(),
        ];
        let c = class(c"NSDictionary")?;
        let s_alloc = sel(c"alloc");
        // SAFETY: docs ObjectiveC/NSObject/alloc, as in `new_object`.
        let a = unsafe { MSG_ID(c, s_alloc) };
        if a.is_null() {
            return Err(fail("alloc"));
        }
        let ks: *const Id = key_ptrs.as_ptr();
        let vs: *const Id = value_ptrs.as_ptr();
        let s_init = sel(c"initWithObjects:forKeys:count:");
        // SAFETY: docs Foundation/NSDictionary/initWithObjects:forKeys:count: reads
        // `count` objects and `count` keys from the two C arrays, retains them, and
        // returns an owned dictionary or nil. `vs` and `ks` point to two live local
        // arrays of 4 non-nil objects each (owned by `values` and `keys`, which
        // outlive the call), and `count` is 4. MSG_ID_IDS_IDS_USIZE is `(id, SEL,
        // const id *, const id *, NSUInteger) -> id`.
        let d = unsafe { MSG_ID_IDS_IDS_USIZE(a, s_init, vs, ks, 4) };
        let dict = Object::owned(d, "initWithObjects:forKeys:count:")?;
        let props: Id = dict.ptr();
        // SAFETY: docs IOSurface/IOSurfaceCreate: takes a dictionary of properties
        // (an NSDictionary is toll-free bridged to CFDictionaryRef) and returns an
        // owned surface or NULL. `props` is the live dictionary `dict` holds for the
        // whole call.
        let p = unsafe { IOSurfaceCreate(props) };
        let ptr = NonNull::new(p).ok_or(fail("IOSurfaceCreate"))?;
        Ok(Surface { ptr, width, height })
    }

    /// Its width in pixels.
    pub fn width(&self) -> usize {
        self.width
    }

    /// Its height in pixels.
    pub fn height(&self) -> usize {
        self.height
    }
}

/// An RGBA8 texture on a [`Surface`] (`id<MTLTexture>`), usable as a render target.
#[derive(Debug)]
pub struct Texture {
    obj: Object,
    width: usize,
    height: usize,
}

impl Texture {
    /// Its width in pixels.
    pub fn width(&self) -> usize {
        self.width
    }

    /// Its height in pixels.
    pub fn height(&self) -> usize {
        self.height
    }

    /// Copy every pixel out, rows from the top, 4 bytes each, packed. `out` must
    /// be exactly `width × height × 4` bytes. Call it after the command buffer that
    /// drew it has completed.
    pub fn read_pixels(&self, out: &mut [u8]) -> Result<(), MetalError> {
        let row = self.width.checked_mul(4).ok_or(fail("row"))?;
        let total = row.checked_mul(self.height).ok_or(fail("size"))?;
        if out.len() != total {
            return Err(fail("read_pixels length"));
        }
        let region = Region {
            origin: Origin { x: 0, y: 0, z: 0 },
            size: Size {
                width: self.width,
                height: self.height,
                depth: 1,
            },
        };
        let dst: *mut c_void = out.as_mut_ptr().cast();
        let s = sel(c"getBytes:bytesPerRow:fromRegion:mipmapLevel:");
        let this_id: Id = self.obj.ptr();
        // SAFETY: docs Metal/MTLTexture/getBytes:bytesPerRow:fromRegion:mipmapLevel:
        // copies the region into `pixelBytes`, `bytesPerRow` apart; the texture's
        // storage is shared, so the CPU may read it. The region is the whole
        // texture at level 0, and `dst` is the start of `out`, mutably borrowed for
        // the call, whose length was checked to be exactly `height` rows of `row`
        // bytes. MSG_VOID_OUT_USIZE_REGION_USIZE is `(id, SEL, void *, NSUInteger,
        // MTLRegion, NSUInteger) -> void`.
        unsafe { MSG_VOID_OUT_USIZE_REGION_USIZE(this_id, s, dst, row, region, 0) }
        Ok(())
    }
}

/// `MTLResourceStorageModeShared`, as a resource option: 0.
const STORAGE_SHARED: usize = 0;

impl Device {
    /// The system's default GPU.
    pub fn system_default() -> Result<Device, MetalError> {
        // SAFETY: docs Metal/MTLCreateSystemDefaultDevice: no arguments; returns an
        // owned device or nil when there is no GPU.
        let d = unsafe { MTLCreateSystemDefaultDevice() };
        Object::owned(d, "MTLCreateSystemDefaultDevice").map(Device)
    }

    /// A command queue.
    pub fn new_command_queue(&self) -> Result<CommandQueue, MetalError> {
        let s = sel(c"newCommandQueue");
        let this_id: Id = self.0.ptr();
        // SAFETY: docs Metal/MTLDevice/newCommandQueue: returns an owned queue or
        // nil. `self` holds a live device; MSG_ID is `(id, SEL) -> id`.
        let q = unsafe { MSG_ID(this_id, s) };
        Object::owned(q, "newCommandQueue").map(CommandQueue)
    }

    /// A buffer in shared storage holding a copy of `bytes`, which must not be
    /// empty.
    pub fn new_buffer_with_bytes(&self, bytes: &[u8]) -> Result<Buffer, MetalError> {
        if bytes.is_empty() {
            return Err(fail("empty buffer"));
        }
        let p: *const c_void = bytes.as_ptr().cast();
        let len = bytes.len();
        let s = sel(c"newBufferWithBytes:length:options:");
        let this_id: Id = self.0.ptr();
        // SAFETY: docs Metal/MTLDevice/newBufferWithBytes:length:options: copies
        // `length` bytes from `pointer` into a new buffer and returns it (owned) or
        // nil. `p` and `len` are the pointer and length of `bytes`, borrowed for
        // the call, and not zero. MSG_ID_PTR_USIZE_USIZE is `(id, SEL, const void *,
        // NSUInteger, NSUInteger) -> id`.
        let b = unsafe { MSG_ID_PTR_USIZE_USIZE(this_id, s, p, len, STORAGE_SHARED) };
        Object::owned(b, "newBufferWithBytes:length:options:").map(|obj| Buffer { obj, len })
    }

    /// A buffer in shared storage of `len` bytes, not zero, whose contents start
    /// undefined but initialised (Metal zeroes new buffers).
    pub fn new_buffer(&self, len: usize) -> Result<Buffer, MetalError> {
        if len == 0 {
            return Err(fail("empty buffer"));
        }
        let s = sel(c"newBufferWithLength:options:");
        let this_id: Id = self.0.ptr();
        // SAFETY: docs Metal/MTLDevice/newBufferWithLength:options: returns an owned
        // buffer of `length` bytes or nil; nothing is read from the CPU.
        // MSG_ID_USIZE_USIZE is `(id, SEL, NSUInteger, NSUInteger) -> id`.
        let b = unsafe { MSG_ID_USIZE_USIZE(this_id, s, len, STORAGE_SHARED) };
        Object::owned(b, "newBufferWithLength:options:").map(|obj| Buffer { obj, len })
    }

    /// An RGBA8 texture on `surface`, in shared storage, usable as a render target
    /// and by shaders.
    pub fn new_texture_on(&self, surface: &Surface) -> Result<Texture, MetalError> {
        let desc = new_object(c"MTLTextureDescriptor")?;
        // MTLTextureUsageShaderRead (1) | MTLTextureUsageRenderTarget (4).
        let settings: [(&CStr, usize); 5] = [
            (c"setPixelFormat:", PixelFormat::Rgba8Unorm.raw()),
            (c"setWidth:", surface.width),
            (c"setHeight:", surface.height),
            (c"setUsage:", 5),
            (c"setStorageMode:", STORAGE_SHARED),
        ];
        for (name, value) in settings {
            let s = sel(name);
            let desc_id: Id = desc.ptr();
            // SAFETY: docs Metal/MTLTextureDescriptor/pixelFormat, width, height,
            // usage and storageMode: each setter takes an `NSUInteger` (or an
            // `NSUInteger` enumeration) and returns nothing. `desc` is a live
            // descriptor; MSG_VOID_USIZE is `(id, SEL, NSUInteger) -> void`.
            unsafe { MSG_VOID_USIZE(desc_id, s, value) }
        }
        let surf: Id = surface.ptr.as_ptr();
        let s = sel(c"newTextureWithDescriptor:iosurface:plane:");
        let this_id: Id = self.0.ptr();
        let desc_id: Id = desc.ptr();
        // SAFETY: docs Metal/MTLDevice/newTextureWithDescriptor:iosurface:plane:
        // returns an owned texture backed by the surface, or nil (for instance if
        // the descriptor does not fit the surface). `desc` and `surf` are live for
        // the call, and the texture retains the surface. Plane 0 is the only plane
        // of a non-planar surface. MSG_ID_ID_ID_USIZE is `(id, SEL, id, id,
        // NSUInteger) -> id`.
        let t = unsafe { MSG_ID_ID_ID_USIZE(this_id, s, desc_id, surf, 0) };
        let obj = Object::owned(t, "newTextureWithDescriptor:iosurface:plane:")?;
        Ok(Texture {
            obj,
            width: surface.width,
            height: surface.height,
        })
    }

    /// Compile `desc.source` and make a render pipeline from two of its functions,
    /// writing one colour attachment.
    pub fn new_pipeline(&self, desc: &PipelineDesc<'_>) -> Result<Pipeline, MetalError> {
        let source = ns_string(desc.source)?;
        let mut error: Id = std::ptr::null_mut();
        let error_slot: *mut Id = &raw mut error;
        let nil: Id = std::ptr::null_mut();
        let s = sel(c"newLibraryWithSource:options:error:");
        let this_id: Id = self.0.ptr();
        let source_id: Id = source.ptr();
        // SAFETY: docs Metal/MTLDevice/newLibraryWithSource:options:error: compiles
        // the source and returns an owned library, or nil and an autoreleased
        // NSError in `*error`. `source` is a live NSString, the options are nil
        // (the defaults), and `error_slot` points to the live local `error`.
        // MSG_ID_ID_ID_OUT is `(id, SEL, id, id, id *) -> id`.
        let l = unsafe { MSG_ID_ID_ID_OUT(this_id, s, source_id, nil, error_slot) };
        let library = Object::owned(l, "newLibraryWithSource:options:error:")?;
        let function = |name: &str, what: &'static str| -> Result<Object, MetalError> {
            let n = ns_string(name)?;
            let s = sel(c"newFunctionWithName:");
            let library_id: Id = library.ptr();
            let n_id: Id = n.ptr();
            // SAFETY: docs Metal/MTLLibrary/newFunctionWithName: returns an owned
            // function or nil. `library` and `n` are live; MSG_ID_ID is `(id, SEL,
            // id) -> id`.
            let f = unsafe { MSG_ID_ID(library_id, s, n_id) };
            Object::owned(f, what)
        };
        let vertex = function(desc.vertex, "newFunctionWithName: (vertex)")?;
        let fragment = function(desc.fragment, "newFunctionWithName: (fragment)")?;
        let pd = new_object(c"MTLRenderPipelineDescriptor")?;
        for (name, f) in [
            (c"setVertexFunction:", &vertex),
            (c"setFragmentFunction:", &fragment),
        ] {
            let s = sel(name);
            let pd_id: Id = pd.ptr();
            let f_id: Id = f.ptr();
            // SAFETY: docs Metal/MTLRenderPipelineDescriptor/vertexFunction and
            // fragmentFunction: setters taking a function (retained by the
            // descriptor). `pd` and `f` are live; MSG_VOID_ID is `(id, SEL, id) ->
            // void`.
            unsafe { MSG_VOID_ID(pd_id, s, f_id) }
        }
        let attachment = colour_attachment(&pd)?;
        let s = sel(c"setPixelFormat:");
        let format_raw: usize = desc.format.raw();
        // SAFETY: docs Metal/MTLRenderPipelineColorAttachmentDescriptor/pixelFormat:
        // a setter taking an `NSUInteger` enumeration. `attachment` is attachment 0
        // of the live descriptor `pd`, which owns it; MSG_VOID_USIZE is `(id, SEL,
        // NSUInteger) -> void`.
        unsafe { MSG_VOID_USIZE(attachment, s, format_raw) }
        if let Some((src, dst)) = desc.blend {
            let s = sel(c"setBlendingEnabled:");
            // SAFETY: docs Metal/MTLRenderPipelineColorAttachmentDescriptor/isBlendingEnabled:
            // a
            // setter taking a `BOOL`; `attachment` is live as above; MSG_VOID_BOOL
            // is `(id, SEL, BOOL) -> void`.
            unsafe { MSG_VOID_BOOL(attachment, s, true) }
            for (name, factor) in [
                (c"setSourceRGBBlendFactor:", src),
                (c"setDestinationRGBBlendFactor:", dst),
                (c"setSourceAlphaBlendFactor:", src),
                (c"setDestinationAlphaBlendFactor:", dst),
            ] {
                let s = sel(name);
                let factor_raw: usize = factor.raw();
                // SAFETY: docs Metal/MTLRenderPipelineColorAttachmentDescriptor/sourceRGBBlendFactor
                //
                // and its three siblings: setters taking an `MTLBlendFactor`
                // (`NSUInteger`). `attachment` is live as above.
                unsafe { MSG_VOID_USIZE(attachment, s, factor_raw) }
            }
        }
        let mut error: Id = std::ptr::null_mut();
        let error_slot: *mut Id = &raw mut error;
        let s = sel(c"newRenderPipelineStateWithDescriptor:error:");
        let this_id: Id = self.0.ptr();
        let pd_id: Id = pd.ptr();
        // SAFETY: docs Metal/MTLDevice/newRenderPipelineStateWithDescriptor:error:
        // returns an owned pipeline state, or nil and an autoreleased NSError in
        // `*error`. `pd` is live and `error_slot` points to the live local `error`.
        // MSG_ID_ID_OUT is `(id, SEL, id, id *) -> id`.
        let p = unsafe { MSG_ID_ID_OUT(this_id, s, pd_id, error_slot) };
        Object::owned(p, "newRenderPipelineStateWithDescriptor:error:").map(Pipeline)
    }
}

/// Colour attachment 0 of a render pipeline or render pass descriptor, borrowed
/// from it: valid while the descriptor lives.
fn colour_attachment(descriptor: &Object) -> Result<Id, MetalError> {
    let s = sel(c"colorAttachments");
    let descriptor_id: Id = descriptor.ptr();
    // SAFETY: docs Metal/MTLRenderPipelineDescriptor/colorAttachments and docs Metal/MTLRenderPassDescriptor/colorAttachments:
    // a property returning the
    // descriptor's array (not owned by the caller). `descriptor` is live; MSG_ID is
    // `(id, SEL) -> id`.
    let array = unsafe { MSG_ID(descriptor_id, s) };
    if array.is_null() {
        return Err(fail("colorAttachments"));
    }
    let s = sel(c"objectAtIndexedSubscript:");
    // SAFETY: docs Metal/MTLRenderPipelineColorAttachmentDescriptorArray/objectAtIndexedSubscript
    //
    // and docs Metal/MTLRenderPassColorAttachmentDescriptorArray/objectAtIndexedSubscript:
    // return attachment `index`, which the array keeps; index 0 always exists.
    // MSG_ID_USIZE is `(id, SEL, NSUInteger) -> id`.
    let a = unsafe { MSG_ID_USIZE(array, s, 0) };
    if a.is_null() {
        return Err(fail("objectAtIndexedSubscript:"));
    }
    Ok(a)
}

/// `MTLCommandBufferStatusCompleted`.
const STATUS_COMPLETED: usize = 4;

impl CommandQueue {
    /// A new command buffer.
    pub fn command_buffer(&self) -> Result<CommandBuffer, MetalError> {
        let s = sel(c"commandBuffer");
        let this_id: Id = self.0.ptr();
        // SAFETY: docs Metal/MTLCommandQueue/commandBuffer: returns an autoreleased
        // command buffer (retained below) or nil. `self` holds a live queue; MSG_ID
        // is `(id, SEL) -> id`.
        let b = unsafe { MSG_ID(this_id, s) };
        Object::retained(b, "commandBuffer").map(CommandBuffer)
    }
}

/// A command buffer (`id<MTLCommandBuffer>`). Encoders are opened and ended inside
/// its methods, so none is open when it is committed.
#[derive(Debug)]
pub struct CommandBuffer(Object);

/// Which shader stage a buffer or bytes are bound for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    /// The vertex function.
    Vertex,
    /// The fragment function.
    Fragment,
}

/// The highest buffer index a stage has: Metal's limit is 31 buffer slots.
const MAX_BUFFER_INDEX: usize = 30;

/// The most bytes `setVertexBytes:` and `setFragmentBytes:` take (4 KB, their
/// documentation).
const MAX_INLINE_BYTES: usize = 4096;

impl CommandBuffer {
    /// Copy `len` bytes from `src` at `src_offset` to `dst` at `dst_offset`, after
    /// everything encoded so far. Offsets and `len` must be multiples of 4 (macOS),
    /// `len` not zero, and both ranges inside their buffers.
    pub fn copy_buffer(
        &mut self,
        src: &Buffer,
        src_offset: usize,
        dst: &Buffer,
        dst_offset: usize,
        len: usize,
    ) -> Result<(), MetalError> {
        let inside = |offset: usize, buffer: &Buffer| {
            offset.checked_add(len).is_some_and(|end| end <= buffer.len)
        };
        if len == 0
            || !src_offset.is_multiple_of(4)
            || !dst_offset.is_multiple_of(4)
            || !len.is_multiple_of(4)
            || !inside(src_offset, src)
            || !inside(dst_offset, dst)
        {
            return Err(fail("copy_buffer range"));
        }
        let s = sel(c"blitCommandEncoder");
        let this_id: Id = self.0.ptr();
        // SAFETY: docs Metal/MTLCommandBuffer/blitCommandEncoder: returns an
        // autoreleased encoder (retained below) or nil. No other encoder of this
        // buffer is open: every method here ends its own. MSG_ID is `(id, SEL) ->
        // id`.
        let e = unsafe { MSG_ID(this_id, s) };
        let encoder = Object::retained(e, "blitCommandEncoder")?;
        let s = sel(c"copyFromBuffer:sourceOffset:toBuffer:destinationOffset:size:");
        let encoder_id: Id = encoder.ptr();
        let src_id: Id = src.obj.ptr();
        let dst_id: Id = dst.obj.ptr();
        // SAFETY: docs Metal/MTLBlitCommandEncoder/copyFromBuffer:sourceOffset:toBuffer:destinationOffset:size:
        //
        // encodes a GPU copy; on macOS the offsets and size must be multiples of 4,
        // and both ranges must lie inside their buffers, as checked above. The
        // command buffer keeps both buffers alive until it completes.
        // MSG_VOID_ID_USIZE_ID_USIZE_USIZE is `(id, SEL, id, NSUInteger, id,
        // NSUInteger, NSUInteger) -> void`.
        unsafe {
            MSG_VOID_ID_USIZE_ID_USIZE_USIZE(
                encoder_id, s, src_id, src_offset, dst_id, dst_offset, len,
            )
        }
        end_encoding(&encoder);
        Ok(())
    }

    /// Encode a render pass into `target`, cleared to `clear` (red, green, blue,
    /// alpha, 0 to 1) or, with `None`, keeping what it holds; `f` encodes the
    /// pass's commands, and the pass is ended whatever `f` returns.
    pub fn render<R>(
        &mut self,
        target: &Texture,
        clear: Option<[f64; 4]>,
        f: impl FnOnce(&mut RenderEncoder<'_>) -> Result<R, MetalError>,
    ) -> Result<R, MetalError> {
        let c = class(c"MTLRenderPassDescriptor")?;
        let s = sel(c"renderPassDescriptor");
        // SAFETY: docs Metal/MTLRenderPassDescriptor/renderPassDescriptor: a class
        // method returning an autoreleased descriptor (retained below) or nil. `c`
        // is the class; MSG_ID is `(id, SEL) -> id`.
        let d = unsafe { MSG_ID(c, s) };
        let pass = Object::retained(d, "renderPassDescriptor")?;
        let attachment = colour_attachment(&pass)?;
        let s = sel(c"setTexture:");
        let target_id: Id = target.obj.ptr();
        // SAFETY: docs Metal/MTLRenderPassAttachmentDescriptor/texture: a setter
        // taking the texture to render into (retained by the descriptor).
        // `attachment` is attachment 0 of the live `pass`; `target` is live;
        // MSG_VOID_ID is `(id, SEL, id) -> void`.
        unsafe { MSG_VOID_ID(attachment, s, target_id) }
        // MTLLoadActionLoad (1) or MTLLoadActionClear (2); MTLStoreActionStore (1).
        let load = if clear.is_some() { 2 } else { 1 };
        for (name, value) in [(c"setLoadAction:", load), (c"setStoreAction:", 1)] {
            let s = sel(name);
            // SAFETY: docs Metal/MTLRenderPassAttachmentDescriptor/loadAction and
            // storeAction: setters taking an `NSUInteger` enumeration. `attachment`
            // is live as above; MSG_VOID_USIZE is `(id, SEL, NSUInteger) -> void`.
            unsafe { MSG_VOID_USIZE(attachment, s, value) }
        }
        if let Some([red, green, blue, alpha]) = clear {
            let colour = ClearColor {
                red,
                green,
                blue,
                alpha,
            };
            let s = sel(c"setClearColor:");
            // SAFETY: docs Metal/MTLRenderPassColorAttachmentDescriptor/clearColor:
            // a setter taking an `MTLClearColor` by value. `attachment` is live as
            // above; MSG_VOID_CLEAR is `(id, SEL, MTLClearColor) -> void`.
            unsafe { MSG_VOID_CLEAR(attachment, s, colour) }
        }
        let s = sel(c"renderCommandEncoderWithDescriptor:");
        let this_id: Id = self.0.ptr();
        let pass_id: Id = pass.ptr();
        // SAFETY: docs Metal/MTLCommandBuffer/renderCommandEncoderWithDescriptor:
        // returns an autoreleased encoder (retained below) or nil. `pass` is live
        // and no other encoder of this buffer is open. MSG_ID_ID is `(id, SEL, id)
        // -> id`.
        let e = unsafe { MSG_ID_ID(this_id, s, pass_id) };
        let encoder = Object::retained(e, "renderCommandEncoderWithDescriptor:")?;
        let mut scoped = RenderEncoder {
            obj: &encoder,
            width: target.width,
            height: target.height,
        };
        let out = f(&mut scoped);
        end_encoding(&encoder);
        out
    }

    /// Commit, wait until the GPU has finished, and report its status.
    pub fn commit_and_wait(self) -> Result<(), MetalError> {
        for name in [c"commit", c"waitUntilCompleted"] {
            let s = sel(name);
            let this_id: Id = self.0.ptr();
            // SAFETY: docs Metal/MTLCommandBuffer/commit and waitUntilCompleted:
            // take nothing and return nothing; commit is sent once (this method
            // takes the buffer by value) and every encoder was ended by the method
            // that opened it. MSG_VOID is `(id, SEL) -> void`.
            unsafe { MSG_VOID(this_id, s) }
        }
        let s = sel(c"status");
        let this_id: Id = self.0.ptr();
        // SAFETY: docs Metal/MTLCommandBuffer/status: returns an
        // `MTLCommandBufferStatus` (`NSUInteger`). MSG_USIZE is `(id, SEL) ->
        // NSUInteger`.
        let status = unsafe { MSG_USIZE(this_id, s) };
        if status == STATUS_COMPLETED {
            Ok(())
        } else {
            Err(MetalError {
                what: "command buffer status",
                code: i64::try_from(status).unwrap_or(-1),
            })
        }
    }
}

/// End an encoder.
fn end_encoding(encoder: &Object) {
    let s = sel(c"endEncoding");
    let encoder_id: Id = encoder.ptr();
    // SAFETY: docs Metal/MTLCommandEncoder/endEncoding: ends the encoder; called
    // once per encoder, by the method that opened it. MSG_VOID is `(id, SEL) ->
    // void`.
    unsafe { MSG_VOID(encoder_id, s) }
}

/// An open render pass, inside [`CommandBuffer::render`].
#[derive(Debug)]
pub struct RenderEncoder<'a> {
    obj: &'a Object,
    width: usize,
    height: usize,
}

impl RenderEncoder<'_> {
    /// Draw with `pipeline` from now on.
    pub fn set_pipeline(&mut self, pipeline: &Pipeline) {
        let s = sel(c"setRenderPipelineState:");
        let this_id: Id = self.obj.ptr();
        let pipeline_id: Id = pipeline.0.ptr();
        // SAFETY: docs Metal/MTLRenderCommandEncoder/setRenderPipelineState: takes a
        // pipeline state, which the command buffer keeps alive. Both are live;
        // MSG_VOID_ID is `(id, SEL, id) -> void`.
        unsafe { MSG_VOID_ID(this_id, s, pipeline_id) }
    }

    /// Bind `buffer` from its start at `index` (0 to 30) for `stage`.
    pub fn set_buffer(
        &mut self,
        stage: Stage,
        buffer: &Buffer,
        index: usize,
    ) -> Result<(), MetalError> {
        if index > MAX_BUFFER_INDEX {
            return Err(fail("buffer index"));
        }
        let s = match stage {
            Stage::Vertex => sel(c"setVertexBuffer:offset:atIndex:"),
            Stage::Fragment => sel(c"setFragmentBuffer:offset:atIndex:"),
        };
        let this_id: Id = self.obj.ptr();
        let buffer_id: Id = buffer.obj.ptr();
        // SAFETY: docs Metal/MTLRenderCommandEncoder/setVertexBuffer:offset:atIndex
        // and setFragmentBuffer:offset:atIndex: bind a buffer at an offset within
        // it (0 here) to a slot below 31 (checked); the command buffer keeps the
        // buffer alive. MSG_VOID_ID_USIZE_USIZE is `(id, SEL, id, NSUInteger,
        // NSUInteger) -> void`.
        unsafe { MSG_VOID_ID_USIZE_USIZE(this_id, s, buffer_id, 0, index) }
        Ok(())
    }

    /// Copy `bytes` (1 to 4096) into the pass at `index` (0 to 30) for `stage`.
    pub fn set_bytes(
        &mut self,
        stage: Stage,
        bytes: &[u8],
        index: usize,
    ) -> Result<(), MetalError> {
        if index > MAX_BUFFER_INDEX || bytes.is_empty() || bytes.len() > MAX_INLINE_BYTES {
            return Err(fail("set_bytes"));
        }
        let p: *const c_void = bytes.as_ptr().cast();
        let len = bytes.len();
        let s = match stage {
            Stage::Vertex => sel(c"setVertexBytes:length:atIndex:"),
            Stage::Fragment => sel(c"setFragmentBytes:length:atIndex:"),
        };
        let this_id: Id = self.obj.ptr();
        // SAFETY: docs Metal/MTLRenderCommandEncoder/setVertexBytes:length:atIndex
        // and setFragmentBytes:length:atIndex: copy `length` bytes (at most 4 KB,
        // checked) from `bytes` at call time. `p` and `len` are the pointer and
        // length of the borrowed slice. MSG_VOID_PTR_USIZE_USIZE is `(id, SEL,
        // const void *, NSUInteger, NSUInteger) -> void`.
        unsafe { MSG_VOID_PTR_USIZE_USIZE(this_id, s, p, len, index) }
        Ok(())
    }

    /// Draw only inside the rectangle at (`x`, `y`) of `width` × `height` pixels,
    /// which must be inside the target and not empty.
    pub fn set_scissor(
        &mut self,
        x: usize,
        y: usize,
        width: usize,
        height: usize,
    ) -> Result<(), MetalError> {
        let fits = |at: usize, len: usize, max: usize| {
            len > 0 && at.checked_add(len).is_some_and(|end| end <= max)
        };
        if !fits(x, width, self.width) || !fits(y, height, self.height) {
            return Err(fail("scissor rectangle"));
        }
        let rect = ScissorRect {
            x,
            y,
            width,
            height,
        };
        let s = sel(c"setScissorRect:");
        let this_id: Id = self.obj.ptr();
        // SAFETY: docs Metal/MTLRenderCommandEncoder/setScissorRect: the rectangle
        // must lie within the render target, as checked above against the target's
        // size. MSG_VOID_SCISSOR is `(id, SEL, MTLScissorRect) -> void`.
        unsafe { MSG_VOID_SCISSOR(this_id, s, rect) }
        Ok(())
    }

    /// Draw `instance_count` instances of `vertex_count` vertices as triangles,
    /// instances numbered from `base_instance`. What the shaders read for them is
    /// bounded by the shaders.
    pub fn draw_triangles(
        &mut self,
        vertex_count: usize,
        instance_count: usize,
        base_instance: usize,
    ) {
        let s = sel(c"drawPrimitives:vertexStart:vertexCount:instanceCount:baseInstance:");
        let this_id: Id = self.obj.ptr();
        // SAFETY: docs Metal/MTLRenderCommandEncoder/drawPrimitives:vertexStart:vertexCount:instanceCount:baseInstance:
        //
        // encodes a draw with the bound pipeline and buffers; MTLPrimitiveTypeTriangle
        // is 3. No CPU memory is passed; the GPU's reads are the fixed shaders',
        // which check the instance index and every buffer index against counts the
        // caller passes. MSG_VOID_USIZE_USIZE_USIZE_USIZE_USIZE is `(id, SEL,
        // NSUInteger × 5) -> void`.
        unsafe {
            MSG_VOID_USIZE_USIZE_USIZE_USIZE_USIZE(
                this_id,
                s,
                3,
                0,
                vertex_count,
                instance_count,
                base_instance,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Device, Surface};

    // Miri cannot run foreign calls. CI's macOS runner may have no GPU, so a
    // missing device skips with a message rather than failing.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn a_surface_texture_has_the_surface_size() {
        let Ok(device) = Device::system_default() else {
            eprintln!("skipped: no Metal device");
            return;
        };
        let surface = Surface::new(7, 3);
        assert!(surface.is_ok(), "{surface:?}");
        let Ok(surface) = surface else { return };
        let texture = device.new_texture_on(&surface);
        assert!(
            texture
                .as_ref()
                .is_ok_and(|t| t.width() == 7 && t.height() == 3),
            "{texture:?}"
        );
    }

    #[test]
    fn sizes_are_checked_before_any_call() {
        assert!(Surface::new(0, 1).is_err());
        assert!(Surface::new(1, 16_385).is_err());
    }
}
