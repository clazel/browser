//! The host's window on macOS (phase-5.md item 5.21), on Apple silicon: AppKit
//! and Core Animation through the Objective-C runtime, and a CPU image through
//! Core Graphics.
//!
//! Safe wrappers, each doing one AppKit or Core Animation operation with values
//! `clazel-window` chose (a title, a size, a layer's frame, which events to hand
//! back to AppKit), checking what the operation's documentation requires of
//! them, and deciding nothing about what a window shows or what an event means.
//!
//! Objective-C messages go through `objc_msgSend`, declared once with no
//! parameters and cast once per message signature to a `"C-unwind"` function
//! pointer of the method's exact type, in a `const` (the dispatcher casts of
//! `xtask/src/sys.rs`), exactly as in `metal.rs`. This file declares its own
//! dispatcher, runtime functions and casts so that its lists stay its own.
//! Citations are to Apple's developer documentation, written
//! `docs <Framework>/<Class>/<member>`, and to the SDK header that declares each.
//!
//! # Modelling choices
//!
//! - **No Rust function is ever called by the Objective-C runtime.** Events are
//!   polled with `nextEventMatchingMask:untilDate:inMode:dequeue:` and handed back
//!   with `sendEvent:` only when the caller says so, so no class, delegate, block
//!   or callback is defined here. What that costs: a window's closing is seen as
//!   it no longer being visible (no `windowWillClose:`), its size and scale are
//!   read rather than reported, and AppKit's own loops (a live resize, a drag of
//!   the title bar) run inside `sendEvent:` until they end.
//! - **The main thread only.** AppKit's windows and the shared application may
//!   only be used on the main thread. [`MainThread`] is the proof that the caller
//!   is on it (`pthread_main_np`), every type here holds a raw pointer and so is
//!   neither `Send` nor `Sync`, and nothing can be made without a `MainThread`.
//! - **No window server, no application.** `+[NSApplication sharedApplication]`
//!   ends the process when there is no window server session (an SSH login, a
//!   headless machine), so [`App::shared`] first asks Core Graphics whether there
//!   is one (`CGSessionCopyCurrentDictionary`).
//! - **Apple silicon only** (`target_arch = "aarch64"`), as `metal.rs`: `BOOL` is
//!   C `bool` there, and structures of two or four `double` (`NSPoint`, `NSRect`)
//!   are passed and returned in floating-point registers by `objc_msgSend` itself,
//!   with no `_stret` or `_fpret` variant. Intel Macs are not supported.
//! - **Every object held is owned** (+1), as in `metal.rs`: `alloc`/`init…`
//!   results are kept, and [`Drop`] sends `release`; a non-owning getter's result
//!   (`-[NSWindow contentView]`) is used at once and never kept. A window is made with
//!   `releasedWhenClosed` set to `NO` straight after `init`, so `close` never
//!   releases the reference [`Window`] owns. Autoreleased objects (an event, its
//!   characters) are read inside an autorelease pool and never kept.
//! - **Accessors are only sent to events that have them.** `-[NSEvent keyCode]`
//!   on a mouse event raises an exception, so [`RawEvent`] reads each accessor
//!   only for the event types its documentation names ([`EventFields::of`]).
//! - **The content view hosts a layer tree of the caller's** ([`Window::host_layer`]):
//!   `setLayer:` and then `setWantsLayer:YES`, which AppKit's documentation of
//!   `wantsLayer` calls a layer-hosting view, the form in which the application,
//!   not the view, manages the layer and its sublayers.
//! - **Layer geometry is checked to be finite.** Core Animation raises an
//!   exception for a NaN position or bounds, so every rectangle is checked first.
//! - **A page's surface** is shown by setting a layer's `contents` to an
//!   `IOSurfaceRef`. Core Animation accepts that, and WebKit and Chromium rely on
//!   it, but `CALayer.contents` documents only `CGImage` (and `NSImage`); this is
//!   the one undocumented behaviour used here. A surface is `metal.rs`'s
//!   [`Surface`]: in this process for now; the Mach port that carries one from the
//!   GPU process is item 5.18's.
//! - **Objective-C exceptions unwind; they are not caught**, as in `metal.rs`: the
//!   casts are `"C-unwind"`, so an exception from a method is a defined unwind
//!   through the Rust frames above the call (or an abort). The checks above keep
//!   the documented exceptions from being raised.

use std::ffi::{CStr, c_char, c_int, c_void};
use std::fmt;
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::time::Duration;

use super::metal::Surface;

/// An Objective-C object pointer (`id`).
type Id = *mut c_void;
/// A selector (`SEL`).
type Sel = *const c_void;

#[link(name = "objc", kind = "dylib")]
// SAFETY: docs ObjectiveC/objc_msgSend, from <objc/message.h>: declared here with
// no parameters, as <objc/message.h> does when OBJC_OLD_DISPATCH_PROTOTYPES is 0,
// because it is never called as declared, only cast to a typed pointer (below).
// The ABI is "C-unwind", not "C": the method a message reaches may throw an
// Objective-C exception, and an unwind out of a "C" call is undefined behaviour.
// The declaration is identical to `metal.rs`'s. libobjc is linked by name.
unsafe extern "C-unwind" {
    fn objc_msgSend();
}

#[link(name = "objc", kind = "dylib")]
// SAFETY: docs ObjectiveC/objc_getClass and docs ObjectiveC/sel_registerName,
// from <objc/runtime.h>: `Class objc_getClass(const char *name)` and
// `SEL sel_registerName(const char *str)`, both returning a pointer; `c_char` and
// pointers match, and the declarations are identical to `metal.rs`'s. Neither
// sends a message, so neither runs a method that could throw.
unsafe extern "C" {
    fn objc_getClass(name: *const c_char) -> Id;
    fn sel_registerName(name: *const c_char) -> Sel;
}

// SAFETY: man 3 pthread_main_np, from <pthread.h>: `int pthread_main_np(void)`,
// non-zero on the main thread; `c_int` is C `int`. It lives in libSystem, which
// the standard library links, and reads no memory of the caller's.
unsafe extern "C" {
    fn pthread_main_np() -> c_int;
}

#[link(name = "CoreGraphics", kind = "framework")]
// SAFETY: docs CoreGraphics/CGSessionCopyCurrentDictionary, from
// <CoreGraphics/CGSession.h>: `CFDictionaryRef CGSessionCopyCurrentDictionary(void)`,
// an owned dictionary (the Copy rule) or NULL when the caller is not in a Quartz
// GUI session; docs CoreGraphics/CGDataProviderCreateWithCFData, from
// <CoreGraphics/CGDataProvider.h>: `CGDataProviderRef
// CGDataProviderCreateWithCFData(CFDataRef data)`; docs
// CoreGraphics/CGColorSpaceCreateDeviceRGB, from <CoreGraphics/CGColorSpace.h>:
// `CGColorSpaceRef CGColorSpaceCreateDeviceRGB(void)`; docs CoreGraphics/CGImageCreate,
// from <CoreGraphics/CGImage.h>: `CGImageRef CGImageCreate(size_t width, size_t
// height, size_t bitsPerComponent, size_t bitsPerPixel, size_t bytesPerRow,
// CGColorSpaceRef space, CGBitmapInfo bitmapInfo, CGDataProviderRef provider,
// const CGFloat *decode, bool shouldInterpolate, CGColorRenderingIntent intent)`.
// Every `…Ref` is a pointer, `size_t` is `usize`, `CGBitmapInfo` is `uint32_t`,
// `CGColorRenderingIntent` is an `int32_t` enumeration, `CGFloat` is `double`
// and `bool` is C `bool`, as declared. Each Create function returns an owned
// object or NULL.
unsafe extern "C" {
    fn CGSessionCopyCurrentDictionary() -> Id;
    fn CGDataProviderCreateWithCFData(data: Id) -> Id;
    fn CGColorSpaceCreateDeviceRGB() -> Id;
    fn CGImageCreate(
        width: usize,
        height: usize,
        bits_per_component: usize,
        bits_per_pixel: usize,
        bytes_per_row: usize,
        space: Id,
        bitmap_info: u32,
        provider: Id,
        decode: *const f64,
        should_interpolate: bool,
        intent: i32,
    ) -> Id;
}

#[link(name = "CoreFoundation", kind = "framework")]
// SAFETY: docs CoreFoundation/CFRelease, from <CoreFoundation/CFBase.h>:
// `void CFRelease(CFTypeRef cf)`, `cf` not NULL, identical to `metal.rs`'s
// declaration; docs CoreFoundation/CFDataCreate, from
// <CoreFoundation/CFData.h>: `CFDataRef CFDataCreate(CFAllocatorRef allocator,
// const UInt8 *bytes, CFIndex length)`, which copies `length` bytes and returns
// an owned object or NULL. `CFIndex` is `signed long`, 64 bits, as `isize`;
// `UInt8` is `u8`; the references are pointers.
unsafe extern "C" {
    fn CFRelease(cf: Id);
    fn CFDataCreate(allocator: Id, bytes: *const u8, length: isize) -> Id;
}

#[link(name = "AppKit", kind = "framework")]
// SAFETY: docs AppKit (the framework): nothing is declared; the block links
// AppKit for the NSApplication and NSWindow classes this file finds by name with
// objc_getClass.
unsafe extern "C" {}

#[link(name = "QuartzCore", kind = "framework")]
// SAFETY: docs QuartzCore (the framework): nothing is declared; the block links
// Core Animation for the CALayer and CATransaction classes.
unsafe extern "C" {}

#[link(name = "Foundation", kind = "framework")]
// SAFETY: docs Foundation (the framework): nothing is declared; the block links
// Foundation for the NSString, NSDate and NSAutoreleasePool classes.
unsafe extern "C" {}

/// `NSPoint`, `CGPoint` (<CoreGraphics/CGGeometry.h>): two `CGFloat`.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
struct Point {
    x: f64,
    y: f64,
}

/// `NSSize`, `CGSize` (<CoreGraphics/CGGeometry.h>): two `CGFloat`.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
struct Size {
    width: f64,
    height: f64,
}

/// `NSRect`, `CGRect` (<CoreGraphics/CGGeometry.h>): an origin and a size.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
struct CgRect {
    origin: Point,
    size: Size,
}

// The dispatcher casts. Each has the receiver (`id`) and the selector (`SEL`)
// first, then the method's parameters, and its return type, exactly as the
// method is declared; `NSUInteger` is `usize`, `NSInteger` is `isize`, `BOOL` is
// `bool` and `CGFloat` is `f64` on Apple silicon, and every object parameter is
// `id`. Each is "C-unwind", the ABI `objc_msgSend` is declared with.

// SAFETY: docs ObjectiveC/objc_msgSend ("must be cast to an appropriate function
// pointer type before being called"). Methods `(id)m` returning `id`: docs
// ObjectiveC/NSObject/alloc (a class method), docs ObjectiveC/NSObject/init, docs
// AppKit/NSApplication/sharedApplication (a class method), docs
// AppKit/NSWindow/contentView, docs AppKit/NSEvent/window and docs
// AppKit/NSEvent/characters.
const MSG_ID: unsafe extern "C-unwind" fn(Id, Sel) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(void)m`: docs ObjectiveC/NSObject/release, docs
// Foundation/NSAutoreleasePool/drain, docs AppKit/NSApplication/finishLaunching,
// docs AppKit/NSWindow/close, docs AppKit/NSWindow/center, and docs
// QuartzCore/CATransaction/begin and commit (class methods).
const MSG_VOID: unsafe extern "C-unwind" fn(Id, Sel) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(NSUInteger)m`: docs AppKit/NSEvent/type (`NSEventType`, an `NSUInteger`
// enumeration), docs AppKit/NSEvent/modifierFlags (`NSEventModifierFlags`, an
// `NSUInteger` set) and docs Foundation/NSString/length.
const MSG_USIZE: unsafe extern "C-unwind" fn(Id, Sel) -> usize =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(BOOL)m`: docs AppKit/NSWindow/isVisible, docs AppKit/NSWindow/isMiniaturized,
// docs AppKit/NSApplication/isHidden and docs
// AppKit/NSEvent/hasPreciseScrollingDeltas; `BOOL` is `bool` on Apple silicon.
const MSG_BOOL: unsafe extern "C-unwind" fn(Id, Sel) -> bool =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(CGFloat)m`: docs AppKit/NSWindow/backingScaleFactor, docs
// AppKit/NSEvent/scrollingDeltaX and docs AppKit/NSEvent/scrollingDeltaY;
// `CGFloat` is `double`, returned in d0 by `objc_msgSend` on arm64.
const MSG_F64: unsafe extern "C-unwind" fn(Id, Sel) -> f64 =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(unsigned short)keyCode`: docs AppKit/NSEvent/keyCode; `unsigned short` is
// `u16`.
const MSG_U16: unsafe extern "C-unwind" fn(Id, Sel) -> u16 =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(NSPoint)locationInWindow`: docs AppKit/NSEvent/locationInWindow; `NSPoint` is
// two `CGFloat`, a homogeneous floating-point aggregate returned in d0 and d1 on
// arm64, where `objc_msgSend` has no `_stret` form.
const MSG_POINT: unsafe extern "C-unwind" fn(Id, Sel) -> Point =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(NSRect)bounds`: docs AppKit/NSView/bounds; `NSRect` is four `CGFloat`, a
// homogeneous floating-point aggregate returned in d0 to d3 on arm64.
const MSG_RECT: unsafe extern "C-unwind" fn(Id, Sel) -> CgRect =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(void)m:(id)a`: docs AppKit/NSWindow/title (its setter, an NSString), docs
// AppKit/NSApplication/sendEvent:, docs AppKit/NSWindow/orderFront:, docs
// AppKit/NSWindow/makeKeyAndOrderFront:, docs AppKit/NSView/layer (its setter),
// docs QuartzCore/CALayer/addSublayer:,
// docs QuartzCore/CALayer/contents (its setter, `id`) and docs
// QuartzCore/CALayer/contentsGravity (its setter, an NSString).
const MSG_VOID_ID: unsafe extern "C-unwind" fn(Id, Sel, Id) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Methods
// `(void)m:(BOOL)a`: docs AppKit/NSWindow/isReleasedWhenClosed (its setter), docs
// AppKit/NSView/wantsLayer (its setter), docs QuartzCore/CALayer/masksToBounds
// and docs QuartzCore/CALayer/isHidden (their setters), docs
// QuartzCore/CATransaction/setDisableActions: (a class method) and docs
// AppKit/NSApplication/activateIgnoringOtherApps:.
const MSG_VOID_BOOL: unsafe extern "C-unwind" fn(Id, Sel, bool) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(void)setContentsScale:(CGFloat)s`: docs QuartzCore/CALayer/contentsScale (its
// setter); `CGFloat` is `double`, passed in d0.
const MSG_VOID_F64: unsafe extern "C-unwind" fn(Id, Sel, f64) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(void)setAutoresizingMask:(CAAutoresizingMask)m`: docs
// QuartzCore/CALayer/autoresizingMask (its setter); <QuartzCore/CALayer.h>
// declares `CAAutoresizingMask` as `NS_OPTIONS (unsigned int, …)`, so `u32`.
const MSG_VOID_U32: unsafe extern "C-unwind" fn(Id, Sel, u32) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(void)setFrame:(CGRect)r`: docs QuartzCore/CALayer/frame (its setter), the
// structure by value (four `double`, passed in d0 to d3).
const MSG_VOID_RECT: unsafe extern "C-unwind" fn(Id, Sel, CgRect) =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(BOOL)setActivationPolicy:(NSApplicationActivationPolicy)p`: docs
// AppKit/NSApplication/setActivationPolicy:; <AppKit/NSRunningApplication.h>
// declares the policy `NS_ENUM(NSInteger, …)`, so `isize`.
const MSG_BOOL_ISIZE: unsafe extern "C-unwind" fn(Id, Sel, isize) -> bool =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(unichar)characterAtIndex:(NSUInteger)i`: docs
// Foundation/NSString/characterAtIndex:; `unichar` is `unsigned short`, `u16`.
const MSG_U16_USIZE: unsafe extern "C-unwind" fn(Id, Sel, usize) -> u16 =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(instancetype)initWithTimeIntervalSinceNow:(NSTimeInterval)t`: docs
// Foundation/NSDate/initWithTimeIntervalSinceNow:; `NSTimeInterval` is `double`.
const MSG_ID_F64: unsafe extern "C-unwind" fn(Id, Sel, f64) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(instancetype)initWithBytes:(const void *)p length:(NSUInteger)n
// encoding:(NSStringEncoding)e`: docs Foundation/NSString/initWithBytes:length:encoding:
// (`NSStringEncoding` is an `NSUInteger`).
const MSG_ID_PTR_USIZE_USIZE: unsafe extern "C-unwind" fn(
    Id,
    Sel,
    *const c_void,
    usize,
    usize,
) -> Id = unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(NSEvent *)nextEventMatchingMask:(NSEventMask)m untilDate:(NSDate *)d
// inMode:(NSRunLoopMode)r dequeue:(BOOL)q`: docs
// AppKit/NSApplication/nextEventMatchingMask:untilDate:inMode:dequeue:
// (`NSEventMask` is `unsigned long long`, 64 bits as `usize` on arm64; the mode is
// an NSString).
const MSG_ID_USIZE_ID_ID_BOOL: unsafe extern "C-unwind" fn(Id, Sel, usize, Id, Id, bool) -> Id =
    unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

// SAFETY: docs ObjectiveC/objc_msgSend (cast to the method's type). Method
// `(instancetype)initWithContentRect:(NSRect)r styleMask:(NSWindowStyleMask)s
// backing:(NSBackingStoreType)b defer:(BOOL)d`: docs
// AppKit/NSWindow/initWithContentRect:styleMask:backing:defer: (`NSWindowStyleMask`
// and `NSBackingStoreType` are `NSUInteger`; the rectangle is passed in d0 to d3).
const MSG_ID_RECT_USIZE_USIZE_BOOL: unsafe extern "C-unwind" fn(
    Id,
    Sel,
    CgRect,
    usize,
    usize,
    bool,
) -> Id = unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };

/// An AppKit, Core Animation or Core Graphics call failed or was refused before
/// it was made. This crate decides nothing about it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WindowError {
    /// The method or function, or the check, that failed.
    pub what: &'static str,
}

impl fmt::Display for WindowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AppKit: {} failed", self.what)
    }
}

impl std::error::Error for WindowError {}

fn fail(what: &'static str) -> WindowError {
    WindowError { what }
}

/// The selector named `name`.
fn sel(name: &CStr) -> Sel {
    let p: *const c_char = name.as_ptr();
    // SAFETY: docs ObjectiveC/sel_registerName: takes a NUL-terminated C string and
    // returns its selector, registering it if new. `p` is the NUL-terminated
    // buffer of `name`, borrowed for the call.
    unsafe { sel_registerName(p) }
}

/// The class named `name`.
fn class(name: &'static CStr) -> Result<Id, WindowError> {
    let p: *const c_char = name.as_ptr();
    // SAFETY: docs ObjectiveC/objc_getClass: takes a NUL-terminated class name and
    // returns the class, or nil if none is registered. `p` is the NUL-terminated
    // buffer of a `'static` string. Classes are never released.
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
    /// Take an owned reference (+1), as `alloc`/`init…` give; nil is an error.
    fn owned(p: Id, what: &'static str) -> Result<Object, WindowError> {
        NonNull::new(p).map(Object).ok_or(fail(what))
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
        // here once, on the thread that holds it (`Object` is not `Send`).
        unsafe { MSG_VOID(this_id, s) }
    }
}

/// `[[class alloc] init]`: a new owned object.
fn new_object(name: &'static CStr) -> Result<Object, WindowError> {
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
    // SAFETY: docs ObjectiveC/NSObject/init: consumes the allocated instance and
    // returns the initialised one (owned) or nil. `a` is the instance `alloc` just
    // returned and is used no more.
    let o = unsafe { MSG_ID(a, s_init) };
    Object::owned(o, "init")
}

/// An owned `NSString` holding `text`, which may contain any character, NUL
/// included (the string is made from a length, not a terminator).
fn ns_string(text: &str) -> Result<Object, WindowError> {
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
    // bytes at `bytes` in the given encoding (NSUTF8StringEncoding, 4) and copies
    // them, returning an owned string or nil. `bytes` and `len` are the pointer and
    // length of `text`, valid UTF-8 borrowed for the call. `a` is the instance
    // `alloc` returned.
    let o = unsafe { MSG_ID_PTR_USIZE_USIZE(a, s_init, bytes, len, 4) };
    Object::owned(o, "initWithBytes:length:encoding:")
}

/// Drains an autorelease pool when dropped, on the thread that made it.
struct Pool(NonNull<c_void>);

impl Pool {
    fn new() -> Result<Pool, WindowError> {
        let pool = new_object(c"NSAutoreleasePool")?;
        let p = pool.0;
        // Draining releases the pool, so it must not also be released.
        std::mem::forget(pool);
        Ok(Pool(p))
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        let s = sel(c"drain");
        let p: Id = self.0.as_ptr();
        // SAFETY: docs Foundation/NSAutoreleasePool/drain: releases the pool's
        // objects and the pool itself. `p` is the pool `init` returned (its `Object`
        // forgotten in `new`, so never released), drained once, here, on the thread
        // that made it (`Pool` is not `Send`), after every pool made inside its
        // scope.
        unsafe { MSG_VOID(p, s) }
    }
}

/// Proof that the holder is on the process's main thread, which AppKit requires.
/// Neither `Send` nor `Sync`, so it cannot leave that thread.
#[derive(Debug, Clone, Copy)]
pub struct MainThread(PhantomData<*const ()>);

impl MainThread {
    /// The proof, or `None` on any other thread.
    pub fn new() -> Option<MainThread> {
        // SAFETY: man 3 pthread_main_np: takes nothing and returns non-zero on the
        // main thread; it reads no memory of the caller's.
        let main = unsafe { pthread_main_np() };
        (main != 0).then_some(MainThread(PhantomData))
    }
}

/// Whether this process is in a window server (Quartz GUI) session, so that it
/// may open windows.
pub fn has_window_server() -> bool {
    // SAFETY: docs CoreGraphics/CGSessionCopyCurrentDictionary: takes nothing and
    // returns an owned dictionary, or NULL outside a Quartz GUI session.
    let d = unsafe { CGSessionCopyCurrentDictionary() };
    if d.is_null() {
        return false;
    }
    // SAFETY: docs CoreFoundation/CFRelease: `d` is the non-NULL dictionary just
    // returned under the Copy rule, released once, here.
    unsafe { CFRelease(d) }
    true
}

/// `NSApplicationActivationPolicy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivationPolicy {
    /// `NSApplicationActivationPolicyRegular`, 0: in the Dock, with a menu bar.
    Regular,
    /// `NSApplicationActivationPolicyAccessory`, 1: no Dock icon or menu bar; it
    /// may still show windows and be activated.
    Accessory,
}

impl ActivationPolicy {
    fn raw(self) -> isize {
        match self {
            ActivationPolicy::Regular => 0,
            ActivationPolicy::Accessory => 1,
        }
    }
}

/// `NSEventMaskAny`: `NSUIntegerMax`.
const EVENT_MASK_ANY: usize = usize::MAX;

/// The longest wait [`App::next_event`] accepts, one day; the date it is turned
/// into must be finite.
pub const MAX_WAIT: Duration = Duration::from_secs(86_400);

/// The most UTF-16 code units of an event's `characters` that are read.
pub const MAX_CHARACTERS: usize = 64;

/// The shared application (`NSApp`). It is never released: it lives as long as
/// the process.
#[derive(Debug)]
pub struct App {
    ptr: NonNull<c_void>,
    /// `NSDefaultRunLoopMode`, the mode events are read in.
    mode: Object,
}

impl App {
    /// The shared application, made on first use. An error if there is no window
    /// server session ([`has_window_server`]), where AppKit would end the process.
    pub fn shared(_main: MainThread) -> Result<App, WindowError> {
        if !has_window_server() {
            return Err(fail("a window server session"));
        }
        let c = class(c"NSApplication")?;
        let s = sel(c"sharedApplication");
        // SAFETY: docs AppKit/NSApplication/sharedApplication: a class method that
        // returns the application, making it if needed; it lives as long as the
        // process and is not owned by the caller. The caller is on the main thread
        // (`MainThread`) and a window server session exists (checked above).
        let p = unsafe { MSG_ID(c, s) };
        let ptr = NonNull::new(p).ok_or(fail("sharedApplication"))?;
        // `NSDefaultRunLoopMode` is a data symbol, which the checker does not allow
        // to be declared; its value, from <Foundation/NSRunLoop.h> and
        // `kCFRunLoopDefaultMode`, is this string.
        let mode = ns_string("kCFRunLoopDefaultMode")?;
        Ok(App { ptr, mode })
    }

    /// `setActivationPolicy:`. False if the system refused it.
    pub fn set_activation_policy(&self, policy: ActivationPolicy) -> bool {
        let s = sel(c"setActivationPolicy:");
        let app: Id = self.ptr.as_ptr();
        let raw = policy.raw();
        // SAFETY: docs AppKit/NSApplication/setActivationPolicy: takes one of the
        // documented policies (`raw` is 0 or 1) and returns whether it was set.
        unsafe { MSG_BOOL_ISIZE(app, s, raw) }
    }

    /// `finishLaunching`: makes the application ready to show windows and read
    /// events. Sending it more than once is the caller's choice.
    pub fn finish_launching(&self) {
        let s = sel(c"finishLaunching");
        let app: Id = self.ptr.as_ptr();
        // SAFETY: docs AppKit/NSApplication/finishLaunching: takes nothing; the
        // application is the shared one, on the main thread.
        unsafe { MSG_VOID(app, s) }
    }

    /// `activateIgnoringOtherApps:YES`: bring the application to the front and give
    /// it the keyboard.
    pub fn activate(&self) {
        let s = sel(c"activateIgnoringOtherApps:");
        let app: Id = self.ptr.as_ptr();
        // SAFETY: docs AppKit/NSApplication/activateIgnoringOtherApps: takes a BOOL
        // and returns nothing; deprecated in favour of `activate` (macOS 14), and
        // still present.
        unsafe { MSG_VOID_BOOL(app, s, true) }
    }

    /// `isHidden`: the user hid the application.
    pub fn is_hidden(&self) -> bool {
        let s = sel(c"isHidden");
        let app: Id = self.ptr.as_ptr();
        // SAFETY: docs AppKit/NSApplication/isHidden: a BOOL property getter.
        unsafe { MSG_BOOL(app, s) }
    }

    /// Wait up to `wait` (at most [`MAX_WAIT`]) for the next event of any kind,
    /// remove it from the queue and read it. If `forward` says so, hand it to
    /// AppKit (`sendEvent:`), which moves, resizes and closes windows; a drag of a
    /// window's frame stays inside that call until it ends. `None` if no event
    /// came.
    pub fn next_event(
        &self,
        wait: Duration,
        forward: impl FnOnce(&RawEvent) -> bool,
    ) -> Result<Option<RawEvent>, WindowError> {
        let seconds = wait_seconds(wait)?;
        let _pool = Pool::new()?;
        let date_class = class(c"NSDate")?;
        let s_alloc = sel(c"alloc");
        // SAFETY: docs ObjectiveC/NSObject/alloc, as in `new_object`.
        let a = unsafe { MSG_ID(date_class, s_alloc) };
        if a.is_null() {
            return Err(fail("alloc"));
        }
        let s_init = sel(c"initWithTimeIntervalSinceNow:");
        // SAFETY: docs Foundation/NSDate/initWithTimeIntervalSinceNow: takes a
        // finite number of seconds (`seconds` is 0 to 86,400, checked) and returns
        // an owned date or nil. `a` is the instance `alloc` returned.
        let d = unsafe { MSG_ID_F64(a, s_init, seconds) };
        let until = Object::owned(d, "initWithTimeIntervalSinceNow:")?;
        let s = sel(c"nextEventMatchingMask:untilDate:inMode:dequeue:");
        let app: Id = self.ptr.as_ptr();
        let until_id: Id = until.ptr();
        let mode_id: Id = self.mode.ptr();
        // SAFETY: docs AppKit/NSApplication/nextEventMatchingMask:untilDate:inMode:dequeue:
        // returns the next event matching the mask (any), waiting until the date,
        // in the run loop mode, removed from the queue, or nil; the event is
        // autoreleased into `_pool`, which outlives every use of it below. `until`
        // and `self.mode` are live owned objects. On the main thread.
        let e = unsafe { MSG_ID_USIZE_ID_ID_BOOL(app, s, EVENT_MASK_ANY, until_id, mode_id, true) };
        let Some(event) = NonNull::new(e) else {
            return Ok(None);
        };
        let raw = RawEvent::read(event)?;
        if forward(&raw) {
            let s_send = sel(c"sendEvent:");
            let event_id: Id = event.as_ptr();
            // SAFETY: docs AppKit/NSApplication/sendEvent: dispatches an event the
            // application took from its queue; `event_id` is the event just dequeued,
            // kept alive by `_pool`. On the main thread.
            unsafe { MSG_VOID_ID(app, s_send, event_id) }
        }
        Ok(Some(raw))
    }
}

/// `wait` as the seconds an `NSDate` is made from: at most [`MAX_WAIT`], so finite.
fn wait_seconds(wait: Duration) -> Result<f64, WindowError> {
    if wait > MAX_WAIT {
        return Err(fail("a wait of at most a day"));
    }
    Ok(wait.as_secs_f64())
}

/// Which window an event is for, by identity only: it is never dereferenced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WindowId(usize);

/// A scroll event's deltas (`scrollingDeltaX`, `scrollingDeltaY`), in lines, or in
/// points when `precise` (`hasPreciseScrollingDeltas`), already inverted if the
/// user's setting inverts them.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Scroll {
    /// Horizontal.
    pub dx: f64,
    /// Vertical.
    pub dy: f64,
    /// Points rather than lines.
    pub precise: bool,
}

/// An event as AppKit gave it, with no meaning attached. A field is `None` when the
/// event's type does not have that accessor.
#[derive(Debug, Clone, PartialEq)]
pub struct RawEvent {
    /// `NSEventType`.
    pub kind: usize,
    /// `modifierFlags`.
    pub modifiers: usize,
    /// The window it is for (`window`), if any.
    pub window: Option<WindowId>,
    /// `locationInWindow`, in points from the window's bottom left, for
    /// mouse-related events.
    pub location: Option<(f64, f64)>,
    /// `keyCode`, for key and modifier events.
    pub key_code: Option<u16>,
    /// `characters`, as UTF-16 code units, for key events; at most
    /// [`MAX_CHARACTERS`].
    pub characters: Vec<u16>,
    /// For scroll wheel events.
    pub scroll: Option<Scroll>,
}

/// Which accessors an event type has, from AppKit's documentation of each
/// (<AppKit/NSEvent.h>): an accessor sent to an event without it may raise an
/// exception.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EventFields {
    /// `locationInWindow`: "valid for all mouse-related events" (mouse down, up,
    /// moved, dragged, entered, exited, scroll wheel, other mouse).
    pub location: bool,
    /// `keyCode`: key down, key up and flags changed.
    pub key_code: bool,
    /// `characters`: key down and key up.
    pub characters: bool,
    /// `scrollingDeltaX`, `scrollingDeltaY`, `hasPreciseScrollingDeltas`: scroll
    /// wheel.
    pub scroll: bool,
}

impl EventFields {
    /// The accessors of the event type `kind` (`NSEventType`).
    pub fn of(kind: usize) -> EventFields {
        // NSEventTypeLeftMouseDown 1 to NSEventTypeMouseExited 9 (left and right
        // down, up and dragged, moved, entered, exited), ScrollWheel 22,
        // OtherMouseDown 25, OtherMouseUp 26, OtherMouseDragged 27.
        let location = matches!(kind, 1..=9 | 22 | 25..=27);
        EventFields {
            location,
            key_code: matches!(kind, 10..=12),
            characters: matches!(kind, 10 | 11),
            scroll: kind == 22,
        }
    }
}

impl RawEvent {
    /// Read `event`, sending only the accessors its type has.
    fn read(event: NonNull<c_void>) -> Result<RawEvent, WindowError> {
        let e: Id = event.as_ptr();
        let s_type = sel(c"type");
        // SAFETY: docs AppKit/NSEvent/type: an `NSEventType` (`NSUInteger`)
        // getter, valid for every event. `e` is a live event kept by the caller's
        // autorelease pool.
        let kind = unsafe { MSG_USIZE(e, s_type) };
        let s_flags = sel(c"modifierFlags");
        // SAFETY: docs AppKit/NSEvent/modifierFlags: an `NSUInteger` getter, valid
        // for every event.
        let modifiers = unsafe { MSG_USIZE(e, s_flags) };
        let s_window = sel(c"window");
        // SAFETY: docs AppKit/NSEvent/window: the window the event is for, or nil;
        // valid for every event. Only its address is kept, never dereferenced.
        let w = unsafe { MSG_ID(e, s_window) };
        let window = NonNull::new(w).map(|w| WindowId(w.as_ptr() as usize));
        let fields = EventFields::of(kind);
        let location = if fields.location {
            let s = sel(c"locationInWindow");
            // SAFETY: docs AppKit/NSEvent/locationInWindow: an `NSPoint` getter,
            // "valid for all mouse-related events", which `kind` is
            // (`EventFields::of`).
            let p = unsafe { MSG_POINT(e, s) };
            Some((p.x, p.y))
        } else {
            None
        };
        let key_code = if fields.key_code {
            let s = sel(c"keyCode");
            // SAFETY: docs AppKit/NSEvent/keyCode: "valid for keyup, keydown and
            // flagschanged events", which `kind` is (`EventFields::of`).
            Some(unsafe { MSG_U16(e, s) })
        } else {
            None
        };
        let characters = if fields.characters {
            let s = sel(c"characters");
            // SAFETY: docs AppKit/NSEvent/characters: the typed characters, an
            // autoreleased NSString or nil, "valid for keyup and keydown events",
            // which `kind` is.
            let text = unsafe { MSG_ID(e, s) };
            utf16_units(text)
        } else {
            Vec::new()
        };
        let scroll = if fields.scroll {
            let s_dx = sel(c"scrollingDeltaX");
            // SAFETY: docs AppKit/NSEvent/scrollingDeltaX: a `CGFloat` getter, valid
            // for scroll wheel events, which `kind` is.
            let dx = unsafe { MSG_F64(e, s_dx) };
            let s_dy = sel(c"scrollingDeltaY");
            // SAFETY: docs AppKit/NSEvent/scrollingDeltaY, as scrollingDeltaX.
            let dy = unsafe { MSG_F64(e, s_dy) };
            let s_precise = sel(c"hasPreciseScrollingDeltas");
            // SAFETY: docs AppKit/NSEvent/hasPreciseScrollingDeltas: a BOOL getter,
            // valid for scroll wheel events, which `kind` is.
            let precise = unsafe { MSG_BOOL(e, s_precise) };
            Some(Scroll { dx, dy, precise })
        } else {
            None
        };
        Ok(RawEvent {
            kind,
            modifiers,
            window,
            location,
            key_code,
            characters,
            scroll,
        })
    }
}

/// The first [`MAX_CHARACTERS`] UTF-16 code units of the NSString `text` (nil is
/// empty). Every index sent is below its `length`, which `characterAtIndex:`
/// requires.
fn utf16_units(text: Id) -> Vec<u16> {
    if text.is_null() {
        return Vec::new();
    }
    let s_len = sel(c"length");
    // SAFETY: docs Foundation/NSString/length: the number of UTF-16 code units, an
    // `NSUInteger` getter; `text` is a live string kept by the caller's pool.
    let len = unsafe { MSG_USIZE(text, s_len) };
    let s_at = sel(c"characterAtIndex:");
    (0..units_to_read(len))
        .map(|i| {
            // SAFETY: docs Foundation/NSString/characterAtIndex: returns the code
            // unit at `i`, raising an exception if `i` is not below `length`; `i`
            // is below `units_to_read(len)`, which is at most `len`.
            unsafe { MSG_U16_USIZE(text, s_at, i) }
        })
        .collect()
}

/// How many code units of a string of `len` are read.
fn units_to_read(len: usize) -> usize {
    len.min(MAX_CHARACTERS)
}

/// The kinds of window this file opens: always titled, as AppKit needs for the
/// close, minimise and resize controls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Style {
    /// A close button (`NSWindowStyleMaskClosable`).
    pub closable: bool,
    /// A minimise button (`NSWindowStyleMaskMiniaturizable`).
    pub miniaturizable: bool,
    /// A resizable frame (`NSWindowStyleMaskResizable`).
    pub resizable: bool,
}

impl Style {
    /// `NSWindowStyleMask`, from <AppKit/NSWindow.h>: Titled 1, Closable 2,
    /// Miniaturizable 4, Resizable 8.
    fn mask(self) -> usize {
        let mut m = 1;
        if self.closable {
            m |= 2;
        }
        if self.miniaturizable {
            m |= 4;
        }
        if self.resizable {
            m |= 8;
        }
        m
    }
}

/// The largest side of a window's content, in points, that [`Window::new`]
/// accepts.
pub const MAX_WINDOW_POINTS: f64 = 16_384.0;

/// A rectangle in points: `x`, `y` from the bottom left of the layer that holds
/// it (Core Animation's and AppKit's unflipped coordinates).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Rect {
    /// From the left.
    pub x: f64,
    /// From the bottom.
    pub y: f64,
    /// Width, not negative.
    pub width: f64,
    /// Height, not negative.
    pub height: f64,
}

impl Rect {
    /// The rectangle, if every number is finite and the size is not negative, as
    /// Core Animation requires (it raises an exception for NaN geometry).
    fn checked(self) -> Result<CgRect, WindowError> {
        let finite = [self.x, self.y, self.width, self.height]
            .iter()
            .all(|v| v.is_finite());
        if !finite || self.width < 0.0 || self.height < 0.0 {
            return Err(fail("a finite rectangle"));
        }
        Ok(CgRect {
            origin: Point {
                x: self.x,
                y: self.y,
            },
            size: Size {
                width: self.width,
                height: self.height,
            },
        })
    }
}

/// An `NSWindow`, owned. Dropping it closes it.
#[derive(Debug)]
pub struct Window {
    obj: Object,
}

impl Window {
    /// A new window whose content area is `width` by `height` points (each above
    /// 0 and at most [`MAX_WINDOW_POINTS`]), centred on the screen, not yet shown.
    pub fn new(
        _app: &App,
        title: &str,
        width: f64,
        height: f64,
        style: Style,
    ) -> Result<Window, WindowError> {
        if !window_side_ok(width) || !window_side_ok(height) {
            return Err(fail("a window size"));
        }
        let _pool = Pool::new()?;
        let c = class(c"NSWindow")?;
        let s_alloc = sel(c"alloc");
        // SAFETY: docs ObjectiveC/NSObject/alloc, as in `new_object`; on the main
        // thread (an `App` exists only there).
        let a = unsafe { MSG_ID(c, s_alloc) };
        if a.is_null() {
            return Err(fail("alloc"));
        }
        let rect = Rect {
            x: 0.0,
            y: 0.0,
            width,
            height,
        }
        .checked()?;
        let mask = style.mask();
        let s_init = sel(c"initWithContentRect:styleMask:backing:defer:");
        // SAFETY: docs AppKit/NSWindow/initWithContentRect:styleMask:backing:defer:
        // consumes the allocated instance and returns an owned window or nil. The
        // rectangle is finite and positive (checked), the mask is a combination of
        // the four documented values (`Style::mask`), the backing is
        // NSBackingStoreBuffered (2), and `defer` is NO. On the main thread.
        let w = unsafe { MSG_ID_RECT_USIZE_USIZE_BOOL(a, s_init, rect, mask, 2, false) };
        let obj = Object::owned(w, "initWithContentRect:styleMask:backing:defer:")?;
        let window = Window { obj };
        let s_released = sel(c"setReleasedWhenClosed:");
        let this: Id = window.obj.ptr();
        // SAFETY: docs AppKit/NSWindow/isReleasedWhenClosed (its setter): with NO,
        // `close` does not release the window, so the one reference `obj` owns is
        // given up only by its `Drop`. Sent before anything could close it.
        unsafe { MSG_VOID_BOOL(this, s_released, false) }
        window.set_title(title)?;
        let s_center = sel(c"center");
        // SAFETY: docs AppKit/NSWindow/center: takes nothing; moves the window.
        unsafe { MSG_VOID(this, s_center) }
        Ok(window)
    }

    /// The content view, not owned: the window keeps it while it lives.
    fn content_view(&self) -> Result<Id, WindowError> {
        let s = sel(c"contentView");
        let this: Id = self.obj.ptr();
        // SAFETY: docs AppKit/NSWindow/contentView: the window's content view, a
        // getter that returns an object the window owns.
        let v = unsafe { MSG_ID(this, s) };
        if v.is_null() {
            return Err(fail("contentView"));
        }
        Ok(v)
    }

    /// This window's identity, to compare with [`RawEvent::window`].
    pub fn id(&self) -> WindowId {
        WindowId(self.obj.ptr() as usize)
    }

    /// Set the title bar's text. Any text is accepted, NUL included.
    pub fn set_title(&self, title: &str) -> Result<(), WindowError> {
        let text = ns_string(title)?;
        let s = sel(c"setTitle:");
        let this: Id = self.obj.ptr();
        let text_id: Id = text.ptr();
        // SAFETY: docs AppKit/NSWindow/title (its setter): takes an NSString, which
        // the window copies; `text` is a live owned string.
        unsafe { MSG_VOID_ID(this, s, text_id) }
        Ok(())
    }

    /// `orderFront:`: show the window in front of the application's others,
    /// without making the application active or the window key.
    pub fn order_front(&self) {
        let s = sel(c"orderFront:");
        let this: Id = self.obj.ptr();
        let nil: Id = std::ptr::null_mut();
        // SAFETY: docs AppKit/NSWindow/orderFront: the sender may be nil.
        unsafe { MSG_VOID_ID(this, s, nil) }
    }

    /// `makeKeyAndOrderFront:`: show the window and make it the key window.
    pub fn make_key_and_order_front(&self) {
        let s = sel(c"makeKeyAndOrderFront:");
        let this: Id = self.obj.ptr();
        let nil: Id = std::ptr::null_mut();
        // SAFETY: docs AppKit/NSWindow/makeKeyAndOrderFront: the sender may be nil.
        unsafe { MSG_VOID_ID(this, s, nil) }
    }

    /// `close`: remove the window from the screen. It stays allocated (it is not
    /// released when closed) until this is dropped.
    pub fn close(&self) {
        let s = sel(c"close");
        let this: Id = self.obj.ptr();
        // SAFETY: docs AppKit/NSWindow/close: takes nothing; closing a closed
        // window does nothing. `releasedWhenClosed` is NO (set in `new`), so this
        // does not release the reference `obj` owns.
        unsafe { MSG_VOID(this, s) }
    }

    /// `isVisible`.
    pub fn is_visible(&self) -> bool {
        let s = sel(c"isVisible");
        let this: Id = self.obj.ptr();
        // SAFETY: docs AppKit/NSWindow/isVisible: a BOOL property getter.
        unsafe { MSG_BOOL(this, s) }
    }

    /// `isMiniaturized`.
    pub fn is_miniaturized(&self) -> bool {
        let s = sel(c"isMiniaturized");
        let this: Id = self.obj.ptr();
        // SAFETY: docs AppKit/NSWindow/isMiniaturized: a BOOL property getter.
        unsafe { MSG_BOOL(this, s) }
    }

    /// `backingScaleFactor`: device pixels per point.
    pub fn backing_scale(&self) -> f64 {
        let s = sel(c"backingScaleFactor");
        let this: Id = self.obj.ptr();
        // SAFETY: docs AppKit/NSWindow/backingScaleFactor: a `CGFloat` getter.
        unsafe { MSG_F64(this, s) }
    }

    /// The content view's size in points (`bounds`).
    pub fn content_size(&self) -> Result<(f64, f64), WindowError> {
        let view = self.content_view()?;
        let s = sel(c"bounds");
        // SAFETY: docs AppKit/NSView/bounds: an `NSRect` getter; `view` is the
        // window's live content view.
        let r = unsafe { MSG_RECT(view, s) };
        Ok((r.size.width, r.size.height))
    }

    /// Make the content view host `root`: `setLayer:` and then
    /// `setWantsLayer:YES`, in that order, which makes a layer-hosting view (docs
    /// AppKit/NSView/wantsLayer). The view retains `root`, and AppKit sizes it to
    /// the view; its sublayers are the caller's.
    pub fn host_layer(&self, root: &Layer) -> Result<(), WindowError> {
        let view = self.content_view()?;
        let s_layer = sel(c"setLayer:");
        let root_id: Id = root.obj.ptr();
        // SAFETY: docs AppKit/NSView/layer (its setter): takes a CALayer, which the
        // view retains; `view` is the window's live content view and `root` a live
        // layer.
        unsafe { MSG_VOID_ID(view, s_layer, root_id) }
        let s_wants = sel(c"setWantsLayer:");
        // SAFETY: docs AppKit/NSView/wantsLayer (its setter): YES, after the layer
        // was set, makes the view layer-hosting. `view` is live as above.
        unsafe { MSG_VOID_BOOL(view, s_wants, true) }
        Ok(())
    }
}

impl Drop for Window {
    fn drop(&mut self) {
        // `obj`'s own drop then releases the window.
        self.close();
    }
}

/// Whether a window side of `points` is accepted.
fn window_side_ok(points: f64) -> bool {
    points.is_finite() && points > 0.0 && points <= MAX_WINDOW_POINTS
}

/// `CAAutoresizingMask`, from <QuartzCore/CALayer.h>: which margins and sizes
/// follow the superlayer's size.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Autoresizing {
    /// `kCALayerMinYMargin` (8): the bottom margin stretches, so the layer keeps
    /// its distance from the top.
    pub flexible_bottom_margin: bool,
}

impl Autoresizing {
    fn mask(self) -> u32 {
        if self.flexible_bottom_margin { 8 } else { 0 }
    }
}

/// A `CALayer`, owned.
#[derive(Debug)]
pub struct Layer {
    obj: Object,
}

impl Layer {
    /// A new, empty layer. Needs the main thread, as everything shown in a window.
    pub fn new(_main: MainThread) -> Result<Layer, WindowError> {
        new_object(c"CALayer").map(|obj| Layer { obj })
    }

    fn send_bool(&self, name: &CStr, value: bool) {
        let s = sel(name);
        let this: Id = self.obj.ptr();
        // SAFETY: docs QuartzCore/CALayer/masksToBounds and docs
        // QuartzCore/CALayer/isHidden (their setters, the two `name`s used below):
        // each takes a BOOL.
        unsafe { MSG_VOID_BOOL(this, s, value) }
    }

    /// `addSublayer:`: `child` is drawn above the sublayers added before it. The
    /// superlayer retains it.
    pub fn add_sublayer(&self, child: &Layer) {
        let s = sel(c"addSublayer:");
        let this: Id = self.obj.ptr();
        let child_id: Id = child.obj.ptr();
        // SAFETY: docs QuartzCore/CALayer/addSublayer: takes a layer, which it
        // retains (removing it from any other superlayer first); `child` is live.
        unsafe { MSG_VOID_ID(this, s, child_id) }
    }

    /// `frame`, in the superlayer's points; refused unless finite.
    pub fn set_frame(&self, rect: Rect) -> Result<(), WindowError> {
        let r = rect.checked()?;
        let s = sel(c"setFrame:");
        let this: Id = self.obj.ptr();
        // SAFETY: docs QuartzCore/CALayer/frame (its setter): a CGRect by value,
        // finite and of non-negative size (checked), which Core Animation needs to
        // not raise an exception.
        unsafe { MSG_VOID_RECT(this, s, r) }
        Ok(())
    }

    /// `contentsScale`: pixels of its contents per point; refused unless finite
    /// and positive.
    pub fn set_contents_scale(&self, scale: f64) -> Result<(), WindowError> {
        if !(scale.is_finite() && scale > 0.0) {
            return Err(fail("a positive scale"));
        }
        let s = sel(c"setContentsScale:");
        let this: Id = self.obj.ptr();
        // SAFETY: docs QuartzCore/CALayer/contentsScale (its setter): a `CGFloat`,
        // finite and positive (checked).
        unsafe { MSG_VOID_F64(this, s, scale) }
        Ok(())
    }

    /// `masksToBounds`: draw nothing of the contents or sublayers outside the
    /// layer's bounds.
    pub fn set_masks_to_bounds(&self, masks: bool) {
        self.send_bool(c"setMasksToBounds:", masks);
    }

    /// `hidden`.
    pub fn set_hidden(&self, hidden: bool) {
        self.send_bool(c"setHidden:", hidden);
    }

    /// `autoresizingMask`.
    pub fn set_autoresizing(&self, resizing: Autoresizing) {
        let s = sel(c"setAutoresizingMask:");
        let this: Id = self.obj.ptr();
        let mask = resizing.mask();
        // SAFETY: docs QuartzCore/CALayer/autoresizingMask (its setter): a
        // `CAAutoresizingMask` (`unsigned int`), here 0 or kCALayerMinYMargin.
        unsafe { MSG_VOID_U32(this, s, mask) }
    }

    /// `contentsGravity = kCAGravityTopLeft`: contents keep their size (in pixels
    /// over `contentsScale`) and sit at the layer's top left ("top" meaning the
    /// largest y, per <QuartzCore/CALayer.h>), cut by the bounds if
    /// `masksToBounds`.
    pub fn set_gravity_top_left(&self) -> Result<(), WindowError> {
        // `kCAGravityTopLeft` is a data symbol, which the checker does not allow to
        // be declared; its value is this string.
        let value = ns_string("topLeft")?;
        let s = sel(c"setContentsGravity:");
        let this: Id = self.obj.ptr();
        let value_id: Id = value.ptr();
        // SAFETY: docs QuartzCore/CALayer/contentsGravity (its setter): an
        // NSString, copied; `value` is live.
        unsafe { MSG_VOID_ID(this, s, value_id) }
        Ok(())
    }

    /// Show `image` as the contents. The layer retains it.
    pub fn set_contents_image(&self, image: &Image) {
        self.set_contents(image.ptr.as_ptr());
    }

    /// Show `surface` as the contents. The layer retains it. See the module's
    /// modelling choices: this is the one undocumented behaviour used here.
    pub fn set_contents_surface(&self, surface: &Surface) {
        self.set_contents(surface.as_raw());
    }

    /// Show nothing.
    pub fn clear_contents(&self) {
        self.set_contents(std::ptr::null_mut());
    }

    fn set_contents(&self, contents: Id) {
        let s = sel(c"setContents:");
        let this: Id = self.obj.ptr();
        // SAFETY: docs QuartzCore/CALayer/contents (its setter): an `id`, retained
        // by the layer, or nil. Every caller above passes a live CGImage or
        // IOSurface it holds a reference to, or nil.
        unsafe { MSG_VOID_ID(this, s, contents) }
    }
}

/// Changes to layers inside `f` are applied together and without Core
/// Animation's implicit animations (`+[CATransaction begin]`,
/// `setDisableActions:YES`, `commit`, the last on every exit, a panic included).
pub fn without_animation<R>(_main: MainThread, f: impl FnOnce() -> R) -> Result<R, WindowError> {
    struct Commit(Id);
    impl Drop for Commit {
        fn drop(&mut self) {
            let s = sel(c"commit");
            // SAFETY: docs QuartzCore/CATransaction/commit: a class method that ends
            // the transaction `begin` started; it is begun and committed once each,
            // on one thread, nested properly by this function's scope.
            unsafe { MSG_VOID(self.0, s) }
        }
    }
    let c = class(c"CATransaction")?;
    let s_begin = sel(c"begin");
    // SAFETY: docs QuartzCore/CATransaction/begin: a class method that starts a
    // transaction; it is committed by `Commit`'s drop below.
    unsafe { MSG_VOID(c, s_begin) }
    let commit = Commit(c);
    let s_disable = sel(c"setDisableActions:");
    // SAFETY: docs QuartzCore/CATransaction/setDisableActions: a class method taking
    // a BOOL, for the current transaction.
    unsafe { MSG_VOID_BOOL(c, s_disable, true) }
    let out = f();
    drop(commit);
    Ok(out)
}

/// `kCGImageAlphaNoneSkipFirst` (6) | `kCGBitmapByteOrder32Little` (2 << 12), from
/// <CoreGraphics/CGImage.h>: each pixel a little-endian 32-bit `0x00RRGGBB`, so
/// the bytes B, G, R and an ignored one.
const XRGB_LITTLE: u32 = 0x2006;

/// The largest side of an image, in pixels, as of a Metal texture (`metal.rs`).
pub const MAX_IMAGE_SIDE: usize = 16_384;

/// A Core Graphics image of 32-bit pixels, owned (`CGImageRef`).
#[derive(Debug)]
pub struct Image {
    ptr: NonNull<c_void>,
}

impl Drop for Image {
    fn drop(&mut self) {
        let p: Id = self.ptr.as_ptr();
        // SAFETY: docs CoreFoundation/CFRelease: `p` is the image CGImageCreate
        // returned (owned, the Create rule), not NULL, released once, here.
        unsafe { CFRelease(p) }
    }
}

/// Releases a Core Foundation object made by a Create function, once.
struct Created(NonNull<c_void>);

impl Created {
    fn new(p: Id, what: &'static str) -> Result<Created, WindowError> {
        NonNull::new(p).map(Created).ok_or(fail(what))
    }
}

impl Drop for Created {
    fn drop(&mut self) {
        let p: Id = self.0.as_ptr();
        // SAFETY: docs CoreFoundation/CFRelease: `p` is a non-NULL object a Create
        // function returned to this `Created` alone, released once, here.
        unsafe { CFRelease(p) }
    }
}

/// The bytes per row of an image `width` pixels wide, and its pixel count, if
/// `pixels` pixels make exactly `width` by `height` and each side is 1 to
/// [`MAX_IMAGE_SIDE`].
fn image_layout(pixels: usize, width: usize, height: usize) -> Result<usize, WindowError> {
    let side_ok = |s: usize| (1..=MAX_IMAGE_SIDE).contains(&s);
    if !side_ok(width) || !side_ok(height) {
        return Err(fail("an image size"));
    }
    if width.checked_mul(height) != Some(pixels) {
        return Err(fail("an image's pixel count"));
    }
    width.checked_mul(4).ok_or(fail("an image size"))
}

impl Image {
    /// An image of `width` by `height` pixels, copied from `pixels`, in rows from
    /// the top, each `0x00RRGGBB`. `pixels` must hold exactly that many.
    pub fn new(pixels: &[u32], width: usize, height: usize) -> Result<Image, WindowError> {
        let bytes_per_row = image_layout(pixels.len(), width, height)?;
        let bytes: *const u8 = pixels.as_ptr().cast();
        let length =
            isize::try_from(std::mem::size_of_val(pixels)).map_err(|_| fail("an image size"))?;
        let no_allocator: Id = std::ptr::null_mut();
        // SAFETY: docs CoreFoundation/CFDataCreate: copies `length` bytes from
        // `bytes`; NULL is the default allocator. `bytes` and `length` are the
        // address and byte size of the borrowed slice `pixels`.
        let data = unsafe { CFDataCreate(no_allocator, bytes, length) };
        let data = Created::new(data, "CFDataCreate")?;
        let data_id: Id = data.0.as_ptr();
        // SAFETY: docs CoreGraphics/CGDataProviderCreateWithCFData: takes a CFData,
        // which the provider retains, and returns an owned provider or NULL.
        let provider = unsafe { CGDataProviderCreateWithCFData(data_id) };
        let provider = Created::new(provider, "CGDataProviderCreateWithCFData")?;
        // SAFETY: docs CoreGraphics/CGColorSpaceCreateDeviceRGB: takes nothing and
        // returns an owned colour space or NULL.
        let space = unsafe { CGColorSpaceCreateDeviceRGB() };
        let space = Created::new(space, "CGColorSpaceCreateDeviceRGB")?;
        let space_id: Id = space.0.as_ptr();
        let provider_id: Id = provider.0.as_ptr();
        let no_decode: *const f64 = std::ptr::null();
        // SAFETY: docs CoreGraphics/CGImageCreate: 8 bits a component and 32 a
        // pixel, `bytes_per_row` = 4 × width, so the provider's `height` rows
        // (exactly `width` × `height` × 4 bytes, checked by `image_layout`) are what
        // the image reads; the bitmap info is a documented combination; the colour
        // space and provider are live, and retained by the image; a NULL decode
        // array is allowed; the intent is kCGRenderingIntentDefault, 0.
        let image = unsafe {
            CGImageCreate(
                width,
                height,
                8,
                32,
                bytes_per_row,
                space_id,
                XRGB_LITTLE,
                provider_id,
                no_decode,
                false,
                0,
            )
        };
        let ptr = NonNull::new(image).ok_or(fail("CGImageCreate"))?;
        Ok(Image { ptr })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // These run under Miri: each is a check made before any foreign call.

    #[test]
    fn image_sizes_and_lengths_are_checked_before_any_call() {
        assert_eq!(image_layout(6, 3, 2), Ok(12));
        assert!(image_layout(5, 3, 2).is_err());
        assert!(image_layout(7, 3, 2).is_err());
        assert!(image_layout(0, 0, 0).is_err());
        assert!(image_layout(16_385, 16_385, 1).is_err());
        assert!(image_layout(usize::MAX, usize::MAX, 2).is_err());
        assert!(Image::new(&[0; 5], 3, 2).is_err());
        assert!(Image::new(&[], 0, 1).is_err());
    }

    #[test]
    fn rectangles_must_be_finite_and_not_negative() {
        let ok = Rect {
            x: -5.0,
            y: 1.5,
            width: 0.0,
            height: 3.0,
        };
        assert!(ok.checked().is_ok());
        for bad in [
            Rect { x: f64::NAN, ..ok },
            Rect {
                y: f64::INFINITY,
                ..ok
            },
            Rect { width: -1.0, ..ok },
            Rect {
                height: f64::NEG_INFINITY,
                ..ok
            },
        ] {
            assert!(bad.checked().is_err(), "{bad:?}");
        }
    }

    #[test]
    fn window_sides_and_waits_are_bounded() {
        assert!(window_side_ok(1.0) && window_side_ok(MAX_WINDOW_POINTS));
        for bad in [0.0, -1.0, f64::NAN, f64::INFINITY, 16_384.5] {
            assert!(!window_side_ok(bad), "{bad}");
        }
        assert_eq!(wait_seconds(Duration::ZERO), Ok(0.0));
        assert_eq!(wait_seconds(MAX_WAIT), Ok(86_400.0));
        assert!(wait_seconds(Duration::MAX).is_err());
    }

    #[test]
    fn accessors_follow_the_event_type() {
        let mouse = EventFields::of(1);
        assert!(mouse.location && !mouse.key_code && !mouse.characters && !mouse.scroll);
        let key = EventFields::of(10);
        assert!(!key.location && key.key_code && key.characters && !key.scroll);
        let flags = EventFields::of(12);
        assert!(flags.key_code && !flags.characters);
        let wheel = EventFields::of(22);
        assert!(wheel.location && wheel.scroll && !wheel.key_code);
        for kind in [
            0,
            13,
            14,
            15,
            16,
            17,
            18,
            19,
            20,
            21,
            23,
            24,
            28,
            29,
            30,
            usize::MAX,
        ] {
            assert_eq!(
                EventFields::of(kind),
                EventFields {
                    location: false,
                    key_code: false,
                    characters: false,
                    scroll: false
                },
                "{kind}"
            );
        }
    }

    #[test]
    fn character_reads_stay_below_the_length() {
        assert_eq!(units_to_read(0), 0);
        assert_eq!(units_to_read(3), 3);
        assert_eq!(units_to_read(usize::MAX), MAX_CHARACTERS);
    }

    #[test]
    fn style_masks_are_the_documented_values() {
        let none = Style {
            closable: false,
            miniaturizable: false,
            resizable: false,
        };
        assert_eq!(none.mask(), 1);
        let all = Style {
            closable: true,
            miniaturizable: true,
            resizable: true,
        };
        assert_eq!(all.mask(), 15);
        assert_eq!(Autoresizing::default().mask(), 0);
        assert_eq!(
            Autoresizing {
                flexible_bottom_margin: true
            }
            .mask(),
            8
        );
        assert_eq!(XRGB_LITTLE, 0x2006);
    }
}
