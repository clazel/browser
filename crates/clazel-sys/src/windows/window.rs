//! Windows: the host's window (phase-5.md item 5.22a). Open one, read its
//! messages and copy pixels into it.
//!
//! The window procedure is `DefWindowProcW` itself, so no callback is defined
//! in Rust. Messages sent straight to the procedure, such as `WM_SIZE`, are
//! therefore never seen here; the size is read with [`client_size`] and an
//! ended window with [`is_window`]. What each message means is decided in
//! `clazel-window`.
//!
//! The host's process is not sandboxed and these calls take no page-derived
//! pointer: [`draw_bgra`] reads a slice whose length it has checked.

use std::ffi::c_void;

use super::{Bool, Dword, Handle, SpawnError, last, wide};
use crate::Errno;

/// `WS_OVERLAPPEDWINDOW | WS_VISIBLE`.
const WINDOW_STYLE: Dword = 0x00CF_0000 | 0x1000_0000;
/// `CW_USEDEFAULT`: the system picks the position and size.
const USE_DEFAULT: i32 = i32::MIN;
/// `PM_REMOVE`.
const REMOVE: u32 = 1;
/// `QS_ALLINPUT`.
const ALL_INPUT: Dword = 0x04FF;
/// `IDC_ARROW`, a resource id in the pointer's place.
const ARROW: usize = 32512;
/// `DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2`.
const PER_MONITOR_V2: isize = -4;
/// `ERROR_CLASS_ALREADY_EXISTS`.
const CLASS_EXISTS: i32 = 1410;
/// `ERROR_INVALID_PARAMETER`.
const INVALID_PARAMETER: i32 = 87;

#[repr(C)]
struct WndClassExW {
    size: Dword,
    style: Dword,
    window_procedure: usize,
    class_extra: i32,
    window_extra: i32,
    instance: Handle,
    icon: Handle,
    cursor: Handle,
    background: Handle,
    menu_name: *const u16,
    class_name: *const u16,
    small_icon: Handle,
}

#[repr(C)]
struct Point {
    x: i32,
    y: i32,
}

#[repr(C)]
struct Msg {
    window: Handle,
    message: u32,
    w_param: usize,
    l_param: isize,
    time: Dword,
    point: Point,
    private: Dword,
}

#[repr(C)]
struct Rect {
    left: i32,
    top: i32,
    right: i32,
    bottom: i32,
}

#[repr(C)]
struct BitmapInfoHeader {
    size: Dword,
    width: i32,
    height: i32,
    planes: u16,
    bit_count: u16,
    compression: Dword,
    size_image: Dword,
    x_pels_per_meter: i32,
    y_pels_per_meter: i32,
    colors_used: Dword,
    colors_important: Dword,
}

#[repr(C)]
struct BitmapInfo {
    header: BitmapInfoHeader,
    colors: [u32; 1],
}

#[link(name = "user32")]
#[link(name = "gdi32")]
#[link(name = "kernel32")]
// SAFETY: docs RegisterClassExW, DefWindowProcW, LoadCursorW, CreateWindowExW,
// DestroyWindow, IsWindow, PeekMessageW, TranslateMessage, DispatchMessageW,
// MsgWaitForMultipleObjects, GetClientRect, ScreenToClient, GetDC, ReleaseDC,
// SetProcessDpiAwarenessContext (user32, winuser.h); docs SetDIBitsToDevice
// (gdi32, wingdi.h); docs GetModuleHandleW (kernel32, libloaderapi.h). The
// declarations below match those prototypes on 64-bit Windows: `BOOL`,
// `DWORD`, `UINT` and `int` are 32-bit, `ATOM` is 16-bit, `WPARAM` is
// `usize`, `LPARAM` and `LRESULT` are `isize`, and `HWND`, `HINSTANCE`,
// `HCURSOR`, `HDC` and `DPI_AWARENESS_CONTEXT` are pointer-sized handles carried
// as `isize`. `LoadCursorW`'s name is declared `usize` because it is passed a
// resource id, not a string, in the same register. `system` is the Windows
// calling convention. None is `pub` or declared `safe`, so every call needs its
// own `unsafe` block.
unsafe extern "system" {
    fn RegisterClassExW(class: *const WndClassExW) -> u16;
    fn DefWindowProcW(window: Handle, message: u32, w_param: usize, l_param: isize) -> isize;
    fn LoadCursorW(instance: Handle, name: usize) -> Handle;
    fn CreateWindowExW(
        ex_style: Dword,
        class_name: *const u16,
        window_name: *const u16,
        style: Dword,
        x: i32,
        y: i32,
        width: i32,
        height: i32,
        parent: Handle,
        menu: Handle,
        instance: Handle,
        param: *mut c_void,
    ) -> Handle;
    fn DestroyWindow(window: Handle) -> Bool;
    fn IsWindow(window: Handle) -> Bool;
    fn PeekMessageW(message: *mut Msg, window: Handle, min: u32, max: u32, remove: u32) -> Bool;
    fn TranslateMessage(message: *const Msg) -> Bool;
    fn DispatchMessageW(message: *const Msg) -> isize;
    fn MsgWaitForMultipleObjects(
        count: Dword,
        handles: *const Handle,
        wait_all: Bool,
        milliseconds: Dword,
        wake_mask: Dword,
    ) -> Dword;
    fn GetClientRect(window: Handle, rect: *mut Rect) -> Bool;
    fn ScreenToClient(window: Handle, point: *mut Point) -> Bool;
    fn GetDC(window: Handle) -> Handle;
    fn ReleaseDC(window: Handle, dc: Handle) -> i32;
    fn SetProcessDpiAwarenessContext(context: isize) -> Bool;
    fn SetDIBitsToDevice(
        dc: Handle,
        x: i32,
        y: i32,
        width: Dword,
        height: Dword,
        x_source: i32,
        y_source: i32,
        start_scan: u32,
        lines: u32,
        bits: *const c_void,
        info: *const BitmapInfo,
        color_use: u32,
    ) -> i32;
    fn GetModuleHandleW(name: *const u16) -> Handle;
}

/// A window this module created. An ended window's handle makes the calls below
/// fail or report nothing; it reads no memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WindowHandle(Handle);

/// A message as the system gave it, with no meaning attached.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RawMessage {
    /// `WM_*`.
    pub message: u32,
    /// `wParam`.
    pub w_param: usize,
    /// `lParam`.
    pub l_param: isize,
}

/// Use physical pixels for this process's windows. False if the process's
/// awareness was already set, which leaves it as it was.
pub fn set_dpi_aware() -> bool {
    // SAFETY: docs SetProcessDpiAwarenessContext: takes one of the documented
    // context values, here DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2, and reads
    // no memory.
    let ok = unsafe { SetProcessDpiAwarenessContext(PER_MONITOR_V2) };
    ok != 0
}

/// Open a visible window of the system's default size, owned by the calling
/// thread, which must then read its messages with [`next_message`].
pub fn create_window(title: &str) -> Result<WindowHandle, SpawnError> {
    let class_name = wide("clazel-window")?;
    let window_name = wide(title)?;
    let class_ptr = class_name.as_ptr();
    let window_ptr = window_name.as_ptr();
    let no_name: *const u16 = std::ptr::null();
    // SAFETY: docs GetModuleHandleW: a null name gives this executable's handle,
    // which is not reference counted and need not be freed.
    let instance = unsafe { GetModuleHandleW(no_name) };
    // SAFETY: docs LoadCursorW: instance 0 with a predefined id gives a shared
    // system cursor, which is not freed. A 0 result means no cursor, which the
    // class allows.
    let cursor = unsafe { LoadCursorW(0, ARROW) };
    let class = WndClassExW {
        size: 80,
        style: 0,
        window_procedure: DefWindowProcW as *const () as usize,
        class_extra: 0,
        window_extra: 0,
        instance,
        icon: 0,
        cursor,
        background: 0,
        menu_name: no_name,
        class_name: class_ptr,
        small_icon: 0,
    };
    let class_slot: *const WndClassExW = &raw const class;
    // SAFETY: docs RegisterClassExW: `class_slot` points to the live local
    // `class`, whose `size` is that of WNDCLASSEXW on 64-bit Windows (a test
    // checks it) and whose name is NUL-terminated and live until the call
    // returns; the system copies what it keeps. The procedure is DefWindowProcW.
    let atom = unsafe { RegisterClassExW(class_slot) };
    if atom == 0 {
        let e = last("RegisterClassExW");
        if !matches!(e, SpawnError::Call(_, Errno(CLASS_EXISTS))) {
            return Err(e);
        }
    }
    let no_param: *mut c_void = std::ptr::null_mut();
    // SAFETY: docs CreateWindowExW: both strings are NUL-terminated locals live
    // for the call; the class is registered above; parent and menu are 0; the
    // style and CW_USEDEFAULT values are the documented ones, and `param` is
    // null because DefWindowProcW reads nothing through it.
    let window = unsafe {
        CreateWindowExW(
            0,
            class_ptr,
            window_ptr,
            WINDOW_STYLE,
            USE_DEFAULT,
            USE_DEFAULT,
            USE_DEFAULT,
            USE_DEFAULT,
            0,
            0,
            instance,
            no_param,
        )
    };
    if window == 0 {
        return Err(last("CreateWindowExW"));
    }
    Ok(WindowHandle(window))
}

/// Take the calling thread's next message if there is one, translate it and send
/// it to its window. Returns only when the procedure does, so a drag of the
/// window's frame blocks this thread for as long as the drag lasts.
pub fn next_message() -> Option<RawMessage> {
    let mut msg = Msg {
        window: 0,
        message: 0,
        w_param: 0,
        l_param: 0,
        time: 0,
        point: Point { x: 0, y: 0 },
        private: 0,
    };
    let slot: *mut Msg = &raw mut msg;
    // SAFETY: docs PeekMessageW: `slot` points to the live local `msg`, which the
    // call fills if it returns nonzero; window 0 and a 0..0 range mean every
    // message of this thread; PM_REMOVE takes it from the queue.
    let got = unsafe { PeekMessageW(slot, 0, 0, 0, REMOVE) };
    if got == 0 {
        return None;
    }
    let message: *const Msg = &raw const msg;
    // SAFETY: docs TranslateMessage: `message` points to the MSG PeekMessageW
    // filled; it may post a WM_CHAR and keeps no pointer.
    let _ = unsafe { TranslateMessage(message) };
    // SAFETY: docs DispatchMessageW: `message` points to the same MSG, and the
    // procedure it reaches is DefWindowProcW or the system's own.
    let _ = unsafe { DispatchMessageW(message) };
    Some(RawMessage {
        message: msg.message,
        w_param: msg.w_param,
        l_param: msg.l_param,
    })
}

/// Sleep until the calling thread has a message or `milliseconds` pass.
pub fn wait_for_message(milliseconds: u32) {
    let no_handles: *const Handle = std::ptr::null();
    // SAFETY: docs MsgWaitForMultipleObjects: a count of 0 means the handle
    // array is not read, so it may be null; QS_ALLINPUT is a documented mask.
    let _ = unsafe { MsgWaitForMultipleObjects(0, no_handles, 0, milliseconds, ALL_INPUT) };
}

/// Whether the window still exists. The system destroys it when the user
/// closes it, since `DefWindowProcW` handles `WM_CLOSE`.
pub fn is_window(window: WindowHandle) -> bool {
    // SAFETY: docs IsWindow: takes any handle value and reads no memory.
    let ok = unsafe { IsWindow(window.0) };
    ok != 0
}

/// Destroy the window. Only the thread that created it may do this; on any
/// other thread the system refuses and this returns an error.
pub fn destroy_window(window: WindowHandle) -> Result<(), SpawnError> {
    // SAFETY: docs DestroyWindow: takes a handle and reads no caller memory; the
    // system refuses a handle of another thread.
    let ok = unsafe { DestroyWindow(window.0) };
    if ok == 0 {
        return Err(last("DestroyWindow"));
    }
    Ok(())
}

/// The client area's width and height in pixels.
pub fn client_size(window: WindowHandle) -> Result<(u32, u32), SpawnError> {
    let mut rect = Rect {
        left: 0,
        top: 0,
        right: 0,
        bottom: 0,
    };
    let slot: *mut Rect = &raw mut rect;
    // SAFETY: docs GetClientRect: `slot` points to the live local `rect`, which
    // the call fills. Any thread may ask.
    let ok = unsafe { GetClientRect(window.0, slot) };
    if ok == 0 {
        return Err(last("GetClientRect"));
    }
    // The documented left and top are 0.
    Ok((
        u32::try_from(rect.right).unwrap_or(0),
        u32::try_from(rect.bottom).unwrap_or(0),
    ))
}

/// A point on the screen as a point in the client area.
pub fn screen_to_client(window: WindowHandle, x: i32, y: i32) -> Result<(i32, i32), SpawnError> {
    let mut point = Point { x, y };
    let slot: *mut Point = &raw mut point;
    // SAFETY: docs ScreenToClient: `slot` points to the live local `point`, which
    // the call rewrites in place.
    let ok = unsafe { ScreenToClient(window.0, slot) };
    if ok == 0 {
        return Err(last("ScreenToClient"));
    }
    Ok((point.x, point.y))
}

/// Copy `width` by `height` pixels to the client area's top left corner:
/// `pixels` holds rows from the top, each pixel blue, green, red and an ignored
/// byte. Any other length is `ERROR_INVALID_PARAMETER`. A size of zero draws
/// nothing.
pub fn draw_bgra(
    window: WindowHandle,
    pixels: &[u8],
    width: u32,
    height: u32,
) -> Result<(), SpawnError> {
    let invalid = SpawnError::Call("draw_bgra", Errno(INVALID_PARAMETER));
    let expected = u64::from(width)
        .checked_mul(u64::from(height))
        .and_then(|n| n.checked_mul(4));
    if expected != u64::try_from(pixels.len()).ok() {
        return Err(invalid);
    }
    let (Ok(signed_width), Ok(signed_height)) = (i32::try_from(width), i32::try_from(height))
    else {
        return Err(invalid);
    };
    if width == 0 || height == 0 {
        return Ok(());
    }
    let info = BitmapInfo {
        header: BitmapInfoHeader {
            size: 40,
            width: signed_width,
            // Negative: the rows run from the top.
            height: signed_height.saturating_neg(),
            planes: 1,
            bit_count: 32,
            compression: 0,
            size_image: 0,
            x_pels_per_meter: 0,
            y_pels_per_meter: 0,
            colors_used: 0,
            colors_important: 0,
        },
        colors: [0],
    };
    let head: *const BitmapInfo = &raw const info;
    let bits: *const c_void = pixels.as_ptr().cast();
    // SAFETY: docs GetDC: gives a device context for the window's client area, or
    // 0 on failure, and is released below. Any thread may ask.
    let dc = unsafe { GetDC(window.0) };
    if dc == 0 {
        return Err(last("GetDC"));
    }
    // SAFETY: docs SetDIBitsToDevice: `dc` is live; `head` points to the live
    // local `info`, a 32-bit BI_RGB top-down header, which reads no colour table;
    // `bits` points to `pixels`, whose length is checked above to be exactly
    // width × height × 4, and the call reads `height` rows of `width` pixels of
    // it. 0 is DIB_RGB_COLORS. It keeps no pointer.
    let n = unsafe { SetDIBitsToDevice(dc, 0, 0, width, height, 0, 0, 0, height, bits, head, 0) };
    let failed = (n == 0).then(|| last("SetDIBitsToDevice"));
    // SAFETY: docs ReleaseDC: releases the context GetDC gave above for this same
    // window; it is not used afterwards.
    let _ = unsafe { ReleaseDC(window.0, dc) };
    match failed {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layouts_match_the_headers() {
        // WNDCLASSEXW's `cbSize` as written above, and the sizes winuser.h and
        // wingdi.h give on 64-bit Windows.
        assert_eq!(size_of::<WndClassExW>(), 80);
        assert_eq!(size_of::<Msg>(), 48);
        assert_eq!(size_of::<Rect>(), 16);
        assert_eq!(size_of::<BitmapInfoHeader>(), 40);
        assert_eq!(size_of::<BitmapInfo>(), 44);
    }

    #[test]
    fn draw_refuses_a_wrong_length_before_any_call() {
        let handle = WindowHandle(0);
        let refused = |pixels: &[u8], w, h| {
            matches!(
                draw_bgra(handle, pixels, w, h),
                Err(SpawnError::Call("draw_bgra", Errno(INVALID_PARAMETER)))
            )
        };
        assert!(refused(&[0; 3], 1, 1));
        assert!(refused(&[0; 5], 1, 1));
        assert!(refused(&[], 1, 1));
        assert!(refused(&[0; 4], u32::MAX, u32::MAX));
    }
}
