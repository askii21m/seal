//! `seal-wasm`: a thin, zero-dependency wasm32 shim exposing the Seal
//! compiler to JavaScript via the raw C ABI (no wasm-bindgen).
//!
//! The `seal` crate stays dependency-free; this glue does only
//! string marshalling across the wasm boundary, then calls the SAME pure
//! `compile()` + `result_to_json()` the CLI uses. So a browser cannot derive a
//! different address than the CLI for identical input -- the single shared code
//! path (a fund-loss safety property) extends to the web.
//!
//! ABI (the JS side lives in `web/seal.js`):
//! ```text
//!   bs_alloc(len) -> ptr            JS allocates a buffer in wasm memory
//!   bs_free(ptr, len)               JS frees a buffer
//!   bs_compile(srcPtr, srcLen, argsPtr, argsLen, target, allowUnproven) -> outPtr
//!       returns a length-prefixed buffer: [u32 LE jsonLen][jsonLen UTF-8 bytes].
//!       JS reads jsonLen, decodes the JSON, then bs_free(outPtr, 4 + jsonLen).
//!   argsPtr == 0 (null) means "no args".
//!   target: 0=Check 1=Lower 2=Certify 3=Cost else=Fund.
//! ```
//!
//! Totality: invalid UTF-8 input is reported as a structured JSON error, never a
//! trap. The compiler itself is already total and deterministic.

use std::alloc::{alloc as rust_alloc, dealloc, Layout};

use seal::compile::{compile, result_to_json, CompileOptions, Target};

/// Allocate `len` bytes in wasm linear memory; JS writes the UTF-8 input here
/// before calling [`bs_compile`]. Returns null on a zero/oversized request.
#[unsafe(no_mangle)]
pub extern "C" fn bs_alloc(len: usize) -> *mut u8 {
    if len == 0 {
        return std::ptr::null_mut();
    }
    match Layout::from_size_align(len, 1) {
        Ok(layout) => unsafe { rust_alloc(layout) },
        Err(_) => std::ptr::null_mut(),
    }
}

/// Free a buffer from [`bs_alloc`] or [`bs_compile`]. For a `bs_compile` result,
/// pass `len = 4 + jsonLen` (the whole length-prefixed buffer).
#[unsafe(no_mangle)]
pub extern "C" fn bs_free(ptr: *mut u8, len: usize) {
    if ptr.is_null() || len == 0 {
        return;
    }
    if let Ok(layout) = Layout::from_size_align(len, 1) {
        unsafe { dealloc(ptr, layout) };
    }
}

/// Compile `source` (+ optional `args` JSON) and return the result as JSON.
///
/// Returns a heap buffer `[u32 LE jsonLen][jsonLen bytes]`; JS reads the length,
/// decodes the JSON, then calls `bs_free(out, 4 + jsonLen)`. Returns null only
/// on allocation failure.
///
/// # Safety
/// `src_ptr`/`args_ptr` must each point to the number of readable bytes given by
/// `src_len`/`args_len`, as allocated by [`bs_alloc`]. `args_ptr` may be null.
#[unsafe(no_mangle)]
pub extern "C" fn bs_compile(
    src_ptr: *const u8,
    src_len: usize,
    args_ptr: *const u8,
    args_len: usize,
    target: u32,
    allow_unproven: u32,
) -> *mut u8 {
    let source = match unsafe { read_str(src_ptr, src_len) } {
        Some(s) => s,
        None => return pack(r#"{"ok":false,"error":"source is not valid UTF-8"}"#),
    };
    let args = if args_ptr.is_null() {
        None
    } else {
        match unsafe { read_str(args_ptr, args_len) } {
            Some(s) => Some(s),
            None => return pack(r#"{"ok":false,"error":"args is not valid UTF-8"}"#),
        }
    };
    let target = match target {
        0 => Target::Check,
        1 => Target::Lower,
        2 => Target::Certify,
        3 => Target::Cost,
        _ => Target::Fund,
    };
    let opts = CompileOptions { allow_unproven: allow_unproven != 0, hrp: "bc" };
    let result = compile(source, args, target, opts);
    let json = result_to_json(&result, source, args);
    pack(&json)
}

/// View `len` bytes at `ptr` as a UTF-8 `&str`, or `None` on null / invalid
/// UTF-8.
///
/// # Safety
/// `ptr` must point to `len` readable bytes (or be null).
unsafe fn read_str<'a>(ptr: *const u8, len: usize) -> Option<&'a str> {
    if ptr.is_null() {
        return None;
    }
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    std::str::from_utf8(bytes).ok()
}

/// Box a string into a freshly-allocated `[u32 LE len][bytes]` buffer; ownership
/// transfers to the caller (freed via [`bs_free`]).
fn pack(s: &str) -> *mut u8 {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let total = 4 + len;
    let Ok(layout) = Layout::from_size_align(total, 1) else {
        return std::ptr::null_mut();
    };
    unsafe {
        let buf = rust_alloc(layout);
        if buf.is_null() {
            return std::ptr::null_mut();
        }
        let le = (len as u32).to_le_bytes();
        std::ptr::copy_nonoverlapping(le.as_ptr(), buf, 4);
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), buf.add(4), len);
        buf
    }
}
