//! Oracle + cdelta wrapper for benchmarking.
//!
//! `Xdelta3` wraps the `xdelta3` crate (bindings to libxdelta).
//! `Cdelta` calls into our verified-candidate C (`encoder/vcdiff_enc.c`,
//! `decoder/vcdiff_dec.c`) via FFI.

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    Encode,
    Decode(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Encode => write!(f, "encode failed"),
            Error::Decode(m) => write!(f, "decode: {}", m),
        }
    }
}

impl std::error::Error for Error {}

pub type Bytes = Vec<u8>;

/// Parameter order mirrors xdelta3-rs: `target` is the new data, `source`
/// the original. `source` is the full buffer; VCDIFF source-segment framing
/// happens inside the encoder/decoder.
pub trait VcdiffImpl {
    const NAME: &'static str;
    fn encode(target: &[u8], source: &[u8]) -> Result<Bytes, Error>;
    fn decode(delta: &[u8], source: &[u8]) -> Result<Bytes, Error>;
}

pub mod xdelta3_oracle {
    use super::*;

    pub struct Xdelta3;

    impl VcdiffImpl for Xdelta3 {
        const NAME: &'static str = "xdelta3";

        fn encode(target: &[u8], source: &[u8]) -> Result<Bytes, Error> {
            xdelta3::encode(target, source).ok_or(Error::Encode)
        }

        fn decode(delta: &[u8], source: &[u8]) -> Result<Bytes, Error> {
            xdelta3::decode(delta, source)
                .ok_or_else(|| Error::Decode("xdelta3 returned None".into()))
        }
    }
}

pub mod cdelta {
    use std::sync::Mutex;

    use super::*;

    /// Encoder + decoder both use file-scope static state (required for
    /// AutoCorres2 heap-lift tractability — see feedback_autocorres_c_subset.md).
    /// That means concurrent calls from Rust would race. Serialise them.
    static LOCK: Mutex<()> = Mutex::new(());

    pub struct Cdelta;

    impl VcdiffImpl for Cdelta {
        const NAME: &'static str = "cdelta";

        fn encode(target: &[u8], source: &[u8]) -> Result<Bytes, Error> {
            let _g = LOCK.lock().unwrap();
            let margin: usize = 64;
            let section_cap = target.len() + margin;
            let out_cap = target.len() + source.len() / 8 + 1024;
            let mut head = vec![0u32; 1usize << 16];
            let mut next_arr = vec![0u32; source.len().max(4)];
            let mut pending = vec![0u8; target.len().max(1)];
            let mut data_sec = vec![0u8; section_cap];
            let mut inst_sec = vec![0u8; section_cap];
            let mut addr_sec = vec![0u8; section_cap];
            let mut out = vec![0u8; out_cap];
            let n = unsafe {
                ffi::vcdiff_encode(
                    out.as_mut_ptr(),
                    out_cap as u32,
                    source.as_ptr() as *mut u8,
                    source.len() as u32,
                    target.as_ptr() as *mut u8,
                    target.len() as u32,
                    head.as_mut_ptr(),
                    next_arr.as_mut_ptr(),
                    pending.as_mut_ptr(), pending.len() as u32,
                    data_sec.as_mut_ptr(), section_cap as u32,
                    inst_sec.as_mut_ptr(), section_cap as u32,
                    addr_sec.as_mut_ptr(), section_cap as u32,
                )
            };
            if n == 0 {
                return Err(Error::Encode);
            }
            out.truncate(n as usize);
            Ok(out)
        }

        fn decode(delta: &[u8], source: &[u8]) -> Result<Bytes, Error> {
            let _g = LOCK.lock().unwrap();
            // Target window length is stored in the delta header; we don't
            // peek it here, so over-provision. Any real target is ≤ a
            // small multiple of source+delta for normal use.
            let cap = (source.len() + delta.len()) * 4 + 4096;
            let mut out = vec![0u8; cap];
            let mut out_len: u32 = 0;
            let rc = unsafe {
                ffi::vcdiff_decode(
                    delta.as_ptr() as *mut u8,
                    delta.len() as u32,
                    source.as_ptr() as *mut u8,
                    source.len() as u32,
                    out.as_mut_ptr(),
                    cap as u32,
                    &mut out_len,
                )
            };
            if rc != 0 {
                return Err(Error::Decode(format!("cdelta decode error code {}", rc)));
            }
            out.truncate(out_len as usize);
            Ok(out)
        }
    }

    pub mod ffi {
        extern "C" {
            pub fn vcdiff_encode(
                out: *mut u8, out_cap: u32,
                src: *mut u8, src_len: u32,
                tgt: *mut u8, tgt_len: u32,
                head: *mut u32,
                next_arr: *mut u32,
                pending: *mut u8, pending_cap: u32,
                data_sec: *mut u8, data_cap: u32,
                inst_sec: *mut u8, inst_cap: u32,
                addr_sec: *mut u8, addr_cap: u32,
            ) -> u32;

            pub fn vcdiff_decode(
                patch: *mut u8,
                patch_len: u32,
                src: *mut u8,
                src_len: u32,
                out: *mut u8,
                out_cap: u32,
                out_len: *mut u32,
            ) -> i32;
        }
    }
}

pub use cdelta::Cdelta;
pub use xdelta3_oracle::Xdelta3;

/// Test-data paths relative to the workspace root.
pub mod case01 {
    use std::path::PathBuf;

    fn workspace_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("harness is under workspace root")
            .to_path_buf()
    }

    pub fn source() -> PathBuf {
        workspace_root().join("test-data/case01/source_state_bytes.bin")
    }
    pub fn target() -> PathBuf {
        workspace_root().join("test-data/case01/target_state_bytes.bin")
    }
    pub fn diff() -> PathBuf {
        workspace_root().join("test-data/case01/state_diff_bytes.bin")
    }

    pub fn load_all() -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        let s = std::fs::read(source()).expect("read source");
        let t = std::fs::read(target()).expect("read target");
        let d = std::fs::read(diff()).expect("read diff");
        (s, t, d)
    }
}
