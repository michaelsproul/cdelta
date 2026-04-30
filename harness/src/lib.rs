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
    use super::*;

    pub struct Cdelta;

    impl VcdiffImpl for Cdelta {
        const NAME: &'static str = "cdelta";

        /// Our encoder is the no-source single-ADD encoder. `source` is
        /// ignored; the result round-trips via any VCDIFF decoder but is
        /// not a compressed delta against `source`. This exists so the
        /// benchmark bar chart is comparable-shaped, not because it's a
        /// fair encode comparison.
        fn encode(target: &[u8], _source: &[u8]) -> Result<Bytes, Error> {
            // Upper bound: 5-byte header + 1-byte win indicator + up to 5
            // bytes for each of {dlen, tgt_len, data_len, inst_len, addr_len}
            // + 1-byte delta indicator + 1-byte ADD opcode + 5-byte size
            // varint + target bytes. Pad to 64 to be safe.
            let cap = target.len() + 64;
            let mut out = vec![0u8; cap];
            let n = unsafe {
                ffi::vcdiff_encode_add(
                    out.as_mut_ptr(),
                    cap as u32,
                    target.as_ptr() as *mut u8,
                    target.len() as u32,
                )
            };
            if n == 0 {
                return Err(Error::Encode);
            }
            out.truncate(n as usize);
            Ok(out)
        }

        fn decode(delta: &[u8], source: &[u8]) -> Result<Bytes, Error> {
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
            pub fn vcdiff_encode_add(
                out: *mut u8,
                out_cap: u32,
                target: *mut u8,
                target_len: u32,
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
