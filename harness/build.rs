//! Compile the cdelta encoder and decoder C sources into the harness crate.
//!
//! These are the same sources the Isabelle/AutoCorres2 sessions lift, so the
//! benchmark measures exactly what will eventually be proven.

use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("harness is under workspace root")
        .to_path_buf();

    let enc = workspace.join("encoder/vcdiff_enc.c");
    let dec = workspace.join("decoder/vcdiff_dec.c");

    println!("cargo:rerun-if-changed={}", enc.display());
    println!("cargo:rerun-if-changed={}", dec.display());

    let mut build = cc::Build::new();
    build
        .file(&enc)
        .file(&dec)
        .warnings(true)
        .flag_if_supported("-std=gnu11")
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-variable");
    build.compile("cdelta");
}
