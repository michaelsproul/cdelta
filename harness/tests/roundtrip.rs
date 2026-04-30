//! Correctness scan: for a range of sizes, generate a source+target pair,
//! encode with xdelta3 (single-window, no-secondary, no-adler), and check
//! that our decoder reproduces the target.
//!
//! Surfaces the scale at which the cdelta decoder currently starts failing
//! so we can fix it separately from the benchmark.

use std::process::Command;

use cdelta_harness::{case01, Cdelta, VcdiffImpl};

fn synth_pair(size: usize) -> (Vec<u8>, Vec<u8>) {
    // Produce high-entropy source and a target made by rearranging big
    // chunks of source plus fresh random runs, so xdelta3 exercises the
    // NEAR/SAME address cache instead of collapsing to one huge COPY.
    let mut s = 0x9E3779B97F4A7C15u64;
    let mut rng = move || {
        s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        s
    };
    let mut src = vec![0u8; size];
    for chunk in src.chunks_mut(8) {
        let v = rng().to_le_bytes();
        chunk.copy_from_slice(&v[..chunk.len()]);
    }
    let mut tgt = Vec::with_capacity(size + size / 2);
    let mut pos = 0usize;
    while tgt.len() < size {
        let r = (rng() >> 16) as usize;
        let kind = r & 3;
        let len = 64 + (r >> 2) % 4096;
        let remaining = size - tgt.len();
        let take = len.min(remaining);
        match kind {
            0 => {
                // fresh random bytes
                let mut buf = vec![0u8; take];
                for chunk in buf.chunks_mut(8) {
                    let v = rng().to_le_bytes();
                    chunk.copy_from_slice(&v[..chunk.len()]);
                }
                tgt.extend_from_slice(&buf);
            }
            1 => {
                // run of a single byte
                let b = (rng() & 0xFF) as u8;
                tgt.extend(std::iter::repeat(b).take(take));
            }
            _ => {
                // copy a chunk from src at pos
                let off = (r >> 12) % src.len();
                let end = (off + take).min(src.len());
                tgt.extend_from_slice(&src[off..end]);
                pos = end;
            }
        }
        let _ = pos;
    }
    tgt.truncate(size);
    (src, tgt)
}

fn encode_simple(source: &[u8], target: &[u8]) -> Vec<u8> {
    let dir = tempfile::tempdir().expect("tempdir");
    let sp = dir.path().join("src");
    let tp = dir.path().join("tgt");
    let dp = dir.path().join("delta");
    std::fs::write(&sp, source).unwrap();
    std::fs::write(&tp, target).unwrap();

    // xdelta3 -B minimum is 524288; -W minimum is something similar.
    let win = (source.len().max(target.len()).max(1 << 20) + (1 << 16)).to_string();
    let status = Command::new("xdelta3")
        .args(["-e", "-f", "-n", "-S", "none",
               "-B", &win, "-W", &win, "-s"])
        .arg(&sp).arg(&tp).arg(&dp)
        .status()
        .expect("run xdelta3");
    assert!(status.success(), "xdelta3 -e failed: {status}");
    std::fs::read(&dp).unwrap()
}

#[test]
fn size_scan_roundtrip() {
    // Smallest first so a failure points at the smallest broken size.
    // 1 << 24 exceeds xdelta3's -W max of 16777216; stop at 1 << 23.
    let sizes = [1 << 10, 1 << 14, 1 << 17, 1 << 19, 1 << 20, 1 << 22, 1 << 23];
    for &n in &sizes {
        let (src, tgt) = synth_pair(n);
        let delta = encode_simple(&src, &tgt);
        let got = Cdelta::decode(&delta, &src)
            .unwrap_or_else(|e| panic!("decode failed at size {n}: {e} (delta={} bytes)", delta.len()));
        assert_eq!(got.len(), tgt.len(), "length mismatch at size {n}");
        assert_eq!(got, tgt, "content mismatch at size {n}");
        eprintln!("size {n} OK (delta={} bytes)", delta.len());
    }
}

/// Roundtrip the real case01 fixture — same path as the bench.
#[test]
fn case01_roundtrip() {
    let source = std::fs::read(case01::source()).expect("read source");
    let target = std::fs::read(case01::target()).expect("read target");
    let delta = encode_simple(&source, &target);
    eprintln!(
        "case01: source={} target={} delta={}",
        source.len(),
        target.len(),
        delta.len()
    );
    let got = Cdelta::decode(&delta, &source).expect("cdelta decode");
    assert_eq!(got.len(), target.len(), "length mismatch");
    assert_eq!(got, target, "content mismatch");
}
