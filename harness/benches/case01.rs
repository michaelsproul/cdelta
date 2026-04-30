//! Benchmark cdelta vs xdelta3 on the case01 fixture.
//!
//! Decode is the meaningful comparison: both implementations consume the
//! same delta and reconstruct the target.
//!
//! The delta committed under test-data/case01 is multi-window with LZMA
//! secondary compression, neither of which our decoder supports yet. We
//! regenerate a single-window, no-secondary delta at bench startup so both
//! decoders see the same byte stream.
//!
//! Encode is included for completeness, but cdelta's encoder is a no-source
//! single-ADD emitter (essentially memcpy + framing). Expect it to look
//! fast on absolute numbers and useless on compression ratio.

use std::hint::black_box;
use std::path::Path;
use std::process::Command;

use cdelta_harness::{case01, Cdelta, VcdiffImpl, Xdelta3};
use criterion::{criterion_group, criterion_main, Criterion, Throughput};

fn bench_encode<I: VcdiffImpl>(c: &mut Criterion, source: &[u8], target: &[u8]) {
    let mut g = c.benchmark_group(format!("case01/encode/{}", I::NAME));
    g.throughput(Throughput::Bytes(target.len() as u64));
    g.sample_size(10);
    g.bench_function("encode", |b| {
        b.iter(|| match I::encode(black_box(target), black_box(source)) {
            Ok(v) => black_box(v),
            Err(e) => panic!("{}: encode failed: {}", I::NAME, e),
        })
    });
    g.finish();
}

fn bench_decode<I: VcdiffImpl>(c: &mut Criterion, source: &[u8], delta: &[u8], expected: &[u8]) {
    let mut g = c.benchmark_group(format!("case01/decode/{}", I::NAME));
    g.throughput(Throughput::Bytes(expected.len() as u64));
    g.sample_size(20);
    g.bench_function("decode", |b| {
        b.iter(|| match I::decode(black_box(delta), black_box(source)) {
            Ok(v) => black_box(v),
            Err(e) => panic!("{}: decode failed: {}", I::NAME, e),
        })
    });
    g.finish();
}

/// Regenerate a delta the cdelta decoder can handle: single window
/// (large `-B`/`-W`), no secondary compression, no adler32. Runs once per
/// bench invocation.
fn regenerate_simple_delta(source: &Path, target: &Path) -> Vec<u8> {
    let out = tempfile::NamedTempFile::new().expect("tempfile");
    let src_len = std::fs::metadata(source).expect("source stat").len();
    let tgt_len = std::fs::metadata(target).expect("target stat").len();
    let win = src_len.max(tgt_len) + (1 << 16); // headroom
    let status = Command::new("xdelta3")
        .args([
            "-e", "-f", "-S", "none", "-A=",
            "-B", &win.to_string(),
            "-W", &win.to_string(),
            "-s",
        ])
        .arg(source)
        .arg(target)
        .arg(out.path())
        .status()
        .expect("run xdelta3");
    assert!(status.success(), "xdelta3 -e failed: {status}");
    std::fs::read(out.path()).expect("read regenerated delta")
}

fn bench_all(c: &mut Criterion) {
    let source = std::fs::read(case01::source()).expect("read source");
    let target = std::fs::read(case01::target()).expect("read target");
    let diff = regenerate_simple_delta(&case01::source(), &case01::target());

    eprintln!(
        "case01: source={}B target={}B diff={}B (regenerated single-window, no-secondary)",
        source.len(),
        target.len(),
        diff.len()
    );

    // Sanity: both decoders reproduce the target from the regenerated delta.
    let x = Xdelta3::decode(&diff, &source).expect("xdelta3 decode");
    assert_eq!(x.len(), target.len(), "xdelta3 decode length mismatch");
    assert_eq!(x, target, "xdelta3 decode content mismatch");
    let y = Cdelta::decode(&diff, &source).expect("cdelta decode");
    assert_eq!(y.len(), target.len(), "cdelta decode length mismatch");
    assert_eq!(y, target, "cdelta decode content mismatch");

    bench_decode::<Xdelta3>(c, &source, &diff, &target);
    bench_decode::<Cdelta>(c, &source, &diff, &target);

    bench_encode::<Xdelta3>(c, &source, &target);
    bench_encode::<Cdelta>(c, &source, &target);
}

criterion_group!(benches, bench_all);
criterion_main!(benches);
