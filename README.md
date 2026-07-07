# cdelta

A simplified [VCDIFF (RFC 3284)](https://www.rfc-editor.org/rfc/rfc3284) delta
encoder and decoder written in C, formally verified in
[Isabelle/HOL](https://isabelle.in.tum.de/) using
[AutoCorres2](https://www.isa-afp.org/entries/AutoCorres2.html).

The headline result: **the C encoder either rejects its input or produces a
patch that the C decoder provably decompresses back to the original target
bytes** — proved end-to-end, from the C sources, with no `sorry`s.

## The codec

Both sides implement a single-window subset of VCDIFF compatible with xdelta3:

- Default code table (RFC 3284 §5.4) with opcode fusion for ADD+COPY pairs
- Default address cache (4 NEAR slots, 3×256 SAME buckets) with
  SELF/HERE/NEAR/SAME address modes
- RUN instruction detection, 4-byte rolling-hash match finder with chained
  buckets over the source
- No secondary compression, adler32 checksums, or application headers

The C code (`spec/cenc/vcdiff_enc.c`, `spec/cdec/vcdiff_dec.c`) is written in
the AutoCorres-liftable C subset: no function pointers or variadics, helpers
communicate via struct returns, and tables/caches are file-scope arrays.
Despite the constraints it is real, performant code: the decoder runs at
~1 GiB/s, within a few percent of xdelta3, and encoder output is ~1.3× the
size of `xdelta3 -S none` on the bundled test case.

## Key results

All theories build without `sorry`. The proof stack has two layers: a pure
HOL specification of the codec, and AutoCorres refinement proofs connecting
the C programs to that specification.

### 1. Pure-spec roundtrip — `Spec_Roundtrip.thy`

The functional encoder and decoder specs invert each other for essentially
all input sizes:

```isabelle
theorem spec_roundtrip:
  assumes "length src < 2 ^ 32"
      and "length tgt < 2 ^ 32 - 32"
      and "length src + length tgt < 2 ^ 32"
  shows "decode_spec (encode_spec src tgt) src = Inl tgt"
```

### 2. Tight encoder output bounds — `Encoder_Bounds.thy`

The encoded patch can never blow up: its length is linear in the target with
a small constant, and each internal section obeys a provable budget
(notably `4 * |addr| ≤ 5 * |tgt| + …`, the invariant behind the address
section's capacity check):

```isabelle
theorem encode_spec_length_le:
  assumes "length src < 2 ^ 32" and "length tgt < 2 ^ 31 - 32"
  shows "length (encode_spec src tgt) ≤ 2 * length tgt + 38"
```

`encoder_bounds_ok` packages these bounds as a caller-checkable capacity
envelope, mirrored exactly by an upfront runtime guard in `vcdiff_enc.c` —
so a caller that sizes its buffers to the envelope is guaranteed a
successful encode.

### 3. C decoder refines the spec — `VcdiffDec_Refine.thy`

Whenever the pure spec accepts a patch, the C decoder (lifted by AutoCorres)
returns `VCD_OK` and writes exactly the spec's output bytes:

```isabelle
lemma vcdiff_decode'_spec_inl:
  assumes ⟨buffer validity, disjointness, capacity⟩
      and "decode_spec patch_bytes src_bytes = Inl tgt"
  shows "vcdiff_decode' … ∙ s
           ⦃ λr t. r = Result 0 ∧
                   unat (heap_w32 t out_len) = length tgt ∧
                   heap_bytes t out (length tgt) = tgt ⦄"
```

This is the largest proof in the project (~57 k lines), covering the code
table construction loops, header/window parsing, and the copy/add/run
instruction interpreter.

### 4. C encoder writes the spec's bytes — `proof/encoder-correctness/`

The C encoder, on success, writes precisely `encode_spec src tgt` to its
output buffer (`vcdiff_encode'_checked` in `VcdiffEnc_Checked.thy`). The
runtime capacity guards make this **unconditional on arithmetic**: the
theorem needs only structural hypotheses (valid, disjoint buffers), because
an encode that would violate the bounds provably returns the rejection code
instead.

### 5. End-to-end C roundtrip — `VcdiffC_Roundtrip.thy`

Composing all of the above:

```isabelle
theorem vcdiff_encode'_then_decode_roundtrip_checked:
  assumes ⟨structural hypotheses only: valid, disjoint, sized buffers⟩
  shows "vcdiff_encode' … ∙ enc_s
           ⦃ λr enc_t. ∃enc_n. r = Result enc_n ∧
                (enc_n = 0 ∨   -- encoder rejected the input, or:
                 decoder_roundtrip_runs … tgt_bytes) ⦄"
```

where `decoder_roundtrip_runs` states that running the C decoder on the
encoder's output buffer terminates with `VCD_OK` and reproduces
`tgt_bytes` exactly.

## Project structure

```
ROOT                       Isabelle session declarations (l4v-style single ROOT)
spec/
  pure/                    Pure HOL codec spec: Bytes, Varint, AddressCache,
                           CodeTable, Instructions, Encoder_Spec, Decoder_Spec
  cenc/                    vcdiff_enc.c + AutoCorres lifting (VcdiffEnc.thy)
  cdec/                    vcdiff_dec.c + AutoCorres lifting (VcdiffDec.thy)
proof/
  roundtrip/               Spec_Roundtrip.thy — pure-spec decode∘encode = id
  encoder-bounds/          Encoder_Bounds.thy — output-length budget tower
  encoder-correctness/     C encoder refines encode_spec (writers → wire →
                           cache/opcode → match → emit → serialize → checked)
  decoder-refine/          VcdiffDec_Refine.thy — C decoder refines decode_spec
  c-roundtrip/             VcdiffC_Roundtrip.thy — top-level C-to-C roundtrip
  test-add/                Minimal AutoCorres bring-up example
harness/                   Rust crate: compiles the C via cc, roundtrip tests
                           and criterion benches against xdelta3 as oracle
test-data/case01/          ~15 MB source/target/diff sample
planning/                  Working notes and proof-strategy documents
```

Session dependency graph (as declared in `ROOT`):

```
HOL-Library ── CdeltaSpecBase ── CdeltaSpecRoundtrip ── CdeltaEncoderBounds
                                        │                        │
AutoCorres2 ─┬─ CdeltaDecoder ── CdeltaRefineBase ── CdeltaRefine │
             │                                            │      │
             └─ CdeltaEncoder ── CdeltaEncoderCorrectness ┴──────┴─ CdeltaCRoundtrip
```

## Building the proofs

Requires Isabelle2025-2 with the AFP registered (for `AutoCorres2` and
`Word_Lib`). From the repository root:

```sh
isabelle build -d . CdeltaCRoundtrip
```

This checks the whole stack; individual sessions can be built by name
(e.g. `isabelle build -d . CdeltaSpecRoundtrip`). The decoder refinement
session is the long pole and benefits from a prebuilt `AutoCorres2` heap
(`isabelle build -b AutoCorres2`).

## Running the code

The `harness/` crate compiles both C files and exercises them against
[xdelta3](https://github.com/jmacd/xdelta) as a correctness oracle:

```sh
cd harness
cargo test              # roundtrip + cross-decoding tests
cargo bench             # criterion benchmarks on test-data/case01
```

## Caveats

- The verified subset is single-window VCDIFF with the default code table;
  interoperability holds for patches within that subset.
- The C-level theorems are about the AutoCorres-lifted semantics of the C
  sources under the usual assumptions of that toolchain (C parser semantics,
  compiler correctness are trusted).
- Termination/totality: the theorems are stated as total-correctness
  (`runs_to`) results — the lifted programs terminate on the covered inputs.
