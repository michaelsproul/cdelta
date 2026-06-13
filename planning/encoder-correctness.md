# Encoder Correctness and C Roundtrip Plan

## Current status

- `CdeltaSpecRoundtrip` builds and contains the pure success theorem
  `spec_roundtrip` plus matcher-parametric infrastructure.
- `CdeltaRefine` builds, including with `-o quick_and_dirty=false`.
- `proof/decoder-refine/VcdiffDec_Refine.thy` has the success-path decoder
  refinement theorem `vcdiff_decode'_spec_inl`:
  if `decode_spec patch src = Inl tgt`, the lifted C decoder returns `0`,
  writes `length tgt` to `out_len`, and writes `tgt` to `out`.
- `CdeltaEncoderCorrectness` now contains the encoder proof split and builds
  cleanly.  The active frontier is `proof/encoder-correctness/VcdiffEnc_Emit.thy`
  plus the window-loop integration.

## Encoder proof progress

- Writer helpers cover successful byte, byte-sequence, and varint writes while
  preserving the relevant emitted-section buffers, heap typing, and cache
  pointer fields needed by the emit proofs.
- ADD and RUN emitted-section and `enc_sections_inv` preservation are proved,
  including C-varint instruction-size forms.
- COPY emitted-section preservation is proved for all four branches:
  small/large COPY size crossed with one-byte/varint address emission.
- COPY `enc_sections_inv` preservation is proved for all four branches.
  The one-byte address branches are unconditional with respect to wire bytes;
  the varint address and large-size branches currently take explicit
  `varint_bytes32 ... = varint_encode ...` assumptions, matching the existing
  serialization proof style.
- `best_mode'_encode_address_correct` connects the C address cache choice to
  the pure decoder cache predicate used by `section_decodes_append_copy`.

Remaining proof debt before `try_emit_add_copy`/window integration:

- Discharge or centralize the C-varint byte-equality assumptions.
- Carry `enc_cache_abs` and `enc_cache_wf` through COPY emission alongside
  `enc_sections_inv`, so later COPYs can reuse the updated pure cache.
- Prove `flush_pending` and fused ADD+COPY preservation over the same
  section/cache invariant shape.
- Lift these helper facts into the `encode_window` loop invariant.

## Main proof shape

The C encoder should not initially be proved byte-identical to
`encode_spec`.  The current C encoder emits RUNs, COPYs, and fused ADD+COPY
opcodes, while the pure `encode_window` in `Encoder_Spec.thy` emits only
standalone opcodes.  The lower-friction target is therefore:

```isabelle
vcdiff_encode' returns patch_len > 0
  ==> decode_spec emitted_patch source = Inl target
```

Then compose that fact with `vcdiff_decode'_spec_inl`.

## Implementation steps

1. Add a pure bridge theorem in `proof/roundtrip/Spec_Roundtrip.thy`.
   - Reuse `serialize_parse_roundtrip`.
   - State that if the serialized sections' parsed window succeeds via
     `apply_window`, then `decode_spec (serialize src tgt data inst addr) src
     = Inl tgt`.
   - This avoids re-proving header and window parsing in the encoder proof.

2. Add encoder refinement scaffolding.
   - Create a new proof theory/session for encoder correctness.
   - Define encoder-side `heap_bytes` and `buf_valid` helpers in the
     `vcdiff_enc_global_addresses` context.
   - Prove leaf helper specs for `write_byte'`, `write_varint'`, and
     `write_bytes'` against the pure byte-list operations.

3. Prove emitted-section correctness for encoder helpers.
   - `emit_add`, `emit_run`, and `emit_copy` now preserve the invariant that
     emitted sections decode to the target prefix already covered.
   - Next, track the C address cache against the pure cache used by
     `decode_address` through COPY-emitting helpers.
   - Account for fused ADD+COPY by proving the corresponding default-code-table
     opcode decodes as the two intended half-instructions.

4. Prove `encode_window` success correctness.
   - Invariant: `tp` and `pend_len` partition the target prefix; emitted
     sections decode to the flushed prefix; pending bytes equal the unflushed
     suffix; every COPY match points to equal source bytes.
   - On success, emitted sections decode to the full target.

5. Prove top-level encoder success theorem.
   - `serialize'` writes bytes equal to pure `serialize src tgt data inst addr`.
   - `vcdiff_encode'` returning nonzero implies the produced patch satisfies
     `decode_spec patch src = Inl tgt`.

6. Compose C roundtrip.
   - First theorem should be relational over produced bytes, because encoder
     and decoder are AutoCorres-lifted from separate C files with separate
     `lifted_globals`.
   - If a same-state `do encode; decode` theorem is later required, introduce a
     combined C translation after resolving static-name conflicts.

## Build checks

Run these before considering the implementation closed:

```bash
isabelle build -d . CdeltaSpecRoundtrip
isabelle build -d . CdeltaEncoder
isabelle build -o quick_and_dirty=false -d . CdeltaRefine
rg -n "^\s*(sorry|oops)\b" proof spec
```

## Assumptions

- Scope is success only: `decode (encode ...) = Inl ...`.
- Error-path `Inr` refinement is deliberately out of scope.
- Keep current C encoder behavior, including COPY, RUN, and ADD+COPY fusion.
- Use conservative capacity, disjointness, and 32-bit no-overflow premises
  first; tighten them only after the proof exposes unnecessary slack.
