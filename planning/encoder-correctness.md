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
- Cache abstraction preservation is now proved for successful byte writes,
  byte-sequence writes, varint writes, and both byte-form and varint-form
  `emit_address'`.
- ADD and RUN now have combined
  `enc_sections_inv` + `enc_cache_abs` + `enc_cache_wf` success wrappers:
  `emit_add'_small_success_enc_sections_cache_inv`,
  `emit_add'_large_success_enc_sections_cache_inv`, and
  `emit_run'_success_enc_sections_cache_inv`.
- COPY now has combined
  `enc_sections_inv` + `enc_cache_abs` + `enc_cache_wf` success wrappers for
  all four size/address branches.  Their near-pointer bounds are derived from
  `enc_cache_abs`.
- The zero-length `flush_pending'` path has a no-op combined wrapper:
  `flush_pending'_len_zero_enc_sections_cache_inv`.
- The `try_emit_add_copy'` pending-length-zero path has a no-op combined
  invariant wrapper:
  `try_emit_add_copy'_pend_len_zero_enc_sections_cache_inv`.
- `VcdiffEnc_Window.thy` now has a strengthened checked loop invariant,
  `encode_window_c_loop_cache_inv`, which extends the existing window invariant
  with `enc_cache_abs` and `enc_cache_wf`.  Its entry lemma is proved modulo the
  cache facts established by `cache_reset`.
- `VcdiffEnc_Correct.thy` now proves the pure top-level composition path:
  `section_decodes_apply_window`, `enc_sections_inv_apply_window`, and
  `encoder_sections_serialize_decode`.  Thus a proved window postcondition of
  `enc_sections_inv ... tgt ...` plus the existing serialize bridge is enough
  to conclude `decode_spec (serialize src tgt data inst addr) src = Inl tgt`.
- `VcdiffEnc_Correct.thy` also contains two checked `oops` targets, because the
  normal session rejects `sorry`: `encode_window'_success_enc_sections_cache_inv`
  and `vcdiff_encode'_success_decode_spec`.  These typecheck the proposed C
  decomposition without installing fake theorems.

Remaining proof debt before `try_emit_add_copy`/window integration:

- Discharge or centralize the C-varint byte-equality assumptions.
- Prove `flush_pending` and fused ADD+COPY preservation over the same
  section/cache invariant shape.
- Prove the `encode_window'_success_enc_sections_cache_inv` target using
  `encode_window_c_loop_cache_inv`.
- Compose `encode_window'_success_enc_sections_cache_inv`,
  `serialize'_writes_serialize`, and `encoder_sections_serialize_decode` into
  the public `vcdiff_encode'_success_decode_spec` target.

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
   - Small ADD and small COPY / one-byte-address branches now track the C
     address cache against the pure cache used by `decode_address`; extend this
     to branches that write varints after adding a cheap varint-write cache
     frame.
   - Account for fused ADD+COPY by proving the corresponding default-code-table
     opcode decodes as the two intended half-instructions.

4. Prove `encode_window` success correctness.
   - Invariant: `encode_window_c_loop_cache_inv`.
   - It bundles the old heap/capacity/prefix facts, `enc_sections_inv` for the
     flushed prefix, and the cache abstraction/well-formedness facts needed by
     COPY emission.
   - Branch slots:
     pending-byte branch uses `encoder_loop_inv_pending_step_word` plus a
     pending-buffer write frame; no section/cache change.
     no-fusion branch uses non-empty `flush_pending'` preservation, then the
     appropriate `emit_copy'` section/cache wrapper.
     fused branch uses fused `try_emit_add_copy'` preservation, then an
     optional remainder `emit_copy'` wrapper.
     final flush uses non-empty `flush_pending'` preservation and
     `encoder_loop_inv_doneD`.
   - On success, emitted sections decode to the full target.

5. Prove top-level encoder success theorem.
   - `serialize'` writes bytes equal to pure `serialize src tgt data inst addr`.
   - `encoder_sections_serialize_decode` turns the window postcondition into
     pure `decode_spec` success.
   - `vcdiff_encode'` returning nonzero implies the produced patch bytes
     satisfy `decode_spec patch src = Inl tgt`.

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
