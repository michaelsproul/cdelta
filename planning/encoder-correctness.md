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
- `CdeltaEncoderCorrectness` is temporarily in `quick_and_dirty` mode so the
  decomposition can install `sorry` lemmas and check how they compose.
- `VcdiffEnc_Correct.thy` has two installed `sorry` C-glue lemmas:
  `encode_window'_success_enc_sections_cache_inv` and
  `vcdiff_encode'_success_serialized_sections`.  The public
  `vcdiff_encode'_success_decode_spec` theorem is no longer a stub: it is
  proved from the serialized-sections glue lemma and the pure
  `section_decodes_serialize_decode` bridge.
- The `vcdiff_encode'_success_serialized_sections` scaffold explicitly invokes
  `encode_window'_success_enc_sections_cache_inv`, so the proposed window
  postcondition is checked at the C top-level boundary.  The remaining `sorry`
  there is the build-index/serialize glue, including the large
  `serialize'_writes_serialize` premise package.
- The first window `sorry` has been split.  Cache reset and loop-invariant
  entry are now proved by
  `cache_reset'_encode_window_c_loop_cache_inv_entry`, and
  `encode_window'_success_enc_sections_cache_inv` is proved from that entry.
  `encode_window'_after_cache_reset_success_enc_sections_cache_inv` now also
  consumes `cache_reset'` through `runs_to_vcg`; its remaining `sorry` is the
  generated while-loop/final-flush body.
- The pending-byte branch now has a concrete invariant step:
  `encode_window_c_loop_cache_inv_pending_byte_step`.  It advances `tp` and
  `pend_len`, appends the target byte to the pending bytes, and preserves the
  section/cache invariant under explicit buffer-disjointness premises.
- The C-shaped pending-byte heap update is also covered by
  `encode_window_c_loop_cache_inv_pending_byte_step_c_update`, which bridges
  the generated `uint` pointer arithmetic and source-target heap read back to
  the normalized invariant step.
- The pending-byte branch is now proved at the generated monad level by
  `encode_window_pending_byte_branch_result_inv`.  This establishes the
  `liftE { guard; guard; heap update; return }` branch against the loop-result
  invariant that the real `whileLoop` will use.
- The generated small-match branch wrapper
  `encode_window_pending_match_branch_result_inv` is also proved: the
  pending-full path throws a non-OK section, and the non-full path calls the
  pending-byte branch lemma.
- The small-match branch now has a loop-step-strengthened wrapper:
  `encode_window_pending_match_branch_loop_step`.  It proves the same
  result invariant plus the `tp` measure decrease required by
  `runs_to_whileLoop_exn'`.
- The generated loop body has been named as `encode_window_c_loop_body`, and
  `encode_window_c_loop_body_result_inv` checks the decomposition against that
  exact body.  Its `gets_the find_best_match'` witness is supplied through the
  new `encode_window_match_ok` predicate; the `len < 4` branch is proved, while
  the COPY/fusion side is the remaining local body `sorry`.
- The generated `whileLoop` now has a standalone skeleton,
  `encode_window_c_loop_while_run_inv`, over `encode_window_c_loop_run_inv`.
  This plugs the body lemma into `runs_to_whileLoop_exn'` with the real `tp`
  measure and proves the loop rule obligations.  Its postcondition also exposes
  the generated loop exit fact `tp < tgt_len` is false for successful loop
  results.  The run invariant deliberately carries result correctness,
  byte-buffer validity, and matcher totality so the remaining preservation gaps
  are explicit.
- `encode_window'_after_cache_reset_success_enc_sections_cache_inv` now folds
  the generated loop body to `encode_window_c_loop_body` and invokes
  `encode_window_c_loop_while_run_inv` after `cache_reset'`.  It also routes
  the generated final-flush continuation through
  `encode_window_c_loop_final_flush_run_inv_generated`, so the top-level
  `sorry` at this point is now the matcher-totality obligation after
  `cache_reset'` rather than the final continuation.
- The window proof now carries an explicit `encode_window_buffers_ok`
  precondition.  This is needed for target/pending pointer validity and for the
  non-aliasing facts required to preserve the source, target, pending, and
  emitted-section heap slices.
- The zero-pending loop exit is bridged by
  `encode_window_c_loop_result_inv_doneD`: if the generated `whileLoop` exits
  with `(0, sec, tp)` and `tp < tgt_len` is false, the result invariant yields
  the final `enc_sections_inv` plus cache facts directly.
- The generated final-flush continuation has a named split:
  `encode_window_c_loop_final_flush_zero` proves the `pend_len = 0` exit path,
  `encode_window_c_loop_final_flush_result` centralizes the remaining nonzero
  `flush_pending'` preservation hole, and
  `encode_window_c_loop_final_flush_run_inv_generated` adapts this to the
  postcondition shape emitted by the top-level VCG.
- The completed-loop extraction is captured by
  `encode_window_c_loop_cache_inv_doneD`: at `tp = tgt_len` and `pend_len = 0`,
  the strengthened loop invariant yields the exact `enc_sections_inv` and cache
  facts needed by the `encode_window'` success target.

Remaining proof debt before `try_emit_add_copy`/window integration:

- Discharge or centralize the C-varint byte-equality assumptions.
- Prove nonzero `flush_pending` and fused ADD+COPY preservation over the same
  section/cache invariant shape.
- Prove `encode_window_match_ok` from `build_index` plus source/target heap
  facts, or thread it from the build-index stage into the window proof.  This
  is the real totality/match-validity precondition for the generated
  `gets_the (find_best_match' ...)`.
- Prove `encode_window_c_loop_body_run_inv`'s auxiliary preservation slot:
  successful body steps must preserve `encode_window_buffers_ok` and
  `encode_window_match_ok`.  The pending branch should follow from heap-update
  frame facts; COPY/fusion will follow from the emit helper heap-typing/frame
  postconditions.
- Prove the matcher-totality slot in
  `encode_window'_after_cache_reset_success_enc_sections_cache_inv`; reset,
  loop-rule integration, the generated pending-byte/small-match branch, and the
  zero-pending final exit are no longer part of that top-level hole.
- Refine `vcdiff_encode'_success_serialized_sections` so it is proved by
  composing `encode_window'_success_enc_sections_cache_inv` with
  `serialize'_writes_serialize`.
- Once the two installed `sorry` lemmas are discharged, turn
  `CdeltaEncoderCorrectness` back to `quick_and_dirty = false`.

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
     pending-byte branch uses
     `encode_window_pending_byte_branch_result_inv`.
     no-fusion branch uses non-empty `flush_pending'` preservation, then the
     appropriate `emit_copy'` section/cache wrapper.
     fused branch uses fused `try_emit_add_copy'` preservation, then an
     optional remainder `emit_copy'` wrapper.
     final flush uses non-empty `flush_pending'` preservation and
     `encoder_loop_inv_doneD`.
   - On success, `encode_window_c_loop_cache_inv_doneD` extracts the full-target
     section/cache postcondition.

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
