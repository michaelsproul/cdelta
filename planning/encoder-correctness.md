# Encoder Correctness and C Roundtrip Plan

## 2026-06-14 architecture update

The active direction has changed. The C encoder should refine a
non-degenerate pure encoder spec, and all roundtrip properties should be proved
at the spec layer. See `planning/encoder-refinement-strategy.md` for the
current plan.

The detailed direct proof work below is still useful as a record of helper
lemmas and generated AutoCorres structure. It is no longer the top-level plan:
we should not keep pushing `section_decodes` and final-target correctness
through low-level C helpers such as `flush_pending'`.

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
- The first pure-state refinement bridge is in place:
  `enc_sections_state_rel` relates emitted C section prefixes to an
  `enc_full_state`; ADD, RUN, COPY, zero-length final flush, and no-op
  ADD+COPY fusion wrappers now advance or preserve that relation.
- The reusable varint bridge
  `varint_size' v s = Some n ==> varint_bytes32 v n = varint_encode (unat v)`
  is proved, so large ADD/RUN pure-state wrappers no longer need an explicit
  byte-equality assumption.

## Encoder proof progress

- Writer helpers cover successful byte, byte-sequence, and varint writes while
  preserving the relevant emitted-section buffers, heap typing, and cache
  pointer fields needed by the emit proofs.
- ADD and RUN emitted-section and `enc_sections_inv` preservation are proved,
  including C-varint instruction-size forms.
- ADD and RUN also have `enc_sections_state_rel` preservation wrappers for
  the pure encoder state fields.  Large ADD and RUN derive their pure varint
  instruction bytes from `varint_size'`.
- COPY emitted-section preservation is proved for all four branches:
  small/large COPY size crossed with one-byte/varint address emission.
- COPY `enc_sections_inv` preservation is proved for all four branches.
  The one-byte address branches are unconditional with respect to wire bytes;
  the varint address and large-size branches currently take explicit
  `varint_bytes32 ... = varint_encode ...` assumptions, matching the existing
  serialization proof style.
- COPY also has `enc_sections_state_rel` preservation wrappers for all four
  size/address branches. These wrappers target `emit_copy_spec` and leave the
  exact C `best_mode'` to pure `encode_address` equality as an explicit
  address-choice premise for the later cache-choice refinement.
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
- The zero-length `flush_pending'` path has no-op combined and pure-state
  wrappers:
  `flush_pending'_len_zero_enc_sections_cache_inv` and
  `flush_pending'_len_zero_enc_sections_state_rel`.
- `try_emit_add_copy'` has no-op pure-state wrappers for pending length zero,
  the early-exit guard, and the mode-greater-than-5/copy-not-4 guard, alongside
  the existing combined invariant wrappers.
- `VcdiffEnc_Window.thy` now has a strengthened checked loop invariant,
  `encode_window_c_loop_cache_inv`, which extends the existing window invariant
  with `enc_cache_abs` and `enc_cache_wf`.  Its entry lemma is proved modulo the
  cache facts established by `cache_reset`.
- `CdeltaEncoderCorrectness` is temporarily in `quick_and_dirty` mode so the
  decomposition can install `sorry` lemmas and check how they compose.
- The obsolete direct-composition theory `VcdiffEnc_Correct.thy` has been
  removed from the session.  The replacement top-level target is byte-level
  refinement against the pure encoder state and `encode_spec`, not a direct
  `section_decodes` theorem.
- The first window `sorry` has been split.  Cache reset and loop-invariant
  entry are now proved by
  `cache_reset'_encode_window_c_loop_cache_inv_entry`, and
  `encode_window'_success_enc_sections_cache_inv` is proved from that entry
  plus an explicit matcher-totality slot.  The after-reset lemma consumes
  `cache_reset'` through `runs_to_vcg`.
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
- The matcher proof has base cases for windows that do not need the index:
  `find_best_match'_early_zero`/`find_best_match'_early_zero_valid` cover the
  generated early return, and `encode_window_match_ok_src_len_lt4` plus
  `encode_window_match_ok_tgt_len_lt4` lift those cases to the loop-level
  matcher predicate.
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
  `encode_window_c_loop_final_flush_run_inv_generated`.  Its proof is complete
  relative to the explicit `match_ok_entry` premise; the outer serialized
  scaffold now owns the `match_ok_after_reset` hole that should be discharged
  from `build_index'`.
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

Remaining encoder-refinement proof debt:

- Prove nonzero `flush_pending` and fused ADD+COPY preservation over the pure
  encoder-state relation shape.
- Prove `encode_window_match_ok` from `build_index` plus source/target heap
  facts, or thread it from the build-index stage into the window proof.  This
  is the real totality/match-validity precondition for the generated
  `gets_the (find_best_match' ...)`.
- Prove `encode_window_c_loop_body_run_inv`'s auxiliary preservation slot:
  successful body steps must preserve `encode_window_buffers_ok` and
  `encode_window_match_ok`.  The pending branch should follow from heap-update
  frame facts; COPY/fusion will follow from the emit helper heap-typing/frame
  postconditions.
- Prove the top-level `vcdiff_encode'` theorem by composing window refinement
  to pure sections with `serialize'_writes_serialize`.
- Once the remaining window `sorry` lemmas are discharged, turn
  `CdeltaEncoderCorrectness` back to `quick_and_dirty = false`.

## Active proof shape

The pure encoder spec should be upgraded so that byte-level refinement from the
C encoder is true. The roundtrip theorem then belongs entirely in the spec
layer:

```isabelle
encode_spec src tgt = Inl patch
  ==> decode_spec patch src = Inl tgt
```

The C encoder theorem should state that, under buffer validity, disjointness,
capacity, and size preconditions, a successful `vcdiff_encode'` call writes the
same bytes as `encode_spec src tgt`:

```isabelle
vcdiff_encode' ... returns length patch
  ==> heap_bytes out (length patch) = patch
```

Then compose this with the existing decoder refinement theorem
`vcdiff_decode'_spec_inl`. The C encoder proof should carry a simulation
relation to pure encoder state, not a direct `section_decodes` invariant.

## Implementation steps

1. Refactor `spec/pure/Encoder_Spec.thy` into a non-degenerate deterministic
   encoder spec that models source indexing, greedy matching, RUN detection,
   pending flushes, COPY emission, address-cache mode choice, opcode fusion,
   window section construction, and serialization.

2. Prove the non-degenerate spec roundtrip theorem in
   `proof/roundtrip/Spec_Roundtrip.thy`. The target-prefix, COPY-validity,
   RUN-validity, and cache synchronization arguments should live here.

3. Retarget existing writer and emitter C lemmas so they prove refinement to
   pure section-builder functions. They should still preserve buffer, cursor,
   and cache facts, but they should not be responsible for global decode
   correctness.

4. Prove `flush_pending'` refines `flush_pending_spec`. This replaces the
   old nonzero final-flush `section_decodes` target with a local simulation
   theorem.

5. Prove `build_index'`, `find_best_match'`, and the main `encode_window'`
   loop refine their pure spec counterparts.

6. Prove `serialize'` writes the bytes produced by pure serialization, then
   prove `vcdiff_encode'` writes `encode_spec src tgt` on success.

7. Compose encoder refinement, decoder refinement, and the spec roundtrip
   theorem into the C roundtrip theorem.

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
