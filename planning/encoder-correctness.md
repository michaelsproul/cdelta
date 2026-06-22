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
  `spec_roundtrip` for the public, total `encode_spec`.
- `CdeltaRefine` builds, including with `-o quick_and_dirty=false`.
- `proof/decoder-refine/VcdiffDec_Refine.thy` has the success-path decoder
  refinement theorem `vcdiff_decode'_spec_inl`:
  if `decode_spec patch src = Inl tgt`, the lifted C decoder returns `0`,
  writes `length tgt` to `out_len`, and writes `tgt` to `out`.
- `CdeltaEncoderCorrectness` now builds with `quick_and_dirty = false`.
  The obsolete direct window-loop scaffold has been removed from the active
  session; the active frontier is pure-state refinement of the C helpers in
  `proof/encoder-correctness/VcdiffEnc_Emit.thy` plus future C-shaped window
  refinement against the pure encoder spec.
- The first pure-state refinement bridge is in place:
  `enc_sections_state_rel` relates emitted C section prefixes to an
  `enc_full_state`; ADD, RUN, COPY, zero-length final flush, short pending
  flushes, replicated-run flushes, and ADD+COPY fusion wrappers now advance or
  preserve that relation in the cases currently proved.
- Shared proof-infrastructure helpers are in place:
  `section_byte_step_ok`, `section_varint_step_ok`, `section_copy_step_ok`,
  `enc_sections_state_rel_after`, and named theorem sets `enc_vcg`,
  `enc_emit_simps`, `enc_flush_simps`, and `enc_fused_simps`.
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
- `flush_pending'` also has pure-state wrappers for pending lengths 1, 2, 3,
  all length-4 branches, and replicated RUN buffers of arbitrary length.  The
  remaining flush gap is the mixed arbitrary-length case with interleaved ADD
  chunks and RUN chunks.
- `try_emit_add_copy'` has no-op pure-state wrappers for pending length zero,
  the early-exit guard, and the mode-greater-than-5/copy-not-4 guard, alongside
  the existing combined invariant wrappers.
- Pure fused ADD+COPY success shape is now characterized for both opcode
  families:
  `try_emit_add_copy_spec_mode_le5_success` and
  `try_emit_add_copy_spec_mode_gt5_success`.
- The fused success proof has the needed reusable byte-sequence writer frame:
  `write_bytes'_success_heap_bytes_append_wordpos_preserves2_near_ptr`.
- `try_emit_add_copy'` now has pure-state success wrappers for both fused
  opcode families:
  `try_emit_add_copy'_mode_le5_success_enc_sections_state_rel` and
  `try_emit_add_copy'_mode_gt5_success_enc_sections_state_rel`.
- General `flush_pending'` pure-state refinement is now proved via the
  C-shaped intermediate loop spec.  The main entry points are
  `flush_pending'_enc_sections_state_rel_loop_spec_topdown`, which targets
  `flush_pending_loop_spec`, and
  `flush_pending'_enc_sections_state_rel_topdown`, which bridges to
  `flush_pending_spec`.
- Matcher/index proof scaffolding has started in
  `proof/encoder-correctness/VcdiffEnc_Match.thy`: pure bucket facts for
  `build_index_spec`, the abstract `source_index_arrays_rel`, the heap wrapper
  `source_index_heap_rel`, and chain/take/candidate-soundness lemmas for the
  `find_best_match'` `MAX_CHAIN` loop are checked in.
- The obsolete `VcdiffEnc_Window.thy` scaffold has been deleted.  Its
  `section_decodes` loop invariant and final-flush theorem chain belonged to
  the abandoned direct proof strategy and was not needed by serialization or
  the current helper-refinement work.  It can be recovered from git history if
  any local buffer facts are worth mining later.

Remaining encoder-refinement proof debt:

- Package a caller-friendly `flush_pending'` wrapper that derives the current
  `flush_pending_outer_emit_pre` premise from the window-loop buffer,
  capacity, cursor, and relation invariants.  The general loop theorem itself
  is in place.
- Prove `build_index'` and `find_best_match'` refinement against the pure
  matcher/index spec, using `source_index_heap_rel` as the bridge between
  `head`/`next_arr` heap arrays and `build_index_spec`.
- Rebuild the window-loop theorem as a simulation against the pure
  `enc_full_state`/`encode_window_spec` shape, rather than reviving the removed
  `section_decodes` loop invariant.
- Prove the top-level `vcdiff_encode'` theorem by composing window refinement
  to pure sections with `serialize'_writes_serialize`.

## Active proof shape

The pure encoder spec is now a total byte-list function. The roundtrip theorem
belongs entirely in the spec layer:

```isabelle
spec_roundtrip:
  length src < 2 ^ 32 ==>
  length tgt < 2 ^ 32 - 32 ==>
  length src + length tgt < 2 ^ 32 ==>
  decode_spec (encode_spec src tgt) src = Inl tgt
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

1. Done: `spec/pure/Encoder_Spec.thy` now contains a non-degenerate
   deterministic encoder spec that models source indexing, greedy matching,
   RUN detection, pending flushes, COPY emission, address-cache mode choice,
   opcode fusion, window section construction, and serialization.

2. Done: `proof/roundtrip/Spec_Roundtrip.thy` proves `spec_roundtrip` for the
   public `encode_spec`. The target-prefix, COPY-validity, RUN-validity, and
   cache synchronization arguments live in the pure layer.

3. Retarget existing writer and emitter C lemmas so they prove refinement to
   pure section-builder functions. They should still preserve buffer, cursor,
   and cache facts, but they should not be responsible for global decode
   correctness.

4. Done: `flush_pending'` refines `flush_pending_spec` via the intermediate
   `flush_pending_loop_spec` described in
   `planning/flush-pending-loop-spec.md`.  The remaining work here is a
   caller-facing wrapper that discharges the theorem's `emit_pre` premise from
   the eventual window-loop invariant.

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
isabelle build -d . CdeltaEncoderCorrectness
isabelle build -o quick_and_dirty=false -d . CdeltaRefine
rg -n "^\s*(sorry|oops)\b" proof spec
```

## Assumptions

- Scope is success only: `decode_spec (encode_spec src tgt) src = Inl tgt`
  and the C encoder writes those bytes on success.
- Error-path `Inr` refinement is deliberately out of scope.
- Keep current C encoder behavior, including COPY, RUN, and ADD+COPY fusion.
- Use conservative capacity, disjointness, and 32-bit no-overflow premises
  first; tighten them only after the proof exposes unnecessary slack.
