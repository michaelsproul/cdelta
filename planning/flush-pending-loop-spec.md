# Flush Pending Refinement Plan

## Motivation

`flush_pending'` has been expensive because the current target jumps directly
from a pointer/cursor C loop to the nicer pure `flush_pending_spec`. The
behavioral correspondence is clear, but the proof correspondence is not local
enough:

- C tracks `add_start`, `i`, and an inner scan cursor `j`.
- The pure spec currently describes the final grouped instruction list.
- Each emitted chunk mutates two output sections and threads `sections_t_C.err`.
- Every write generates heap-frame, disjointness, cursor, and no-overflow
  obligations.

The next attempt should insert a C-shaped pure intermediate spec. The C proof
then refines that loop-shaped spec, and a separate pure lemma connects the
loop-shaped spec to `flush_pending_spec`.

## Intermediate Spec Shape

Add pure definitions near the existing flush machinery in
`proof/encoder-correctness/VcdiffEnc_Emit.thy` first. Move them to
`spec/pure/Encoder_Spec.thy` only if they become useful outside the refinement
proof.

Suggested definitions:

```isabelle
definition pending_slice :: "byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> byte list" where
  "pending_slice pending a b = take (b - a) (drop a pending)"

definition pending_run_end :: "byte list \<Rightarrow> nat \<Rightarrow> nat" where
  "pending_run_end pending i =
     (let b = pending ! i in
      i + length (takeWhile ((=) b) (drop i pending)))"

definition flush_pending_emit_add_spec ::
  "nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   enc_full_state \<Rightarrow> enc_full_state" where
  "flush_pending_emit_add_spec src_len pending add_start i st =
     (if add_start < i
      then emit_inst_spec src_len (RAdd (pending_slice pending add_start i)) st
      else st)"

definition flush_pending_emit_run_spec ::
  "nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   enc_full_state \<Rightarrow> enc_full_state" where
  "flush_pending_emit_run_spec src_len pending i j st =
     emit_inst_spec src_len (RRun (pending ! i) (j - i)) st"
```

Then define a recursive or fuelled loop spec that mirrors the C outer loop:

```isabelle
flush_pending_loop_spec src_len pending add_start i st
```

Expected behavior:

- If `i >= length pending`, emit the final ADD slice `pending[add_start..<len]`
  if nonempty and clear `enc_pending`.
- Otherwise compute `j = pending_run_end pending i`.
- If `min_run <= j - i`, emit any pending ADD slice
  `pending[add_start..<i]`, emit `RUN (pending ! i) (j - i)`, and recurse
  with `add_start = j`, `i = j`.
- If `j - i < min_run`, recurse with `add_start` unchanged and `i = j`.

The recursive measure should be `length pending - i`; prove `i < j` in the
loop body from `i < length pending`.

## Main Lemmas

Prove these pure lemmas before touching the AutoCorres proof:

```isabelle
lemma flush_pending_loop_spec_eq_groups:
  assumes "add_start \<le> i" "i \<le> length pending"
  shows "flush_pending_loop_spec src_len pending add_start i st =
         (emit_insts_spec src_len
           (flush_pending_groups (pending_slice pending add_start i)
             (drop i pending)) st)\<lparr>enc_pending := []\<rparr>"

lemma flush_pending_loop_spec_eq_flush_pending_spec:
  assumes "enc_pending st = pending"
  shows "flush_pending_loop_spec src_len pending 0 0 st =
         flush_pending_spec src_len st"
```

The first lemma is the bridge to the existing `flush_pending_groups` work. The
second lemma is the public refinement target conversion.

## C Refinement Invariant

For the outer C loop, use the intermediate spec directly:

```isabelle
flush_pending_loop_rel s data inst addr sec pending len add_start i spec_st
```

Required invariant facts:

- `enc_pending spec_st = heap_bytes_word s pending 0 len`
- `unat add_start <= unat i` and `unat i <= unat len`
- emitted C sections equal the pure sections produced by the already-processed
  prefix:
  `flush_pending_loop_spec src_len pending_bytes 0 0 initial_st` up to
  cursor `i`, with `pending[add_start..<i]` deliberately unflushed
- C heap slices for `pending`, `data`, `inst`, and `addr` needed by future
  reads/writes are preserved
- section cursors match the emitted pure section lengths
- `sections_t_C.err_C sec = ENC_OK` on the success path

Do not put `decode_spec`, `section_decodes`, or target-prefix semantics in this
invariant.

For the inner C scan, keep the invariant narrow:

- `j` stays between `i + 1` and `len`
- all bytes in `pending[i..<j]` equal `pending[i]`
- either `j = len` or the next byte differs
- the heap is unchanged

The existing `flush_pending_scan_inner_inv` lemmas should be reused or adapted
rather than reproved.

## Execution Order

1. Add the pure intermediate definitions and prove `pending_run_end` bounds.
2. Prove `flush_pending_loop_spec_eq_groups`.
3. Prove `flush_pending_loop_spec_eq_flush_pending_spec`.
4. State the C outer-loop theorem against `flush_pending_loop_spec`, not
   `flush_pending_spec`.
5. Prove the run branch by composing existing `emit_add'` and `emit_run'`
   state-rel wrappers.
6. Prove the short-run branch as a no-emission state update on `i`.
7. Prove the final tail ADD after the loop.
8. Convert the result to `flush_pending_spec` using
   `flush_pending_loop_spec_eq_flush_pending_spec`.

## 2026-06-18 Implementation Note

The first proof-layer slice is now in `proof/encoder-correctness/VcdiffEnc_Emit.thy`:

- `pending_slice`, `pending_run_end`, `flush_pending_emit_add_spec`,
  `flush_pending_emit_run_spec`, and recursive `flush_pending_loop_spec` are
  defined.
- `pending_run_end_gt`, `pending_run_end_le`, and helper facts connecting
  `pending_run_end` to `takeWhile`/`dropWhile` are proved.
- Branch facts are proved for rewriting `flush_pending_groups` from a
  `pending_run_end` split:
  `flush_pending_groups_run_from_pending_run_end` and
  `flush_pending_groups_short_from_pending_run_end`.
- `flush_pending_loop_spec.simps` is deliberately removed from the global simp
  set; unfold it with `subst` at the specific loop head.

The bridge lemmas are now proved:

- `flush_pending_loop_insts_eq_groups`
- `flush_pending_loop_spec_eq_insts`
- `flush_pending_loop_spec_eq_groups`
- `flush_pending_loop_spec_eq_flush_pending_spec`

The successful structure factors the proof through `flush_pending_loop_insts`,
an instruction-list loop that mirrors `add_start`, `i`, and `j`. This keeps the
semantic grouping proof separate from the state-threading proof and avoids a
large nested Isar script.

The C-proof-prep facts now available are:

- `pending_run_end_eq_maximal`
- `pending_run_end_eq_heap_scan`
- `flush_pending_loop_spec_run_step`
- `flush_pending_loop_spec_short_step`
- `flush_pending_loop_spec_exit`
- `flush_pending_loop_spec_run_step_word`
- `flush_pending_loop_spec_short_step_word`
- `flush_pending_loop_spec_exit_word`
- `pending_slice_heap_bytes_word`
- `flush_pending_emit_add_spec_heap_word`
- `flush_pending_emit_run_spec_heap_word`
- `flush_pending_loop_spec_run_step_heap_emit_word`
- `flush_pending_loop_spec_short_step_heap_word`
- `flush_pending_loop_spec_exit_heap_emit_word`
- `emit_pending_add_chunk_preserves_heap_bytes_word`
- `emit_pending_run_chunk_preserves_heap_bytes_word`
- `emit_pending_run_chunk_enc_sections_state_rel_preserves_heap_bytes_word`
- `flush_pending'_len_zero_enc_sections_state_rel_loop_spec`
- `flush_pending'_scan_from_Res_int_pending_run_end`

These facts are intended to let the AutoCorres proof rewrite one outer-loop
iteration from the concrete `j` scan result to the corresponding
`flush_pending_loop_spec` branch.

The word-indexed variants are the preferred entry points for the C proof: they
hide the recurring `unat`, `word_le_nat_alt`, and heap-buffer length
conversions. The scan wrapper should be used immediately after the inner scan
loop, so the outer proof receives both the concrete `j` and the pure
`pending_run_end` equality.

The heap-word emit helpers are the preferred bridge when composing
`emit_add'`/`emit_run'`: they rewrite the loop-shaped pure state update to the
exact heap slice or byte used by the C emitter call.

The branch-level heap emit lemmas combine the scan result, branch condition,
and emit-shape rewrites. The outer-loop proof should use those directly after
the C branch has established `j`, rather than unfolding
`flush_pending_loop_spec`.

The ADD preservation helper hides the small/large ADD split when the outer
invariant only needs to know that the pending input frame is unchanged.

## Guardrails

- Stop adding one-off length special cases unless they are used to debug the
  general loop invariant.
- Keep the intermediate spec total and success-path focused; overflow behavior
  can remain discharged by capacity preconditions.
- Prefer proving pure bridge lemmas first. If a C subgoal needs a semantic fact
  about grouping, it probably belongs in the intermediate-spec bridge, not in
  the AutoCorres script.
