# Refinement Layer Progress

## Status (2026-05-10) — rescue branch

The previous approach on `refine/close-loop-sorry` has been abandoned.
Audit found three problems with it that made further investment unsafe:

1. **Build is broken.** Last CdeltaRefine build
   (`cdelta-refine-build.log`, 2026-05-09) hung for ~5 minutes on
   `runs_to_vcg` around line 6453 of `VcdiffDec_Refine.thy` and was
   terminated. No incremental elaboration is possible on the current
   top-level proof.
2. **Postcondition is too weak to reuse.** `vcdiff_decode'_prefix_correct`
   proves only `∃ret. r = Result ret` (no Failure). The target theorem
   needs `heap_bytes t out (length tgt) = tgt ∧ heap_w32 t out_len = …`.
   The current proof cannot be composed into `vcdiff_decode'_spec` —
   it is a parallel track, not a stepping stone.
3. **Main loop invariant is disconnected.** The outer
   `runs_to_whileLoop_exn` invariant (line 6468) tracks only
   `buf_valid` + cursor bounds + `heap_typing`. It has no connection
   to `dec_state`, `ds_tgt`, or `decode_spec`, so the sorry-free
   `decode_loop_inv_after_add/run/copy` lemmas cannot be applied inside
   the loop body. ~2000 lines of infrastructure is currently unreachable
   from the top-level goal.

Additionally, the top-level proof is a ~500-line apply-script chain of
copy-pasted `apply (all \<open>… read_varint'_spec … ; fail)?\<close>`
peel steps. Each peel inflates terms the higher-order unifier must
traverse; this is the direct cause of the VCG hang.

## What to keep from the old branch

All of these are sorry-free, heavily reused, and unrelated to the
broken glue code:

* `read_byte'_spec`, `read_byte'_list_spec`
* `read_varint'_spec`, `read_varint'_chain`, `read_varint'_chain_transfer`,
  `varint_decode_value_bound`
* `decode_address'_spec` (all four address modes)
* `build_code_table'_spec` (3 sorrys, but contained and independent)
* `add_loop_correct`, `run_loop_correct`, `copy_loop_correct` (inner
  instruction loops)
* `decode_loop_inv`, `decode_loop_invD`, `decode_loop_inv_init`
* `decode_loop_inv_after_add/run/copy` (invariant preservation for each
  instruction type)
* `decode_loop_inv_advance_inst`, `decode_loop_inv_advance_inst_n`
* `near_init_preserves_patch_heap`, `same_init_preserves_patch_heap`
* Heap/buffer infra (`bufs_disjoint`, `heap_bytes_*`, `buf_valid_*`,
  `ptr_add_inject`, `heap_w32_heap_w8_update`, …)
* Bridge/support lemmas (`code_tbl_matches_{first,second}_half`,
  `byte_to_hi_tag_{ity,isz}`, `exec_half_*_conditions`, `inv_*`,
  `resolve_size_*`)

## What to discard

* `vcdiff_decode'_prefix_correct` (the 1000-line apply-script glue)
* `inst_end_le_patch_len`, `inst_end_le_patch_len2/3`, `inst_end_le_word`,
  `word_le_of_unat_le`, `pos_chain_le`, `runs_to_whileLoop_bind_drop6th`,
  `runs_to_whileLoop_bind_drop6th'`, `summand_le_from_sub_eq`,
  `inst_end_from_sizes`, `inst_end_from_sizes'` — all propped up the
  broken proof, likely not needed by the new decomposition.
  **Decision rule:** leave them in place for now; delete only when a
  replacement lemma is proved and they are confirmed unused.

## New plan: structured decomposition

The previous plan in `proof-strategy.md` and in the old version of this
file is still essentially right; the failure was tactical, not strategic.
The key change is **disciplined modular composition via `runs_to_bind`
and structured Isar**, never `runs_to_vcg` across the whole body.

### Step 0 — unblock the build

1. Replace the broken `vcdiff_decode'_prefix_correct` proof body with
   `sorry` (accepting `quick_and_dirty = true` as we already have it)
   so the session elaborates. Keep the statement; we'll probably
   discard it later but for now we want the file to load so the
   supporting lemmas remain checkable.
2. Confirm `isabelle build -d . -o system_log=true -v CdeltaRefine`
   finishes. Baseline for further work.

### Step 1 — state the target theorem

Write `vcdiff_decode'_spec` with the *real* postcondition (roughly the
one in `refine-progress.md` Goal section) as a `lemma … sorry`.
This anchors what all sub-lemmas need to compose to, and stops us
from drifting into weaker intermediate statements that can't be
glued together.

### Step 2 — Phase 2: four small prefix lemmas

Each is a standalone lemma with an explicit postcondition that names
the parse result and the C state. Each is ~30-80 lines of structured
Isar (`obtain`/`note`/`have`/`show`), not apply-scripts.

| Lemma | C code section | Postcondition |
|-------|---------------|---------------|
| `header_magic_refine` | bytes 0..4 | `parse_header bs = Inl (hdr, rest)` ∧ `hdr` has no app data |
| `init_loops_refine` | near/same init | cache = cache_init, `heap_bytes` of patch/src unchanged, `buf_valid` preserved |
| `window_meta_refine` | byte 5 + 5 varints + di byte | `parse_window rest = Inl (win, tail)`, cursors positioned at `data_pos`/`inst_pos`/`addr_pos`, arithmetic bounds established |
| `section_cursors_refine` | arithmetic + sanity checks | `data_end`, `inst_end`, `addr_end` in `32 word`, all ≤ `patch_len`, `decode_loop_inv` holds at loop entry |

Compose with `runs_to_bind` / `runs_to_weaken`. Don't unfold
`vcdiff_decode'_def` inside these; work against already-lifted
sub-operations (`read_byte'`, `read_varint'`, init loops).

If any of these lemmas resist structured proof, **stop and revisit the
statement** rather than fall back to apply-script peeling. The peel
style is what killed the old approach.

### Step 3 — Phase 3: the main loop as a standalone lemma

```
lemma decode_window_loop_correct:
  assumes decode_loop_inv s0 … data_cursor inst_cursor addr_cursor 0 0 t
      and [code_tbl_matches, buf_valid, disjoint, bounds]
  shows "whileLoop C B (addr_cursor, data_cursor, inst_cursor, 0, 0) ∙ t
           ⦃ λr t'. case r of
               Result (…) ⇒ ∃st'.
                 decode_window (ds_state_from_inv …) = Inl st' ∧
                 decode_loop_inv … t' ∧
                 [final cursors = ends]
             | Exn _ ⇒ False ⦄"
```

Prove with `runs_to_whileLoop_exn` using **`decode_loop_inv`** (not a
bespoke subset of it) as the invariant. The body obligation decomposes
via `runs_to_bind` into:
* opcode read → `decode_loop_inv_advance_inst`
* first half dispatch → `decode_loop_inv_after_{add,run,copy}` or NOOP
* second half dispatch → ditto
* which < 2 inner loop: unroll to 2 sequential dispatches

Termination: measure `unat inst_end - unat inst_cursor`, decreases by
≥ 1 per iteration via the opcode read.

### Step 4 — Phase 4: composition

`vcdiff_decode'_spec` = chain of:

* `header_magic_refine` + `runs_to_bind`
* `init_loops_refine` + `runs_to_bind`
* `window_meta_refine` + `runs_to_bind`
* `section_cursors_refine` — establishes `decode_loop_inv`
* `decode_window_loop_correct` — invariant maintained, `ds_tgt` correct
* post-loop `unless` checks follow from final-state cursor bounds
* final `*out_len = tgt_pos` write + return

Unfold `decode_spec` once at the top level to show the post-condition
matches. Never unfold `vcdiff_decode'_def` except inside the four
prefix lemmas (each unfolds only the prefix it covers).

### Step 5 — cleanup

* Delete discarded helper lemmas once shown unused.
* Turn off `quick_and_dirty` in ROOT for `CdeltaRefine`.
* Full clean build, no sorry / no oops.

## Anti-patterns (do not repeat)

These are the things that caused the previous blowup. Stop and ask
if any of them start to appear again:

1. **`runs_to_vcg` on the full decoder body.** Always bind-decompose
   first, then VCG on bite-sized pieces.
2. **`apply (all \<open>… ; fail)?\<close>` chains longer than ~3 in a row.**
   If you need more, the goal has too much structure; extract a lemma.
3. **Intermediate postconditions of the form `∃ret. r = Result ret`.**
   Any reusable lemma needs a postcondition that names the semantic
   effect on the state.
4. **Bespoke loop invariants that duplicate a subset of `decode_loop_inv`.**
   Use `decode_loop_inv` directly; it's why we defined it.
5. **`unfolding vcdiff_decode'_def` at the top-level theorem.** Only
   unfold inside the smallest lemma that mentions that prefix.

## Build workflow

```
isabelle build -d . -o system_log=true -v CdeltaRefine > .build-tmp/build.log 2>&1
```

Keep foreground. `system_log=true -v` is how we detect stuckness
(timing lines indicate a stuck command).
