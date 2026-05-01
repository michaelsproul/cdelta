# Step 1: Matcher-Parametric Spec Refactor — Progress

## Status: ~70% complete, needs build verification

## Goal
Refactor `spec/` so `Spec_Roundtrip.thy` exposes a `roundtrip_generic` theorem
quantified over any instruction list satisfying a well-formedness predicate,
with `spec_roundtrip` derived as a corollary.

## What was accomplished this session

### Definitions (committed, builds clean)
- `wf_insts_aux` / `wf_insts` / `valid_insts` in Instructions.thy
- `serialize_from_insts` in Encoder_Spec.thy
- `encode_one_prefix` / `encode_window_loop_prefix` in Encoder_Spec.thy
- `encode_spec` redefined as `serialize_from_insts` on `generate_instructions`
- `bounded_insts` predicate in Spec_Roundtrip.thy

### Structural lemmas (committed)
- `decode_loop_fuel_empty`, `decode_loop_mono`, `decode_loop_append`

### Per-instruction roundtrip lemmas (committed)
- `decode_one_add_small_suffix`, `decode_one_add_general_suffix`, `decode_one_add_suffix`
- `decode_one_run_suffix`
- `decode_one_copy_small_suffix`, `decode_one_copy_varint_suffix`, `decode_one_copy_suffix`
- `encode_one_decode_one_add`, `encode_one_decode_one_run`, `encode_one_decode_one_copy`

### Inductive roundtrip (committed, has sorry in Cons case)
- `encode_window_loop_decode_loop`: full structure, case splits on ADD/RUN/COPY
- Uses `encode_window_loop_prefix` for section decomposition
- Uses per-instruction lemmas for `decode_one` step
- Uses `decode_loop_mono` for fuel adjustment

### Top-level (committed, has sorry)
- `roundtrip_generic` theorem statement
- `spec_roundtrip'` corollary derived from `roundtrip_generic`
- `serialize_parse_roundtrip` helper lemma (sorry)

## What remains

### Fix sorry's
1. **`encode_window_loop_decode_loop` Cons case**: The proof structure is
   complete but needs Isabelle verification. The `encode_one_decode_one_*`
   lemmas use a `let` binding pattern that may need adjustment.

2. **`serialize_parse_roundtrip`**: Need dlen bound proof and
   parse_header/parse_window assembly. Can reuse existing
   `parse_window_no_source_head` and `parse_window_with_source_head`.

3. **`roundtrip_generic`**: Combines `serialize_parse_roundtrip` with
   `encode_window_loop_decode_loop` via `apply_window`.

### Build verification
Isabelle builds were repeatedly blocked by SQLite DB corruption from
concurrent build processes that couldn't be killed. A clean session
should allow verification. The initial definitions+existing proofs
were verified before the DB corruption started.

## Key design decisions

1. **`tgt_len = length (exec_inst_list ...)`** in `encode_window_loop_decode_loop`:
   Using equality rather than `>=` simplifies the inductive proof but means
   `roundtrip_generic` needs to reconcile this with the actual `pw_tgt_len`
   from the parsed window.

2. **No combined encode_one_decode_one lemma**: Separate lemmas for ADD/RUN/COPY
   because each has different preconditions. The Cons case of the induction
   case-splits on instruction type.

3. **`combined_bd: length src + tgt_len < 2^32`**: Added as an assumption to
   ensure COPY address encoding/decoding works (the "here" value must fit
   in a varint).

4. **`bounded_insts`**: Separates the varint-encodability requirement from
   the well-formedness predicate, keeping `wf_insts_aux` clean.

## Estimated remaining effort
- Fill sorry's: 1-2 hours of careful Isabelle engineering
- Build verification: 15-30 minutes once DB corruption is resolved
- Total: ~half a day
