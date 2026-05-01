# Step 1: Matcher-Parametric Spec Refactor — Progress

## Goal
Refactor `spec/` so `Spec_Roundtrip.thy` exposes a `roundtrip_generic` theorem
quantified over any instruction list satisfying a well-formedness predicate,
with `spec_roundtrip` derived as a corollary.

## Substeps

### 1. Definitions (Instructions.thy, Encoder_Spec.thy)
- [x] `wf_insts_aux` / `wf_insts` / `valid_insts` in Instructions.thy
- [x] `serialize_from_insts` in Encoder_Spec.thy
- [x] Accumulator-prefix lemma: `encode_one_prefix`, `encode_window_loop_prefix`
- [x] `encode_spec` = `serialize_from_insts` on `generate_instructions`

### 2. decode_loop structural lemmas (Spec_Roundtrip.thy)
- [x] `decode_loop_fuel_empty`
- [x] `decode_loop_mono`
- [x] `decode_loop_append`

### 3. Per-instruction encode/decode roundtrip (Spec_Roundtrip.thy)
- [x] `decode_one_add_small_suffix` / `decode_one_add_general_suffix`
- [x] `decode_one_add_suffix` (unified)
- [x] `decode_one_run_suffix`
- [x] `decode_one_copy_small_suffix` / `decode_one_copy_varint_suffix`
- [x] `decode_one_copy_suffix` (unified)
- [x] `encode_one_decode_one_add` (using let-binding pattern)
- [x] `encode_one_decode_one_run`
- [x] `encode_one_decode_one_copy`

### 4. Inductive roundtrip (Spec_Roundtrip.thy)
- [x] `encode_window_loop_decode_loop` — structure complete
  - Nil case: trivial
  - Cons case: section decomposition via `encode_window_loop_prefix`,
    per-instruction `decode_one` step, IH via `decode_loop_mono`
  - **No sorry's remain in the theorem statement itself**
  - Build verification pending

### 5. Top-level assembly (Spec_Roundtrip.thy)
- [ ] `roundtrip_generic` theorem
- [ ] Derive `spec_roundtrip` as corollary

### 6. Build and verify sorry-free
- Build attempts have been plagued by SQLite DB corruption from concurrent
  Isabelle builds. Needs single clean build to verify.

## Key assumptions added
- `bounded_insts`: varint-encodable sizes for all instructions (< 2^32)
- `combined_bd`: src_seg_len + tgt_len < 2^32 (combined window fits in 32 bits)
- `wf_insts_aux`: per-instruction well-formedness threading partial target

## Architecture decisions
- Per-instruction roundtrip lemmas use "with suffix" pattern: data/inst/addr
  sections have trailing bytes from subsequent instructions
- `encode_one_decode_one_*` lemmas use `let` binding on `encode_one` output
  to avoid explicit destructuring in the caller
- The inductive lemma sets `tgt_len = length (exec_inst_list ...)` exactly,
  rather than just `>=`, to simplify the proof
