# Step 1: Matcher-Parametric Spec Refactor — Progress

## Goal
Refactor `spec/` so `Spec_Roundtrip.thy` exposes a `roundtrip_generic` theorem
quantified over any instruction list satisfying a well-formedness predicate,
with `spec_roundtrip` derived as a corollary.

## Substeps

### 1. Definitions (Instructions.thy, Encoder_Spec.thy)
- [x] `wf_insts_aux` / `wf_insts` in Instructions.thy
- [ ] `serialize_from_insts` in Encoder_Spec.thy
- [ ] Accumulator-prefix lemma for `encode_window_loop`
- [ ] `encode_spec` = `serialize_from_insts` on degenerate matcher

### 2. decode_loop monotonicity (Spec_Roundtrip.thy)
- [ ] `decode_loop_mono`: if decode_loop n succeeds, decode_loop m (m >= n) also succeeds

### 3. Per-instruction encode/decode roundtrip (Spec_Roundtrip.thy)
- [ ] `encode_one_decode_one_add` (unified, with suffix pattern)
- [ ] `encode_one_decode_one_run`
- [ ] `encode_one_decode_one_copy`

### 4. Inductive roundtrip (Spec_Roundtrip.thy)
- [ ] `encode_window_loop_decode_loop`: induction over instruction list

### 5. Top-level assembly (Spec_Roundtrip.thy)
- [ ] `roundtrip_generic` theorem
- [ ] Derive `spec_roundtrip` as corollary

### 6. Build and verify sorry-free

## Key proof structure

The inductive roundtrip uses:
- Accumulator-prefix lemma to split encode_window_loop output
- Per-instruction roundtrip for the first instruction (with suffix pattern)
- decode_loop monotonicity to handle excess fuel
- IH for remaining instructions

The per-instruction lemma uses the "with suffix" pattern for data/inst/addr
sections. The inst section has NO suffix in the outer inductive lemma (because
decode_loop checks for empty inst_rem at the end).
