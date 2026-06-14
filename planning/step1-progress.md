# Step 1: Matcher-Parametric Spec Refactor — Historical Progress

## 2026-06-14 status

This was progress on the previous matcher-parametric plan. The active plan has
changed: build a non-degenerate deterministic encoder spec, prove its
roundtrip theorem at the pure spec layer, and then prove the C encoder refines
that spec. See `planning/encoder-refinement-strategy.md`.

The lemmas listed here may still be useful as support for the pure roundtrip
proof, but `roundtrip_generic` and `valid_insts` are no longer the main path to
C encoder correctness.

## Status: Structure complete, needs build verification + sorry discharge

**9 commits, +1193 lines across 4 files this session.**

## Completed work

### Definitions (Instructions.thy, Encoder_Spec.thy)
- `wf_insts_aux` / `wf_insts` / `valid_insts` — well-formedness predicate
- `serialize_from_insts` — factored out from `encode_spec`
- `encode_one_prefix` / `encode_window_loop_prefix` — accumulator append lemmas
- `bounded_insts` — varint-encodable size bounds

### Structural lemmas (Spec_Roundtrip.thy)
- `decode_loop_fuel_empty`, `decode_loop_mono`, `decode_loop_append`

### Per-instruction roundtrip lemmas (Spec_Roundtrip.thy, 12 lemmas)
- `decode_one_{add,run,copy}_{small,general,varint}_suffix` — with suffix pattern
- `decode_one_{add,run,copy}_suffix` — unified wrappers
- `encode_one_decode_one_{add,run,copy}` — relating encoder output to decoder

### Inductive roundtrip (Spec_Roundtrip.thy)
- `encode_window_loop_decode_loop` — full proof structure with Cons case
  handling ADD/RUN/COPY instruction dispatch

### Top-level assembly (Spec_Roundtrip.thy)
- `serialize_parse_roundtrip` — generic serialize/parse_header/parse_window lemma
- `roundtrip_generic` — the target theorem (sorry)
- `spec_roundtrip'` — derives existing spec_roundtrip as corollary

## Remaining sorry's (4 total)
1. `dlen_bd` in `serialize_parse_roundtrip` — varint size arithmetic
2. `serialize_parse_roundtrip` show — compose parse_header + parse_window
3. `roundtrip_generic` body — compose serialize_parse with decode_loop
4. `encode_window_loop_decode_loop` Cons case — the final `show ?case`
   (proof structure is complete, needs simp to close)

## Known issue: build timeout
The Isabelle build consistently times out at 300s CPU (30 min wall).
No syntax or type errors — the issue is simplifier performance.

**Root cause**: The `decode_one_*_suffix` proofs use `simp` with
`decode_one_def` unfolded. Even with explicit intermediate states,
the simplifier must process record update equations on abstract
records (`st ⟨field := ...⟩`), which creates large terms.

**Suggested fix**: The final `by (simp add: s1 ... s8)` step in each
suffix lemma should be replaced with a manual chain:
```isabelle
  have "decode_one ... ?in_st = ..."
    apply (simp only: decode_one_def)
    apply (simp only: s1)
    apply (simp only: Let_def)
    apply (simp only: entry)
    ...
```
This forces the simplifier to do one rewrite at a time rather than
exploring the whole term. An alternative is to use `subst` or
`unfold` for each step.

## File structure
```
spec/Instructions.thy     — +47 lines (wf_insts_aux, valid_insts)
spec/Encoder_Spec.thy     — +72 lines (prefix lemmas, serialize_from_insts)
spec/Spec_Roundtrip.thy   — +999 lines (Part 2: matcher-parametric)
planning/step1-progress.md — this file
```
