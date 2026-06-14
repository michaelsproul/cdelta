# Pure-spec layer: Phase A baseline complete

## Status

All eight current theories in `spec/` build sorry-free under
`quick_and_dirty = false`. This is the baseline pure-spec milestone, not the
final encoder spec needed for C encoder refinement.

| Theory | Status |
|--------|--------|
| Bytes.thy | done |
| Varint.thy | done |
| AddressCache.thy | done |
| CodeTable.thy | done |
| Instructions.thy | done |
| Encoder_Spec.thy | done |
| Decoder_Spec.thy | done |
| Spec_Roundtrip.thy | **done** |

Top-level theorem (`Spec_Roundtrip.thy`):

```isabelle
theorem spec_roundtrip:
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32 - 32"
  shows   "decode_spec (encode_spec src tgt) src = Inl tgt"
```

The `-32` slack on the target bound accounts for varint-size overhead
in the `dlen` (length of the delta encoding) field: a bound of
`2^32 - 32` leaves room for up to 5 five-byte varints plus single-byte
constants, all well within 32-bit arithmetic.

## Important caveat: degenerate matcher

The encoder's instruction generator is deliberately degenerate:

```isabelle
definition generate_instructions :: "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list" where
  "generate_instructions src tgt = [RAdd tgt]"
```

i.e. it always emits a single ADD covering the whole target. This is
enough to prove the roundtrip theorem but produces patches that are the
same size as the target — no actual delta compression. A realistic
matcher would emit COPY/RUN instructions against the source and within
the target.

**Why this was OK for the baseline:** The theorem validates the
wire-format, parser, instruction-dispatch, and serialization plumbing. It is a
useful executable sanity check and should be kept as a small corollary.

**Why it is not enough now:** The C encoder should refine the encoder spec in
the same sense that the C decoder refines the decoder spec. A single-ADD
encoder cannot be that target, because the C encoder emits RUN, COPY,
ADD+COPY-fused opcodes, and cache-selected address modes. The next pure-spec
phase is therefore to replace the main encoder spec with a non-degenerate,
deterministic model of the C encoder.

## Next: Phase A.7 non-degenerate encoder spec

Add a realistic pure encoder spec before resuming the C encoder proof:

1. Define pure counterparts for source indexing, match search, RUN detection,
   pending ADD buffering, `flush_pending`, COPY emission, address-cache mode
   selection, opcode fusion, window section construction, and serialization.
2. Make `encode_spec` call that non-degenerate encoder. Keep the current
   single-ADD encoder under a separate name such as `encode_spec_degenerate`.
3. Prove the non-degenerate spec roundtrip theorem:

   ```isabelle
   encode_spec src tgt = Inl patch
     ==> decode_spec patch src = Inl tgt
   ```

4. Prove any target-prefix, COPY-validity, RUN-validity, and cache
   synchronization lemmas entirely in the spec layer.
5. Use the resulting `encode_spec` as the C encoder refinement target.

## Size (spec/)

- Varint.thy: 461 lines (Phase A.1)
- AddressCache.thy: 577 lines (Phase A.2)
- CodeTable.thy: 237 lines (Phase A.3)
- Instructions.thy: 123 lines (Phase A.4)
- Encoder_Spec.thy: 155 lines (Phase A.5)
- Decoder_Spec.thy: 246 lines (Phase A.5)
- Spec_Roundtrip.thy: 800 lines (Phase A.6)
- Total: ~2600 lines of Isabelle

Compare to Lean-bdiff (`~/Programming/lean-bdiff`):
- Pure proofs: ~10000 lines of Lean.
- Ratio: ~0.25× Isabelle-to-Lean. Mostly because our Isabelle spec uses
  the degenerate matcher; Lean proved the full realistic matcher's
  roundtrip. When we do the same in Isabelle, expect ~2-4× growth.

## Design notes

### Varint normalisation

`word_of_nat (1 + sz)` vs `(1 + word_of_nat sz :: byte)`: simp normalises
the first to the second, but downstream unat lemmas are phrased on the
first form. Work-around: prove both forms of any `unat` fact, or
explicitly use `subst unat_of_nat_eq`. Either way, always double-check
the normalised form before piping through simp.

### Code table proof style

The `default_entry_*` exhaustion lemmas work best if you:
1. Establish the numeric bounds (`?op \<le> some_numeral`) early.
2. Use `linarith` for bound subtractions like `mode - 6 \<le> 2` — `simp`
   can't handle assumption conjunctions around Nat subtraction.
3. Unfold `default_entry_def` and `Let_def` only at the final step; keep
   the let-bindings wrapped up until then so simp doesn't duplicate them.

### Address-cache chain invariants

Three invariants thread through `try_near_modes` / `try_same_modes`:
1. Mode < num_modes (= 9)
2. Mode = 0 ⟹ bytes = varint_encode addr
3. Mode ≠ 0 ⟹ `wf_encoding c addr here mode bs`

Each has its own `_preserves_` lemma with a clean inductive form.
`le_refl` gives `s_near \<le> s_near` / `s_same \<le> s_same` for the
top-level instantiation.

### parse_window proof pattern

`parse_window` has deeply nested `case` expressions. To prove it
inverts a serialized input, the pattern that works is:
1. State the lemma with section lengths as `length data`, not free
   `data_len` — simp unifies better that way.
2. Pre-compute each `varint_decode (varint_encode n @ rest) = Some
   (n, rest)` as a local `have` for every n.
3. Prove the win_ind bit tests (`AND 0x02 = 0`, etc.) as numeric facts.
4. Single `unfolding parse_window_def pop_byte_def Let_def`
   + `by (simp add: <all local varint lemmas + bit-tests>)`.

### ROOT quick_and_dirty

Keep `quick_and_dirty = true` while any file has a sorry — the build
fails otherwise and makes iteration slower. Flip to `false` to audit
at the end.
