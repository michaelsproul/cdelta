# Pure-spec layer: non-degenerate encoder roundtrip complete

## Status

All eight current theories in `spec/` build sorry-free under
`quick_and_dirty = false`. The public encoder spec is now the C-shaped
non-degenerate spec, not the old single-ADD baseline.

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
          "length src + length tgt < 2 ^ 32"
  shows   "decode_spec (encode_spec src tgt) src = Inl tgt"
```

The `-32` slack on the target bound accounts for varint-size overhead
in the `dlen` (length of the delta encoding) field: a bound of
`2^32 - 32` leaves room for up to 5 five-byte varints plus single-byte
constants, all well within 32-bit arithmetic.

## Encoder shape

`encode_spec` is total and delegates to `encode_spec_full`, which uses
`encode_window_full_spec` when the generated sections fit in the 32-bit wire
format and falls back to the older RUN-aware baseline otherwise.

```isabelle
definition encode_spec :: "byte list \<Rightarrow> byte list \<Rightarrow> byte list" where
  "encode_spec src tgt = encode_spec_full src tgt"
```

The old single-ADD path remains under `encode_spec_degenerate`, and the
RUN-aware baseline remains under `encode_spec_run`. They are now regression
or fallback facts, not the public C-refinement target.

## Next: C encoder refinement

Use `encode_spec` as the byte-level refinement target:

```isabelle
patch = encode_spec src_bytes tgt_bytes
```

The next proof layer should show that a successful `vcdiff_encode'` call writes
exactly `patch`, then compose that with `spec_roundtrip` and the existing
decoder refinement theorem.

## Size (spec/)

- Varint.thy: 461 lines (Phase A.1)
- AddressCache.thy: 577 lines (Phase A.2)
- CodeTable.thy: 237 lines (Phase A.3)
- Instructions.thy: 123 lines (Phase A.4)
- Encoder_Spec.thy: 579 lines (Phase A.7)
- Decoder_Spec.thy: 246 lines (Phase A.5)
- Spec_Roundtrip.thy: 5636 lines (Phase A.8)
- Total: ~8900 lines of pure/spec roundtrip Isabelle

Compare to Lean-bdiff (`~/Programming/lean-bdiff`):
- Pure proofs: ~10000 lines of Lean.
- Ratio: now roughly comparable; most of the remaining project size is in
  AutoCorres refinement rather than pure semantic roundtrip.

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
