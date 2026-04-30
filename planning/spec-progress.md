# Pure-spec layer: Phase A progress notes

## Status (end of initial overnight pass)

| Theory | Sorries | Status |
|--------|---------|--------|
| Bytes.thy | 0 | done |
| Varint.thy | 0 | done |
| AddressCache.thy | 0 | done |
| CodeTable.thy | 0 | done |
| Instructions.thy | 0 | done |
| Encoder_Spec.thy | 0 | done |
| Decoder_Spec.thy | 0 | done |
| Spec_Roundtrip.thy | 2 | **partial** |

Bottom 7 theories: sorry-free. Spec_Roundtrip has `spec_roundtrip_small`
and `spec_roundtrip` as the only remaining sorries.

Intermediate lemmas proved in Spec_Roundtrip:
- `parse_header_of_magic` — parse_header (magic ++ [0x00, rest]) = Inl rest
- `encode_one_add_small` — encoder output shape for ADD of size 1..17
- `decode_one_add_small` — decoder consumes one small-ADD opcode and appends
  data to the target
- `encode_window_small_empty_src` — encode_window [RAdd tgt] 0 = (tgt, [op], [], cache)

What's missing to close `spec_roundtrip_small`:
- A `parse_window_of_encode_window_output` lemma that plays back the
  serializer's output through `parse_window`. The serialize format is
  `magic ++ [0x00, win_ind] ++ src_desc ++ varint(dlen) ++ varint(tgt_len)
  ++ [0x00] ++ varint(data_len) ++ varint(inst_len) ++ varint(addr_len)
  ++ data ++ inst ++ addr`.
  The proof is many sequential varint_decode_encode applications + one
  list-split for the three sections at the end. It is shape-wise
  mechanical; the trickiness is:
  * parse_window's threading uses deeply nested `case` expressions,
    not monadic Inl/Inr composition, so each step of the decoder
    pattern-match needs explicit unfolding.
  * The `data_len + inst_len + addr_len > length bs9` branch needs
    bookkeeping that the serialized sections are exactly `data ++
    inst ++ addr` of the expected sizes.

What's missing to close the *general* `spec_roundtrip`:
- `decode_loop_of_encode_window_loop` — the big induction showing that
  running `decode_loop` on the encoder's concatenated instruction
  section recovers `exec_inst_list` of the original instruction list.
  This is the Isabelle analogue of Lean's
  `encodeInstList_decodeLoop_roundtrip` (see
  `lean-bdiff/LeanBdiff/Vcdiff/Proofs/WindowRoundtrip.lean`, ~4700 LoC).
  Expect a similar scale of proof effort once started — mostly
  case-by-case on RAdd/RRun/RCopy + cache threading.

## Design notes to carry forward

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

### `quick_and_dirty` in ROOT

Keep `quick_and_dirty = true` while any file has a sorry — the build
fails otherwise and makes iteration slower. Flip to `false` to audit at
the end.
