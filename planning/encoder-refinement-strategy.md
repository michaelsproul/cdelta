# Encoder Refinement Strategy

## 2026-06-18 status

The pure encoder spec is now non-degenerate and total:

```isabelle
encode_spec :: byte list \<Rightarrow> byte list \<Rightarrow> byte list
```

`proof/roundtrip/Spec_Roundtrip.thy` proves the public `spec_roundtrip`
theorem for this `encode_spec`. The active remaining work is C-to-pure encoder
refinement, not pure semantic roundtrip.

## 2026-06-14 decision

The active plan is to make the pure encoder spec non-degenerate, prove all
roundtrip properties at the spec layer, and then prove that the C encoder
refines that encoder spec. This mirrors the decoder architecture: pure HOL
specs state the semantic correctness theorem, and AutoCorres proofs connect C
code to those specs.

The previous strategy, where the C encoder was proved directly to emit some
valid instruction stream or directly to satisfy `decode_spec patch src = Inl
tgt`, is superseded. The proof work already done for emitted sections, cache
preservation, and buffer framing remains useful as local refinement machinery,
but it is no longer the top-level proof target.

## Why change direction

- The earlier pure encoder was degenerate:

  ```isabelle
  generate_instructions src tgt = [RAdd tgt]
  ```

  That was enough for a baseline roundtrip theorem, but it could not be the
  final C refinement target because the C encoder emits COPY, RUN, ADD+COPY
  fusion, and cache-selected address modes.

- The direct C proof path carries `section_decodes` and target-prefix facts
  through low-level routines such as `flush_pending'`. That makes local buffer
  proofs responsible for global semantic correctness, which is brittle.

- A non-degenerate pure spec gives each proof layer a cleaner job:
  the spec proves that the chosen instruction stream roundtrips, and the C
  proof proves that the implementation follows the same algorithm and writes
  the same bytes.

## Target architecture

```
Pure encoder spec
  build_index_spec
  find_best_match_spec
  best_mode_spec
  flush_pending_spec
  try_emit_add_copy_spec
  encode_window_spec
  serialize_spec
        |
        | roundtrip theorem, entirely in pure HOL
        v
  patch = encode_spec src tgt
  decode_spec patch src = Inl tgt

C encoder
        |
        | AutoCorres refinement
        v
  heap output bytes = encode_spec src tgt
```

The encoder spec should be deterministic and C-shaped enough that byte-level
refinement is true under explicit size, capacity, and disjointness
preconditions. It does not need to be pretty; it needs to be the stable
mathematical reference for the implementation.

## Main theorem shape

Spec-level theorem:

```isabelle
theorem encode_spec_roundtrip:
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32 - 32"
          "length src + length tgt < 2 ^ 32"
  shows   "decode_spec (encode_spec src tgt) src = Inl tgt"
```

C encoder refinement theorem, success form:

```isabelle
theorem vcdiff_encode'_refines_encode_spec:
  assumes "encoder_buffers_ok s src src_len tgt tgt_len out out_cap scratch"
          "heap_bytes s src src_len = src_bytes"
          "heap_bytes s tgt tgt_len = tgt_bytes"
          "sections_fit_32 src_bytes tgt_bytes
             (encode_window_full_spec src_bytes tgt_bytes)"
          "patch = encode_spec src_bytes tgt_bytes"
          "length patch <= unat out_cap"
  shows
    "vcdiff_encode' out out_cap src src_len tgt tgt_len scratch \<bullet> s
       \<lbrace>\<lambda>rv s'.
          rv = of_nat (length patch)
        \<and> heap_bytes s' out (length patch) = patch\<rbrace>"
```

An overflow/error theorem can be added later, but it should not be required for
the first roundtrip result. For the initial correctness theorem, assume enough
output capacity, valid scratch space, and inputs compatible with the C fast
path. In particular, the C theorem is for the full-window encoder path where
`sections_fit_32 src_bytes tgt_bytes (encode_window_full_spec src_bytes
tgt_bytes)` holds. The pure `encode_spec` remains total by falling back to
`encode_spec_run` when full-window sections do not fit, but that fallback is a
spec-layer totality device and is not part of the C encoder refinement target.

Composition theorem:

```isabelle
theorem c_encoder_then_decoder_roundtrip:
  assumes "patch = encode_spec src tgt"
          "vcdiff_encode' writes patch"
          "vcdiff_decode' refines decode_spec"
          "decode_spec patch src = Inl tgt"
  shows   "running the C encoder and then the C decoder writes tgt"
```

## Pure spec work

### 1. Replace the degenerate encoder with a realistic one

Done. `spec/pure/Encoder_Spec.thy` keeps the old degenerate encoder as a small
sanity theorem/fallback path, but the public `encode_spec` now uses a
deterministic C-shaped encoder that models:

- source index construction;
- greedy match search;
- RUN detection and splitting;
- pending ADD buffer;
- COPY emission with address-cache mode choice;
- ADD+COPY fusion where the default code table permits it;
- final pending flush;
- section serialization.

The pure spec exposes smaller functions that correspond to C helper
boundaries:

```isabelle
build_index_spec
find_best_match_spec
best_mode_spec
emit_add_spec
emit_run_spec
emit_copy_spec
flush_pending_spec
try_emit_add_copy_spec
encode_window_full_spec
encode_spec
```

The public spec is intentionally total. For C refinement, however, we assume
the input fits the C full-window path. Under `sections_fit_32 src tgt
(encode_window_full_spec src tgt)`, `encode_spec src tgt` reduces to
serialization of `encode_window_full_spec`; the `encode_spec_run` fallback is
kept for totality and roundtrip reasoning, not as behavior that
`vcdiff_encode'` must implement.

### 2. Decide the spec state representation

Done. The current state is `enc_full_state`:

```isabelle
record enc_full_state =
  enc_tp      :: nat
  enc_flushed :: nat
  enc_pending :: "byte list"
  enc_data    :: "byte list"
  enc_inst    :: "byte list"
  enc_addr    :: "byte list"
  enc_cache   :: cache
  enc_trace   :: "raw_inst list"
```

The state tracks the same observable pieces the C loop mutates. That
makes refinement invariants mostly field equality between heap slices and pure
state fields.

### 3. Prove roundtrip at the spec layer

Done for the public `encode_spec`. The semantic invariant belongs here, not in
the C proof:

- the instruction/section stream represented by `data_sec`, `inst_sec`, and
  `addr_sec` decodes to the target prefix already processed;
- pending bytes are exactly the unflushed target suffix since `add_start`;
- COPY ranges are valid in the combined source/target window at the point of
  emission;
- RUN segments are byte-replicates of the target segment;
- address-cache encode/decode stays synchronized.

The checked-in proof uses `enc_trace` plus section-byte decode invariants; the
section bytes are still used for final serialization.

### 4. Keep the degenerate proof as a baseline

The old single-ADD theorem remains valuable:

```isabelle
theorem encode_spec_degenerate_roundtrip:
  "decode_spec (encode_spec_degenerate src tgt) src = Inl tgt"
```

It should no longer be the theorem cited by the C encoder proof.

## C refinement work

### 1. Refine leaf writers to pure section builders

The existing writer and emit lemmas can be redirected toward equality with
pure builders:

- `write_byte'` appends one byte to the corresponding pure section;
- `write_bytes'` appends a byte list;
- `write_varint'` appends `varint_encode n`;
- `emit_add'`, `emit_run'`, and `emit_copy'` refine the matching pure emitters.

These lemmas should still preserve heap typing, disjointness, cursor bounds,
and cache facts, but their primary postcondition should be pure-state equality,
not `decode_spec` success.

### 2. Refine `flush_pending'` to `flush_pending_spec`

The old final-flush `section_decodes` target is obsolete. The local theorem
should say:

```isabelle
flush_pending' ... refines flush_pending_spec ...
```

Use the intermediate `flush_pending_loop_spec` approach documented in
`planning/flush-pending-loop-spec.md`.  The C proof should refine the
loop-shaped spec first, then a pure bridge lemma should rewrite that result to
`flush_pending_spec`.

Its invariant should track:

- C pending buffer equals the pure state's `pending`;
- C `data_sec`, `inst_sec`, and `addr_sec` prefixes equal pure sections;
- C cache arrays equal the pure cache;
- cursors equal pure section lengths;
- overflow exits return an error or are excluded by capacity assumptions.

No final target-roundtrip fact should be proved inside this lemma. That fact is
proved once for `flush_pending_spec` in the pure spec layer.

### 3. Refine the window loop to `encode_window_spec`

The C loop invariant should be a simulation relation between generated C state
and pure spec state after the same logical step:

- `tp` equals `enc_spec_state.tp`;
- `pending[0..pend_len)` equals `enc_spec_state.pending`;
- emitted C section prefixes equal `data_sec`, `inst_sec`, and `addr_sec`;
- C cache arrays equal `enc_spec_state.cache`;
- C source index arrays equal `enc_spec_state.index`;
- source and target input heap slices are unchanged;
- cursor and capacity bounds hold.

The loop proof should not carry `section_decodes` directly. When a C helper is
hard to prove, prove the corresponding pure helper first and make the C lemma a
small simulation proof.

### 4. Refine top-level serialization

After `encode_window'` refines `encode_window_spec`, prove that `serialize'`
writes the bytes produced by `serialize_spec`. The final C theorem then states
that success writes exactly `encode_spec src tgt`.

## Phased plan

| Phase | Goal | Result |
|-------|------|--------|
| A.7 | Add the non-degenerate pure encoder spec | Done: executable spec follows the C algorithm |
| A.8 | Prove non-degenerate spec roundtrip | Done: `decode_spec (encode_spec src tgt) src = Inl tgt` |
| B.3a | Retarget writer/emit proofs to pure builders | In progress: leaf emit helpers, fused wrappers, serialization, and general flush-pending refinement exist |
| B.3b | Prove `build_index'` and `find_best_match'` refinement | Started: pure bucket facts, `source_index_heap_rel`, and chain/candidate lemmas are in place |
| B.3c | Prove `flush_pending'` refinement | General loop theorem done; package caller-side preconditions for window use |
| B.4 | Prove `encode_window'` refinement | Window loop writes spec sections |
| B.5 | Prove `vcdiff_encode'` refinement | C encoder writes `encode_spec` bytes |
| C | Compose with decoder refinement | C encode followed by C decode recovers target |

## Reuse from current proof work

The committed encoder-correctness helpers should be mined rather than thrown
away:

- buffer validity and disjointness lemmas;
- writer framing lemmas;
- emitted-section cursor and capacity facts;
- cache abstraction and well-formedness lemmas;
- generated-body naming and loop-measure setup.

However, the semantic invariant should move out of the C loop and into the
pure spec proof.

## Open questions

1. Decision: keep the pure encoder spec total under explicit size bounds.  The
   C refinement theorem assumes `sections_fit_32` and proves only the
   full-window success path.  Do not change `encode_spec` to `Inl`/`Inr`
   unless error-path refinement becomes a concrete blocker.
2. Should the pure proof use a ghost instruction trace in addition to section
   bytes? Prefer yes if it substantially simplifies target-prefix proofs.
3. How exact should overflow behavior be? Initial theorem assumes enough
   capacity, scratch space, and section-size fit; later refinement can
   characterize overflow paths.
4. Should the spec model C's hash table layout exactly or expose an abstract
   index relation? Prefer exact enough for `find_best_match'` refinement, with
   abstraction lemmas for semantic match validity.  Current direction:
   `source_index_heap_rel` abstracts the concrete `head`/`next_arr` heap
   arrays into `build_index_spec`; the next proof should show `build_index'`
   establishes that relation, then use the chain/take lemmas to align
   `find_best_match'` with `take max_chain (index_bucket_spec ...)`.
