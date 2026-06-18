# Proof Strategy: VCDIFF Roundtrip Correctness in Isabelle/HOL

## Goal

Prove, in Isabelle/HOL on top of AutoCorres2, that the C encoder and decoder
in `encoder/vcdiff_enc.c` + `decoder/vcdiff_dec.c` invert each other. Concretely:

    theorem roundtrip:
      assumes "well_formed_inputs src tgt"
              "disjoint_buffers src tgt patch_out decoded_out scratch..."
              "sufficient_capacities ..."
      shows   "encode C src tgt patch_out ; decode C patch_out src decoded_out
               ⟹ decoded_out = tgt"

Out of scope for v1:

* **Decoder soundness against arbitrary conforming VCDIFF.** We only decode
  patches produced by *our* encoder. A separate project would prove the decoder
  correct for every RFC-3284-conformant input.
* **The `vcdiff_encode_add` legacy shim.** No verification effort on it.
* Secondary compression, multiple windows, VCD_TARGET, custom code tables,
  VCD_ADLER32. These are already rejected / unused at the C level.

Precedent: we proved the analogous theorem for a pure-Lean VCDIFF
implementation in `~/Programming/lean-bdiff`. The Lean proof sets the
*structure* (Varint → AddressCache → CodeTable → Wire format → Instruction
semantics → Full composition). Isabelle has to add an extra layer:
AutoCorres-generated monadic definitions don't match the specs directly, so
we need a **refinement** step connecting the two.

## Two-layer strategy

```
       ┌──────────────────────────────┐
Layer A│  Pure-HOL functional specs    │   All roundtrip reasoning happens here
       │  (list byte, nat, exceptions) │   — mirrors the Lean proof.
       └──────────────┬───────────────┘
                      │  refines to
                      ▼
       ┌──────────────────────────────┐
Layer B│  AutoCorres-lifted monadic    │   vcdiff_encode' / vcdiff_decode'
       │  definitions over C buffers   │   Proved equivalent to Layer A under
       └──────────────────────────────┘   explicit buffer/bounds preconditions.

                    Compose
                      │
                      ▼
       Theorem: running C encoder then C decoder recovers the target.
```

## 2026-06-14 encoder update

The encoder should follow the same refinement architecture as the decoder:

1. The pure encoder spec becomes non-degenerate and deterministic enough to
   match the C encoder's emitted bytes.
2. All roundtrip properties are proved at Layer A.
3. Layer B proves that `vcdiff_encode'` writes `encode_spec src tgt` on
   success, rather than proving `decode_spec` success directly inside the C
   encoder proof.

The old single-ADD encoder remains useful as a baseline theorem, but it is not
the final refinement target.

**Why two layers and not a direct proof on the monadic form?** Three reasons:

1. The C uses file-scope arrays (`near_arr`, `same_arr`, `code_tbl`,
   `head_arr`) as mutable state. Reasoning about them directly in AutoCorres's
   state monad is painful; hoisting to pure specs turns them into function
   arguments and return values.
2. Lean proofs already worked at the pure level — the spec-level lemma
   structure (varint roundtrip, cache roundtrip, code-table exhaustion,
   instruction-semantics induction) ports over.
3. Refinement is local: each helper in the C (`read_varint`, `decode_address`,
   `write_varint`, `best_mode`, …) gets its own Hoare triple, discharged with
   `runs_to_vcg`, proven independently. Failures stay local.

## Layer A: Pure specifications

Target directory: `isabelle/Spec/`. Files and responsibilities:

### 1. `Bytes.thy`
* `type_synonym byte = "8 word"`
* Carry around `nat` for sizes/addresses with a global bound `2^32` (match the
  C `unsigned int` domain). Use `32 word` where the C does bitwise ops; cast
  at boundaries. Keep bounds explicit in preconditions — this is cleaner than
  implicitly-typed reasoning and matches the approach Lean used
  (`< 2^31` bound to keep Nat arithmetic safe).

### 2. `Varint.thy`
Mirrors `Varint.lean` — both encode and decode as pure functions:

    varint_encode :: "nat ⇒ byte list"
    varint_decode :: "byte list ⇒ (nat × byte list) option"   -- max 5 bytes, big-endian

Key lemmas (port of Lean Phase A):
* `varint_decode (varint_encode n @ rest) = Some (n, rest)` when `n < 2^32`.
* `length (varint_encode n) ≤ 5` when `n < 2^35`.

Isabelle's `word_bitwise` / `bv_decide`-style tactics on `32 word` handle the
bitwise work; the Nat-level structure (`n / 128`, `n mod 128` induction) is the
same as Lean.

### 3. `CodeTable.thy`
The 256-entry default table, written out as an HOL function
`default_entry :: nat ⇒ inst × inst`, plus the inverse predicates used by the
encoder:
* `find_single_add_opcode`, `find_single_copy_opcode`, `find_single_run_opcode`
* `find_add_copy_opcode`, `find_copy_add_opcode`

**Exhaustive lemmas** (Lean proved these with `interval_cases + native_decide`;
Isabelle uses `value`/`code_datatype` + `eval` for the exhaustion and
`simp`/`auto` for the ranges). One key lemma per shape, e.g.:

    lemma lookup_add_opcode_single:
      assumes "1 ≤ sz" "sz ≤ 17"
      shows   "default_entry (1 + sz) = (ADD sz, NOOP)"

### 4. `AddressCache.thy`
Record of the mutable cache:

    record cache = near :: "nat list"     -- length 4
                   near_ptr :: nat
                   same :: "nat list"     -- length 768

* `cache_init`, `cache_update`.
* `encode_address :: cache ⇒ nat ⇒ nat ⇒ nat × byte list × cache`
  — picks the cheapest of 9 modes.
* `decode_address :: cache ⇒ nat ⇒ nat ⇒ byte list ⇒ ((nat × byte list) × cache) option`.

Roundtrip lemma:

    lemma encode_decode_address:
      assumes "addr < 2^32" "here < 2^32"
      shows   "let (mode, bs, c') = encode_address c addr here in
               decode_address c mode here (bs @ rest) = Some ((addr, rest), c')"

Mirrors Lean Phase B. The cache-state-equality part (both sides produce the
same `c'`) is crucial — it's what lets the inductive encode→decode proof thread
through successive instructions.

### 5. `Instructions.thy`
The intermediate representation between encoder and decoder:

    datatype raw_inst = Add "byte list" | Copy nat nat | Run byte nat

    exec_inst :: "raw_inst list ⇒ byte list ⇒ byte list ⇒ byte list option"
    -- source_segment → target_so_far → full_target_or_None

`exec_inst` handles overlap semantics for COPY from the "combined window"
(source ∥ target decoded so far) exactly as the C COPY loop does.

### 6. `Encoder_Spec.thy` / `Decoder_Spec.thy`
Top-level pure functions:

    encode_spec :: "byte list ⇒ byte list ⇒ byte list"
    decode_spec :: "byte list ⇒ byte list ⇒ byte list + decode_error"

The shapes mirror the C entry points but return pure values. They're thin
orchestrators on top of the helpers above. For the encoder, this now means a
realistic C-shaped spec: source index construction, greedy match search, RUN
detection, pending ADD buffering, COPY emission, address-cache mode choice,
opcode fusion, window section construction, and serialization.

Crucially, the specs must be **executable** — use Isabelle's `code_generator`
so we can test that `patch = encode_spec src tgt` and `decode_spec patch src =
Inl tgt` on concrete inputs before investing proof effort, and so we can
compare pure encoder output against C encoder output.

### 7. `Spec_Roundtrip.thy`
The main pure-level theorem:

    theorem encode_spec_roundtrip:
      assumes "length src < 2^32"
              "length tgt < 2^32 - 32"
              "length src + length tgt < 2^32"
      shows   "decode_spec (encode_spec src tgt) src = Inl tgt"

Proof decomposition:
1. Cache roundtrip (§4 lemma above).
2. Code-table exhaustion (§3 lemmas).
3. Varint roundtrip (§2 lemma).
4. Encoder-spec correctness: every instruction or section emitted by the
   non-degenerate spec covers exactly the next target prefix. COPY correctness
   comes from the pure matcher; RUN correctness comes from pure run scanning;
   pending ADD correctness comes from the pure pending-buffer invariant.
5. Wire-format roundtrip: header + window serialization parses back.
6. Compose.

## Layer B: AutoCorres refinement

Target directory: `isabelle/Refine/`. Files:

### `VcdiffDec_Refine.thy`
For each C helper, a Hoare triple saying "under these preconditions, the
monadic function returns the spec result and leaves the heap updated in the
spec-predicted way." Template shape, following the Memset/Memcpy examples in
`afp/…/AutoCorres2/tests/examples/`:

    lemma read_varint_refine:
      "{ buf_valid buf patch_len
       ∧ pos ≤ patch_len
       ∧ patch_len < 2^32 }
         read_varint' buf patch_len pos
       { λrv s. case rv of
           ⦇pos=p', val=v, err=e⦈ ⇒
             case varint_decode (drop pos (take patch_len (heap_bytes s buf))) of
               Some (v_spec, rest) ⇒ e = 0 ∧ v = v_spec ∧ p' = patch_len - length rest
             | None                 ⇒ e ≠ 0 }

Key obstacles and how we address them:

* **File-scope caches (`near_arr`, `same_arr`, `code_tbl`, `head_arr`)** appear
  in the global state. The refinement invariant asserts "their contents are
  exactly `near_spec`, `same_spec`, etc." Threading this through `runs_to_vcg`
  is mostly bookkeeping — each helper that updates the caches gets an
  invariant-preservation lemma.
* **Pointer disjointness**: `src`, `tgt`, `out`, `patch`, `next_arr`,
  `pending`, `data_sec`, `inst_sec`, `addr_sec` all must be non-overlapping.
  Bundle this as `vcdiff_buffers_disjoint` once and reuse.
* **Loop invariants**: the main instruction dispatch loop in `vcdiff_decode`
  is the biggest proof — mirrors Memset's `whileLoop` invariant pattern. The
  invariant carries `(tgt_pos, data_cursor, inst_cursor, addr_cursor,
  near_ptr, near_arr_contents, same_arr_contents)` together with "the bytes
  already written to `out[0..tgt_pos)` equal the prefix of `decode_spec`'s
  output so far." The encoder's main loop is analogous.

The decoder refinement target:

    lemma vcdiff_decode_refine:
      "...preconditions... ⟹
       vcdiff_decode' patch patch_len src src_len out out_cap out_len_ptr ⦃s⦄
        ⦃λrv s'. rv = 0 ⟷ decode_spec (heap_bytes s patch patch_len)
                                       (heap_bytes s src src_len)
                          = Inl tgt
               ∧ rv = 0 ⟶ heap_bytes s' out (length tgt) = tgt
                         ∧ heap_uint32 s' out_len_ptr = length tgt⦄"

The encoder refinement target is byte equality with the non-degenerate pure
encoder spec on success:

    lemma vcdiff_encode_refine:
      "...preconditions... ⟹ patch = encode_spec src_bytes tgt_bytes ⟹
       vcdiff_encode' out out_cap src src_len tgt tgt_len scratch ⦃s⦄
        ⦃λrv s'. rv = length patch
               ∧ heap_bytes s' out (length patch) = patch⦄"

### Composition: `Roundtrip.thy`
Combines `vcdiff_decode_refine`, `vcdiff_encode_refine`, and
`encode_spec_roundtrip`:

    theorem c_roundtrip:
      assumes preconds   -- buffer validity, disjointness, capacity bounds
      shows
        "⦃s⦄
           do patch_len ← vcdiff_encode' out out_cap src src_len tgt tgt_len scratch;
              decode_res ← vcdiff_decode' out patch_len src src_len decoded decoded_cap;
              return decode_res
         ⦃λ(patch_len, rv) s'.
             patch_len ≠ 0
           ∧ rv = 0
           ∧ heap_bytes s' decoded tgt_len = heap_bytes s tgt tgt_len ⦄"

## Phased work plan

Ordered by dependency. Each phase checks in independently, nothing downstream
starts with a `sorry` upstream.

| Phase | Goal | Rough effort | Depends on |
|-------|------|--------------|------------|
| 0 | Scaffold `isabelle/Spec/` and `isabelle/Refine/` sessions, wire `ROOT` files so `isabelle build -d . CdeltaProof` compiles an empty theory importing AutoCorres2 and our existing `CdeltaEncoder`/`CdeltaDecoder` | half day | — |
| A.1 | `Varint.thy` + roundtrip lemma | 1–3 days | Phase 0 |
| A.2 | `AddressCache.thy` + encode/decode inversion | 1–3 days | A.1 |
| A.3 | `CodeTable.thy` + exhaustion lemmas via `eval` | 1–2 days | — |
| A.4 | `Instructions.thy` + `exec_inst` correctness | 2–4 days | A.2, A.3 |
| A.5 | Baseline `Encoder_Spec.thy`, `Decoder_Spec.thy`, executable via `code_generator`; sanity-check with `value` against test corpus | done | A.4 |
| A.6 | Baseline `Spec_Roundtrip.thy` for the single-ADD encoder | done | A.5 |
| A.7 | Non-degenerate pure encoder spec matching the C algorithm | done | A.1–A.6 |
| A.8 | Non-degenerate spec roundtrip theorem | done | A.7 |
| B.1 | Refine all leaf helpers in `vcdiff_dec.c` (read_byte, read_varint, decode_address) | 3–5 days | A.1, A.2 |
| B.2 | Refine `vcdiff_decode'` main loop (the instruction-dispatch invariant) | 1–2 weeks | A.4, B.1 |
| B.3 | Retarget encoder leaf helpers to pure section builders; refine hash index, matcher, best_mode, and emit helpers | 1–2 weeks | A.7, Memcpy patterns |
| B.4 | Refine `encode_window'` to `encode_window_spec` | 1–2 weeks | A.7, B.3 |
| B.5 | Refine `vcdiff_encode'` top-level serialization to `encode_spec` bytes | 3–5 days | B.4 |
| C | Compose refinements with `encode_spec_roundtrip` into `c_roundtrip` | 2–4 days | A.8, B.2, B.5 |

Realistic total: **6–12 weeks** depending on how much AutoCorres-specific
automation we have to hand-build vs. reuse. Bulk of the time is B.2 + B.4 +
A.6.

## Risks and mitigation

* **AutoCorres heap-lift turns the encoder into an untractable term.** The
  file-scope arrays are already there specifically to sidestep this. Before
  starting B.3, sanity-check that `vcdiff_encode'` lifts cleanly (already
  confirmed per `project_encoder_v0.md`). If something breaks later, fall back
  to `no_heap_abs` on the troublemaker — costs proof effort but unblocks.
* **Spec drift from C.** Because we wrote the C first, the spec is
  essentially a decompilation. Mitigation: keep specs executable, test against
  the in-tree xdelta3 corpus before writing any proofs on top. A broken spec
  will catch at A.5, not at A.6 or beyond.
* **Instruction-dispatch loop invariant is huge.** Lean's
  `encodeInstList_decodeLoop_roundtrip` took substantial effort. Keep the
  per-iteration invariant small by defining `combined_window` and
  `decode_progress` up front and proving one invariant lemma per
  instruction type (ADD / COPY / RUN / fused).
* **Varint-heavy bit reasoning.** Isabelle has `word_bitwise`, but it's
  slower than Lean's `bv_decide` on multi-byte lemmas. Budget extra time on
  A.1 if naive tactics time out; fall back to explicit case splits on bytes.
* **AutoCorres `whileLoop` rules.** The Memset/Memcpy examples show the
  right pattern (`runs_to_whileLoop_res'` with explicit measure + invariant).
  Keep those theories open as a reference.

## Up-front decisions (locked)

1. **Scope**: roundtrip only (`decode (encode src tgt) src = tgt`), not full
   decoder completeness.
2. **Layering**: two layers — pure HOL specs carry the roundtrip, AutoCorres
   refinement is separate.
3. **Bounds**: explicit preconditions `src_len, tgt_len, patch_len < 2^32`
   (match C `unsigned int`). Tighten to `< 2^31` locally if Nat arithmetic
   gets in the way.
4. **Spec executability**: yes — run `value` / `code_generator` tests on the
   xdelta3 corpus before investing proof effort.
5. **Exclude `vcdiff_encode_add`** — legacy shim, not in scope.

## Open questions (to revisit when we hit them)

* **How much code duplication between encoder and decoder caches?** The
  address cache spec is shared; the C implementations are not (encoder has
  `best_mode` on top). Keep shared pieces in `AddressCache.thy`, encoder-only
  helpers in `Encoder_Spec.thy`.
* **Opcode-fusion representation in the spec.** The encoder fuses
  ADD(1..4)+COPY(4..6) into single opcodes where the table allows; the
  decoder is oblivious (it just executes both half-instructions). Spec: emit
  the two-instruction form at the `raw_inst list` level, then have a
  `select_opcode :: raw_inst × raw_inst option ⇒ opcode × needs_varint`
  function that matches the C's `add_copy_opcode`. This keeps the roundtrip
  theorem clean: encoder → inst list → wire bytes → parser → inst list →
  executor, with fusion a pure wire-level concern.
* **Do we bundle all scratch buffers into one precondition predicate
  `vcdiff_scratch_ok`?** Probably yes once B.3 starts — the list of scratch
  buffers (next_arr, pending, data_sec, inst_sec, addr_sec) is long and all
  callers have the same validity/disjointness story.
