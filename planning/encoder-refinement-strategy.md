# Encoder Refinement Strategy

## Context

Phase A is complete: `spec/` proves `decode_spec (encode_spec src tgt) src
= Inl tgt` sorry-free for a degenerate encoder that emits a single `RAdd
tgt` instruction. The C encoder in `encoder/vcdiff_enc.c` is a real greedy
matcher with source-matching, RUN splitting, address-cache mode selection,
and opcode fusion — it produces substantially different bytes than
`encode_spec` for the same inputs.

**Key observation:** byte-level refinement `encode_c = encode_spec` is
**false**. So the shape of Phase B cannot be "encoder monadic function
matches encoder pure spec"; that would be proving something untrue.

The decoder side is fine — `decode_c` and `decode_spec` are both
deterministic parsers of the same wire format, and byte-level equality
refinement is the clean statement.

## Strategy: parametric spec + end-to-end C theorem

We adopt options (1) + (3) from the sketch:

**(1) Refactor `spec_roundtrip` to be matcher-parametric.** Drop the
degenerate-specific statement as the top-level theorem. Replace with a
generic theorem quantified over any instruction list satisfying a
well-formedness predicate. The degenerate matcher becomes one concrete
instantiation, kept for sanity and as an executable test target, but
stops being the theorem we cite downstream.

**(3) Prove the end-to-end C-encoder theorem directly** using (a) the
decoder refinement and (b) a proof that C's matcher produces an
instruction list satisfying the well-formedness predicate.

No intermediate realistic-encoder spec. We skip the full
`encodeInstList_decodeLoop_roundtrip`-style proof (the 4k-line beast in
Lean) by making the parametric roundtrip theorem the cite target instead.

## Work breakdown

### Step 1: refactor pure spec into matcher-parametric form

Target: `spec/Spec_Roundtrip.thy` exposes a theorem of the shape

```isabelle
theorem roundtrip_generic:
  assumes "valid_insts src tgt insts"
          "length src < 2 ^ 32"
          "length tgt < 2 ^ 32 - 32"
  shows   "decode_spec (serialize_from_insts src tgt insts) src = Inl tgt"
```

where `valid_insts` bundles everything the encoder must guarantee:

```isabelle
definition valid_insts :: "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list \<Rightarrow> bool" where
  "valid_insts src tgt insts =
     ( exec_inst_list src insts [] = tgt
     \<and> (\<forall>i \<in> set insts. wf_inst src tgt i)
     \<and> no_oversize insts (2^32) )"
```

and `wf_inst` captures per-instruction well-formedness (ADD length bounds,
COPY address < combined-window size at emission point, RUN size > 0, etc.).

`serialize_from_insts` is the current `encode_window` + `serialize`
composition, factored out to take an arbitrary instruction list.

**Work required:**

- Extract `serialize_from_insts src tgt insts` from `encode_spec`:
  - run `encode_window insts (length src)`
  - run `serialize src tgt data inst addr`.
  That's already the shape; just need to stop hard-coding
  `generate_instructions = [RAdd tgt]`.

- State `valid_insts` precisely. The tricky bit is `wf_inst` for COPY: the
  address is valid *at the point of emission*, not statically. So
  `wf_inst` has to mention the partial target, i.e. it's not just a
  per-instruction predicate but a per-(prefix, instruction) predicate.
  Cleanest form:

  ```isabelle
  definition wf_insts :: "byte list \<Rightarrow> raw_inst list \<Rightarrow> bool" where
    "wf_insts src insts = wf_insts_aux src insts []"
  fun wf_insts_aux where
    "wf_insts_aux src [] tgt = True"
  | "wf_insts_aux src (RAdd bs # is) tgt = (length bs > 0 \<and> wf_insts_aux src is (tgt @ bs))"
  | "wf_insts_aux src (RRun b n # is) tgt = (n > 0 \<and> wf_insts_aux src is (tgt @ replicate n b))"
  | "wf_insts_aux src (RCopy a n # is) tgt =
       (n > 0 \<and> a < length src + length tgt
      \<and> wf_insts_aux src is (copy_loop src tgt a n))"
  ```

- Re-prove the top-level composition theorem with
  `generate_instructions` replaced by an abstract `insts` variable and
  the `valid_insts` premise feeding through. Most of the existing
  `parse_window_*` / `apply_window_*` lemmas carry over verbatim; the
  `decode_loop` step generalises via induction on `insts`.

**This is the hard piece of the refactor.** Rough estimate: the
induction is the analogue of Lean's
`encodeInstList_decodeLoop_roundtrip` but *half* the work because we
only need to show the wire-format roundtrip, not the matcher's
correctness. Realistic effort: 1-2 weeks to extend the existing
`Spec_Roundtrip.thy` (~800 LoC) to ~2000 LoC.

- Keep a concrete `theorem roundtrip_degenerate` that instantiates
  `insts = [RAdd tgt]` and derives the current `spec_roundtrip` as a
  corollary. Serves as a sanity check that the refactor didn't break
  the existing reasoning.

### Step 2: decoder refinement

In `refine/VcdiffDec_Refine.thy` (new directory), prove:

```isabelle
theorem decode_c_refines_spec:
  "\<lbrakk> valid_pointers patch patch_len src src_len out out_cap out_len_ptr;
     disjoint_buffers patch src out;
     patch_len < 2^32; src_len < 2^32; out_cap < 2^32 \<rbrakk>
   \<Longrightarrow> vcdiff_decode' patch patch_len src src_len out out_cap out_len_ptr \<bullet> s
       \<lbrace> \<lambda>rv s'.
           case decode_spec (heap_bytes s patch patch_len)
                            (heap_bytes s src src_len) of
             Inl tgt \<Rightarrow> rv = 0
                       \<and> out_cap \<ge> length tgt
                       \<and> heap_bytes s' out (length tgt) = tgt
                       \<and> heap_uint32 s' out_len_ptr = length tgt
                       \<and> (\<forall>p \<notin> {out, out_len_ptr}. heap_preserved s s' p)
           | Inr _  \<Rightarrow> rv \<noteq> 0 \<rbrace>"
```

Size estimate: 2-3 weeks. Most time on the main loop invariant (data/inst/
addr cursor progress + address-cache shadow state).

Per-helper refinement lemmas (`read_byte`, `read_varint`, `decode_address`)
are mechanical and can be mined from existing AutoCorres2 examples like
`memcpy.c` / `memset.c`.

### Step 3: encoder instruction-validity proof

Forget refining the C encoder byte-for-byte against anything. Prove only
that its output, treated as an instruction list, satisfies `wf_insts`
and `exec_inst_list src insts [] = tgt`.

Define an abstraction function `c_encoder_insts :: s \<Rightarrow> ptr \<Rightarrow> ptr \<Rightarrow>
raw_inst list` that, given the post-encode state of the C encoder,
reconstructs the instruction list from the emitted bytes (or from a
ghost-trace that the refinement carries).

Key intermediate lemma:

```isabelle
theorem c_encode_emits_valid_insts:
  "\<lbrakk> ... preconds ... \<rbrakk>
   \<Longrightarrow> vcdiff_encode' out out_cap src src_len tgt tgt_len ... \<bullet> s
       \<lbrace> \<lambda>rv s'.
           rv \<noteq> 0 \<longrightarrow>
             (\<exists>insts.
                 parse_insts (heap_bytes s' out rv) = Some insts
               \<and> valid_insts (heap_bytes s src src_len)
                             (heap_bytes s tgt tgt_len) insts
               \<and> heap_bytes s' out rv
                   = serialize_from_insts (heap_bytes s src src_len)
                                          (heap_bytes s tgt tgt_len) insts)
         \<rbrace>"
```

The third conjunct — "the emitted bytes equal `serialize_from_insts`
applied to the instruction list" — is what makes this refine against
the pure serializer without requiring byte-level equality with a
spec encoder.

**This is the new hard bit.** Proving the C encoder maintains the
`valid_insts` invariant over its main loop is similar in character to
the Lean-bdiff `findBestMatch_good` / `generateInstructionsLoop_valid`
chain. Realistic effort: 3-5 weeks. Components:

- `find_best_match_valid`: the matches returned by `find_best_match`
  cover byte-equal regions of src/tgt (analogue of Lean's
  `extendMatch_bytes_eq`).
- `best_mode_well_formed`: the address returned by `best_mode` is
  decodable (follows from the pure `encode_address_wf` we already
  proved, plus the fact that C's `best_mode` matches the spec's
  `encode_address`).
- `encode_window_valid`: the C main loop emits a valid instruction
  sequence.
- `serialize_c_matches_pure`: the C's serialize function emits the
  same bytes as `serialize_from_insts`.

### Step 4: compose

End-to-end C roundtrip theorem:

```isabelle
theorem c_roundtrip:
  "\<lbrakk> buffer preconds + disjointness + capacity bounds + input-size bounds \<rbrakk>
   \<Longrightarrow> do patch_len \<leftarrow> vcdiff_encode' out out_cap src src_len tgt tgt_len scratch;
          rv \<leftarrow> vcdiff_decode' out patch_len src src_len dec_out dec_out_cap dec_out_len_ptr;
          return rv
      \<bullet> s
      \<lbrace> \<lambda>(_, rv) s'.
          patch_len \<noteq> 0 \<longrightarrow>
            rv = 0 \<and> heap_bytes s' dec_out tgt_len = heap_bytes s tgt tgt_len \<rbrace>"
```

Proof: step 2 gives `decode_c = decode_spec` modulo byte extraction; step
3 gives that the C encoder's output bytes come from a `valid_insts` chain
via `serialize_from_insts`; step 1 gives that decoding any such
serialization recovers the target.

Estimate: 2-4 days once steps 1-3 are done.

## Effort summary

| Step | Effort | Depends on |
|------|--------|------------|
| 1. matcher-parametric spec | 1-2 weeks | Phase A (done) |
| 2. decoder refinement | 2-3 weeks | Step 1 |
| 3. encoder validity | 3-5 weeks | Step 1 |
| 4. composition | 2-4 days | Steps 2, 3 |
| Total | **6-11 weeks** | |

This is ~50-80% of the original Phase B estimate (6-12 weeks) in the top-
level plan — we save on not having to prove a realistic encoder is
byte-identical to a spec encoder, but we pay for the matcher-parametric
lemma.

## What we give up

- **Concrete encoder spec traceability.** There's no pure HOL function
  that spits out the exact bytes the C encoder produces. If someone
  asks "what does the encoder output for input X?", the answer lives in
  the C, not a spec. The spec says "it's *some* serialization of a
  valid instruction list that executes to tgt", which is enough for
  correctness but less good for debugging.
- **Decoupled encoder refinement.** Changing the C encoder's matching
  heuristics invalidates step 3 but not step 2. That's the same as
  option (2) would cost, but at least there the failure mode is "spec
  diverges from C", which is sometimes easier to diagnose than "validity
  invariant broken at this line".

## What we gain

- **Skipping the big Lean-style proof.** We don't need the full
  instruction-dispatch-loop correctness proof that dominated the Lean
  effort. The parametric roundtrip theorem plays the same role.
- **Matcher improvements are free.** Adding lazy matching, better
  address mode selection, etc. only needs re-proving step 3 for the
  new matcher. No touch to steps 1, 2, or 4.
- **Decoder stays clean.** A realistic-encoder intermediate layer
  wouldn't buy us anything on the decoder side; this approach keeps
  that cleanliness.

## File layout plan

```
spec/
  Bytes.thy                  (unchanged)
  Varint.thy                 (unchanged)
  AddressCache.thy           (unchanged)
  CodeTable.thy              (unchanged)
  Instructions.thy           (unchanged, export wf_insts_aux + copy_loop)
  Encoder_Spec.thy           (refactor: encode_spec becomes degenerate
                              instantiation; serialize_from_insts is the
                              exported primitive)
  Decoder_Spec.thy           (unchanged)
  Spec_Roundtrip.thy         (refactor: theorem roundtrip_generic as main;
                              theorem spec_roundtrip as corollary)

refine/
  ROOT                       (new session depending on CdeltaSpec +
                              CdeltaEncoder + CdeltaDecoder)
  VcdiffDec_Refine.thy       (Step 2: decoder refinement)
  VcdiffEnc_Refine.thy       (Step 3: encoder validity)
  Roundtrip.thy              (Step 4: compose)
```

## Open questions to resolve at start of Phase B

1. **Ghost state for reconstruction.** Does the encoder-validity proof
   need a ghost trace of emitted instructions to recover the
   instruction list, or can we re-parse the bytes? Re-parsing is
   cleaner but adds a decoder-style proof for the encoder's output
   path. Leaning toward ghost trace.

2. **Heap abstraction for ByteArray buffers.** AutoCorres's
   `heap_bytes` concrete API vs a spec-level `byte list`. Need a
   conversion lemma + non-aliasing story.

3. **Cache state in the refinement.** The file-scope arrays
   (`near_arr`, `same_arr`, `code_tbl`, `head_arr`) are part of the
   global state. Refinement has to carry an invariant that their
   contents match the spec's pure cache. Pattern is standard (see
   Memset.thy) but accumulates bookkeeping.

4. **Scratch-buffer disjointness.** The encoder takes many scratch
   buffers. Decide whether to bundle these into a single
   `vcdiff_scratch_ok` predicate or keep them as individual
   preconditions. Bundle probably wins for readability.

See also `planning/proof-strategy.md` §Risks for the general Phase B
caveats.
