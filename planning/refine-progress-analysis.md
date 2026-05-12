# Refine progress — critical analysis (2026-05-12)

Honest critical evaluation of where the decoder refinement proof stands
after the exit_weakening closures.

## What we accomplished

- 8 exit_weakening residuals closed (the *easiest* of the 12 obligations)
- ie_le eliminated via folding
- `cache_abs_unique`, `parse_window_with_source`, `decode_loop_inv_init_core` added
- Abstract lemma strengthened with `e ≠ 0`
- `decode_loop_inv_plus_advance` proved last session (the body-preservation bridge)

## What's actually still required

**Inv_entry × 4** (~100–200 lines each): tractable. We have all the pieces —
`decode_loop_inv_plus_entry`, `decode_loop_inv_init_core`,
`parse_window_{no,with}_source`, `decode_loop_terminates`. It's bookkeeping work.

**Body_preserves × 4** (~500–1000 lines each if done naively, 500 lines total if
factored): this is the heart of the decoder proof and **hasn't been started**.
Each one is: opcode read → `which ∈ {0,1}` whileLoop → dispatch on add/run/copy
→ inner byte-copy whileLoops → prove one iteration = one `decode_one` step via
`decode_loop_inv_plus_advance`. The exit closures, satisfying as they were,
are roughly 1% of the remaining work.

## Structural problems I glossed over

1. **C-vs-spec exit-check mismatch.** The C returns `VCD_ERR_SIZE` if
   `data_cursor != data_end` or `addr_cursor != addr_end` at exit. The pure
   spec's `decode_loop` terminates on `ds_inst_rem = []` and doesn't care about
   leftover data/addr bytes. If a spec-Inl patch has any leftover bytes, C
   returns error and our `Inl tgt ⇒ r = Result 0` theorem is false. We either
   need to tighten the spec or add encoder-side lemmas that our encoder never
   emits such patches.

2. **`out_cap_enough` is a hack.** The theorem takes
   `∀ tgt. decode_spec = Inl tgt ⟹ length tgt ≤ unat out_cap` as a premise,
   which is a roundabout way of saying "the caller knew the output size in
   advance". This narrows the theorem's utility.

3. **Inr case is entirely sorry** (line 7835). That's half the theorem.

4. **`build_code_table'_preserves_typing` is sorry** (line 2820). The main
   proof depends on it.

5. **`vcdiff_decode'_prefix_correct` sorry** at 6866 — legacy cruft from the
   old abandoned proof.

## Are we on a path to finishing?

**Yes structurally, no in terms of remaining effort.** The proof architecture
is now sound and validated end-to-end. But the remaining work is probably
2–4 weeks of focused proof engineering — and that's assuming the spec
mismatches resolve favorably. The 8 exit closures should not be taken as
"6/8 of the way done."

## Strategic recommendation

Before doing any more body_preserves work, we should:

1. **Settle the exit-check mismatch.** Either prove an encoder-side "windows
   are exact" lemma, or weaken the Inl case to allow C to return size-error
   when the patch has leftover bytes. The current theorem statement is
   probably unprovable on well-formed inputs without one of these.

2. **Factor body_preserves into ONE shared lemma** parameterized over the
   four varying values (`data_end`, `inst_end`, `addr_end`, outer state),
   proved once and applied four times. Doing it four separate times would be
   ~3000 lines of duplication.

3. **Decide whether to chase full functional correctness or a weaker
   property.** Maybe "C returns VCD_OK iff spec returns Inl and output buffer
   matches spec's tgt" is too strong for a first milestone, and "C is
   memory-safe and returns something consistent" would be more achievable.

That said — closing body_preserves for *one* branch with a non-trivial proof
would decisively prove the approach scales.
