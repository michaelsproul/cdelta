# Refinement Layer Progress

## Session 2026-05-10 evening 2 — continuation method confirmed

After the survey of l4v/AutoCorres2 patterns, applied the
`vcdiff_decode'_win_target_bit_nonok_built` template to discharge the
first of 4 top-level gets_the continuations:

```isabelle
apply (cases "pos + val < patch_len")
  \<comment> \<open>live case\<close>
  apply (rule exI[where x = "pr_t_C (pos + val + 1) (UCAST ...) VCD_OK"])
  apply (rule conjI)
   apply (subst read_byte'_spec[of "pos + val" patch_len state patch])
    subgoal  \<comment> \<open>ptr_valid via heap_typing chain + patch_ok\<close>
     apply (rule impI, subgoal_tac "heap_typing state = heap_typing s",
            simp, rule buf_valid_uintD[OF patch_ok], simp add: …)
    done
   subgoal by simp  \<comment> \<open>if-simplification to the live branch\<close>
  apply runs_to_vcg
  \<comment> \<open>Closes 6 buf_valid via simp add: buf_valid_def patch_ok\<close>
  apply (all \<open>(simp add: buf_valid_def patch_ok[simplified ...]; fail)?\<close>)
  \<comment> \<open>5 residuals: 2 pos-bounds + 3 more gets_the's.  Recursive pattern.\<close>
```

**Pattern verified**: after each `gets_the` discharge + inner
`runs_to_vcg`, the body advances substantially (6 buf_valid goals
closed trivially, exposing 3 more inner gets_the's for the di-byte /
dlen-byte / addr_len-byte reads, plus 2 word-arithmetic bounds).

**Expected scaling**: 4 top-level gets_the × 3 inner gets_the per
path = 12 witness discharges at 10-15 lines each.  Then the outer
whileLoop (once reached) handled via `supply runs_to_whileLoop_exn5
[where I=…, runs_to_vcg]`.  Total: ~200-300 lines of Isar for the
weak-form proof.

---

## Session 2026-05-10 summary (rescue branch, 28 commits)

**Major breakthroughs:**
1. **Two-step postcondition strategy (22+31 → 12 subgoals).**
   Replaced the conjunctive `?Post = r = Result 0 ∧ output matches`
   (which generates unprovable Exn-branch obligations for every throw
   point) with `?WeakPost = r = Result 0 ⟶ output matches`.  Under
   `?WeakPost`, throw branches are vacuous; only 12 subgoals remain
   (8 trivial + 4 meaningful gets_the continuations).  Full derivation
   of `?Post` from `?WeakPost` + a separate "no failure" claim via
   `runs_to_weaken`.
2. **Word-level init-loop variants.**  `near_init_preserves_patch_heap_word`
   and `same_init_preserves_patch_heap_word` bridge AutoCorres's
   emitted `i < N` (word) guards to the original lemmas' `unat idx < N`
   (nat) form.  Enables `supply [where buf = patch, n = unat patch_len,
   p = out_len, runs_to_vcg]` to fire on the init loops in the body.
3. **`build_code_table'_preserves_typing`.**  Stronger variant
   extending `build_code_table'_spec` with `heap_typing` preservation,
   needed downstream to derive `buf_valid` across the build_code_table'
   call.  Currently sorry; proof is re-running the body's VCG with a
   heavier invariant that includes heap_typing.
4. **`read_byte'_total`.**  `read_byte'` always returns `Some` under
   `buf_valid s buf (unat len)` + `pos ≤ len`, discharging the
   `gets_the` existential obligations uniformly.
5. **`out_cap_enough` precondition.**  Added to `vcdiff_decode'_spec`
   because without it the Inl branch of the theorem is false.

**Closed subgoals:**
- 14 of 22 from the original strong-form runs_to_vcg (magic/hdr/bounds).
- 4 app-header contradictions from Inl via `parse_header_app`.
- 8 of 12 in the weak-form (all trivial via supply).

**Remaining work:**
- 4 gets_the continuations in the weak form, each containing the outer
  whileLoop + post-checks.  These 4 are structurally identical (differ
  only in entry state).
- The outer whileLoop proof itself.  Needs `decode_loop_inv` with a
  progress conjunct; current `decode_loop_inv` has everything except
  the "this state equals `decode_loop k init` for some k" claim.
- The strong-form derivation via `runs_to_weaken`.
- The Inr case.
- 1 inner sorry in `build_code_table'_preserves_typing`.

**5 sorries total** in `VcdiffDec_Refine.thy`.
Build green, ~35s incremental.

---



## Status (2026-05-10, evening) — rescue branch, Step 3+4 partial

**Progress**: `vcdiff_decode'_spec` top-level stated with real
`decode_spec` postcondition, case-split on `decode_spec = Inl tgt / Inr e`.
Inl case 18/22 subgoals closed via supply-runs_to_vcg pattern:

* 14 easy subgoals (ptr_valid / magic / hdr / length bounds) closed
  via one-liner `subgoal using … by simp` lines.  The UCAST-bridge
  needed `word_bitwise` to close.
* 4 "app-header err-path contradiction" subgoals closed via
  `parse_header_app` extraction from Inl + `auto split: option.splits`.
* Remaining 4 subgoals: the full main body (win_ind + varints +
  outer whileLoop + post-checks) across 4 branches (code_tbl ∈ {0,1}
  × has-src flag ∈ {0,1}).

The Inr case is still a single sorry.  Proof strategy for it:
case-split on which parser failed (parse_header / parse_window /
apply_window), use the existing error-case lemmas for magic/hdr
failures, and discharge the rest by tracing the failure through
the C body.

## Main remaining work

### The outer whileLoop (critical path)

The single biggest remaining obligation.  Shape:

```
whileLoop (λ(ac, dc, ic, np, tp) s. ic < inst_end)
  (λ(ac, dc, ic, np, tp). do {
     p ← gets_the (read_byte' patch inst_end ic);
     unless (err_C p = 0) (throw (sint (err_C p)));
     (ac, dc, ic, np, tp, _) ← whileLoop (λ(_,_,_,_,_,w) _. w < 2)
       (λ(ac, dc, ic, np, tp, w). BODY_DISPATCH)
       (ac, dc, pos_C p, np, tp, 0);
     return (ac, dc, ic, np, tp)
  }) (addr_pos, data_pos, inst_pos, 0, 0)
```

Apply via `runs_to_whileLoop_exn [where I = decode_loop_inv_plus,
R = measure (\<lambda>((_,_,ic,_,_), _). unat inst_end - unat ic)]`
with the invariant extended to carry a progress claim linking the
pure spec state to the C cursor state (see "Invariant strengthening"
below).  Body obligation decomposes via another
`runs_to_whileLoop_exn` on the inner `which < 2` loop.

### Invariant strengthening (plan option c from discussion)

`decode_loop_inv` currently tracks the abstract `dec_state` at the
current moment but has no claim about the pure spec having produced
that state via a fixed number of `decode_one` applications.  For the
postcondition `heap_bytes t out = tgt` we need to know the abstract
state equals what `decode_loop` (the pure spec fuel-iterated) would
produce.

**Conjunctive extension** (preferred):

```
decode_loop_inv_plus s0 ... data_cursor inst_cursor addr_cursor tgt_pos np t \<equiv>
  decode_loop_inv s0 ... data_cursor inst_cursor addr_cursor tgt_pos np t \<and>
  (\<exists>dst dst0.
    decode_loop_inv_extract dst s0 ... data_cursor inst_cursor addr_cursor tgt_pos np t \<and>
    dst0 = initial_state_at_inst_pos \<and>
    (\<exists>k. decode_loop k src_seg (unat src_seg_len) tgt_len dst0 = Inl dst) \<and>
    (inst_cursor = inst_end \<longrightarrow>
       decode_loop (length (pw_inst win)) src_seg (unat src_seg_len) tgt_len dst0 = Inl dst))
```

Where `k` is the number of iterations the C loop has completed.  The
body-preservation shows this claim advances by exactly 1 per C
iteration via `decode_loop_inv_after_add/run/copy` (one `decode_one`
per iteration, with the two half-instructions internally corresponding
to two `exec_half` calls).

### Inr case

Strategy: split on which of parse_header / parse_window /
apply_window produced the Inr.  Each is closed by showing the
corresponding C path takes a throw.

Available lemmas: `vcdiff_decode'_short_patch`,
`vcdiff_decode'_magic{0,1,2,3}_nonok`, `vcdiff_decode'_hdr_nonok`,
`vcdiff_decode'_appheader_len5_nonok`,
`vcdiff_decode'_win_{ind,target_bit,mask,srcneed}_nonok_built`.

For failures not covered by the existing lemmas (varint truncation in
header-app, window varint, section-size mismatch, instruction-decode
failure), new per-failure-path lemmas may be needed — or we ride
along with the Inl main-body proof if we structure it as a partial-
refinement that covers both branches.

### Word-level init-loop variants (done)

**Solved.** Added `near_init_preserves_patch_heap_word` and
`same_init_preserves_patch_heap_word` with loop guards
`idx < (4 :: 32 word)` (word level) matching what AutoCorres emits.
Proved via `subst guard_eq` from the nat-form lemmas, where
`guard_eq` is `(λidx st. idx < 4) = (λidx st. unat idx < 4)` on
32-word.  Supplied as `[where buf = patch, n = unat patch_len,
p = out_len, runs_to_vcg]` to pin the free vars to our concrete
pointers.

After this, `runs_to_vcg` inside the main-body subgoal advances
through `build_code_table'` and both init loops, landing at
the win_ind `read_byte'` (= `gets_the (…)` existential).

### Mid-function whileLoop pattern (l4v / AutoCorres2)

From a survey of seL4/l4v and AutoCorres2 examples:

* **Pattern 2 (quicksort → partition)**: if the body contains a call
  to a separately-proved helper with its own Hoare triple, use `note
  helper_correct [runs_to_vcg]` and `runs_to_vcg` will step over the
  call atomically.
* **Pattern 3 (schorr_waite)**: for an **inline** whileLoop with no
  named helper, pre-instantiate the loop rule via `supply
  runs_to_whileLoop_exn5 [where I = …, R = …, runs_to_vcg]` (defining
  `runs_to_whileLoop_exn5 = runs_to_whileLoop_exn' [split_tuple C
  and B arity: 5]`).  Then `apply runs_to_vcg` consumes the loop by
  discharging the 5 standard subgoals (wf, init, ¬C⟶P, Exn⟶P,
  body).  This is what we need for our outer instruction-dispatch
  loop.

**Key caveat for our case**: the whileLoop is inside a `gets_the
(read_byte' …)` continuation.  `runs_to_vcg` processes the `gets_the`
via the default `runs_to_gets_the` rule, producing `∃v. read_byte' …
= Some v ∧ (continuation with whileLoop)` as a residual.  The
supplied `[runs_to_vcg]` rule for `gets_the_read_byte'_spec` does
not fire first (priority issue).  So the whileLoop is buried inside
the existential and can't be reached by the next `runs_to_vcg`.

**Workaround** (template at `vcdiff_decode'_win_target_bit_nonok_built`,
lines 3148-3229): discharge the gets_the manually with
`rule exI[where x = explicit_witness]; rule conjI; subst
read_byte'_spec[of ...]`, then `runs_to_vcg` again advances into the
continuation and — with `supply runs_to_whileLoop_exn5 [where I=…,
runs_to_vcg]` in scope — crosses the outer whileLoop atomically.

### Two-step strategy (KEY BREAKTHROUGH)

Rather than prove the conjunctive `?Post = (r = Result 0 ∧ output
matches)`, prove an intermediate `?WeakPost = (r = Result 0 ⟶
output matches)`.  The weak form makes all throw branches vacuous
(the antecedent `Exn e = Result 0` is false), so `runs_to_vcg` with
all supplies produces **only 12 subgoals instead of 22+31**:

  * 5 × `IS_VALID(8 word) s (patch +ₚ K)` for K = 0..4 — one-liner
    closures via `patchi_ok`
  * 1 × `IS_VALID(32 word) s out_len` — `out_len_ok`
  * 1 × `buf_valid s patch (unat patch_len)` — `patch_ok`
  * 1 × `5 ≤ patch_len` — `len_ge5_word`
  * 4 × `∃v. read_byte' … = Some v ∧ (rest of body runs correctly)`
    — these are the meaningful residuals

8 of the 12 close as one-liners.  The 4 remaining gets_the
continuations each contain the outer whileLoop + post-checks; they
are structurally identical (differ only in entry state), so one
proof + three mechanical copies.

Strong form `?Post` derived from `?WeakPost` + a separate
`r = Result 0` lemma (proving the decoder doesn't fail given Inl),
combined via `runs_to_weaken`.

Added helpers:
  * `read_byte'_total`: `read_byte' buf len pos s = Some v` for some
    v, given `buf_valid s buf (unat len)` and `pos ≤ len`.
  * Extended `?Post` with `out_cap_enough: length tgt ≤ unat out_cap`
    precondition (without this the theorem's Inl branch is false).

### Previous attempt: gets_the-existential for win_ind

**Partially solved.**  Made substantial progress:

* Added `build_code_table'_preserves_typing` (sorry) as a stronger
  supply rule so that downstream buf_valid facts are derivable.
* Added `out_cap_enough` assumption to the theorem statement
  (necessary — without it the Inl branch is false when the spec
  produces a tgt larger than out_cap).
* Closed word-bound arithmetic: `pos_C va + val_C va ≤ patch_len`
  (no overflow).
* Closed `buf_valid td patch` via the heap_typing-preservation chain.
* Invoked `read_byte'_spec` by subst, then `split if_splits;
  intro conjI impI` to produce two branches.

**Remaining**:

* Truncation branch (`pos_C va + val_C va = patch_len`): single
  subgoal `⟹ False`, needs a contradiction from Inl + parse_header_app
  (rest_h = [] ⟹ parse_window rest_h = Inr E_TRUNC ⟹ decode_spec =
  Inr, contradicting Inl).  Deferred.
* Success branch: after `apply runs_to_vcg`, produces 31 residual
  subgoals breaking down as:
  - 9 × `⟹ False` (contradictions from Inl — various win_ind bits,
    varint failures)
  - 6 × `unat (heap_w32 td out_len) = length tgt` (output length
    postcondition, multiple paths)
  - 6 × `heap_bytes td out (length tgt) = tgt` (output bytes
    postcondition, multiple paths)
  - 4 × `pr_t_C.err_C ... = 0` (varint read error checks)
  - 2 × `pos + val + 1 ≤ patch_len` (bound after advancing position)
  - 2 × `∃v. read_byte' ... = Some v ∧ ...` (di-byte, dlen-byte
    `gets_the`s — same pattern as win_ind)
  
  The `heap_bytes td out = tgt` is particularly troubling — `td` is
  the state *before* the outer whileLoop, but the postcondition claims
  the output is already correct.  This suggests either (a) `runs_to_vcg`
  applied the postcondition template to the pre-loop state, which means
  the loop obligation is somewhere else, or (b) there's a broken
  threading we haven't understood.  Investigate.

### Reality check on the outer whileLoop

Even when we reach it, the outer whileLoop is a major undertaking:
~200-400 lines of structured Isar covering invariant preservation
across the ADD / RUN / COPY dispatch, the progress claim tying
C cursors to pure-spec decode_loop execution, and termination.
Realistically, the session budget for Step 3+4 is 2-3 full days
of focused work from here.  Rescue branch currently at 16 commits
covering the architectural restart plus ~20 substantive
sub-lemma closures in the prefix.

### Inr case

Untouched.  Strategy sketched above (split on which parser
rejected, reuse existing error-case lemmas).  Could also ride
on Inl main-body proof by stating both in a unified
contrapositive form — previously rejected because the contrapositive
form requires the C to "compute the spec answer" even on failure,
which is circular.  A cleaner approach: prove C's Hoare triple
in the form "if r = Result 0 then ∃tgt. decode_spec = Inl tgt ∧
output matches", and derive the Inr case by contrapositive.  This
works as long as we don't need the Inr case to be stronger than
"C doesn't succeed".

## Status (2026-05-10) — rescue branch

The previous approach on `refine/close-loop-sorry` has been abandoned.
Audit found three problems with it that made further investment unsafe:

1. **Build hung** in the top-level `runs_to_vcg` for minutes and was
   killed. No incremental elaboration was possible.
2. **Postcondition was too weak to compose.**
   `vcdiff_decode'_prefix_correct` proved only `∃ret. r = Result ret`;
   the target theorem needs semantic correspondence to `decode_spec`.
3. **Main loop invariant was bespoke**, disconnected from
   `decode_loop_inv`. The ~2000 lines of sorry-free invariant-preservation
   infrastructure (`decode_loop_inv_after_{add,run,copy}` etc.) could not
   be applied inside the loop body.

The proximate cause of all three: a 500-line apply-script built from
`apply (rule runs_to_weaken[OF read_varint'_spec]) / apply (all
runs_to_vcg?)` peel chains. Every `runs_to_weaken` leaves a meta
implication that the next `runs_to_vcg` must re-decompose, so the goal
state compounds. This is **not** the idiomatic AutoCorres2 pattern.

## Idiomatic AutoCorres2 pattern (from AFP examples)

Surveying `AutoCorres2/tests/examples/` (IsPrime_Ex, Plus_Ex,
BinarySearch, Memcpy, Quicksort_Ex, SchorrWaite_Ex):

```isabelle
theorem foo_correct:
  assumes …
  shows "foo' args ∙ s ⦃ Q ⦄"
  unfolding foo'_def
  supply leaf_spec_1 [runs_to_vcg]   ← register Hoare triples as VCG rules
  supply leaf_spec_2 [runs_to_vcg]
  supply if_split [split del]         ← prevent split explosion
  apply runs_to_vcg                    ← ONE call decomposes the whole body
  subgoal … done                       ← close each residual side condition
  subgoal
    apply (rule runs_to_whileLoop_exn  ← loops get an explicit I + measure
      [where I = …, R = measure …])
    subgoal by …  (wf)
    subgoal by …  (init)
    subgoal by …  (exit ⇒ post)
    subgoal by …  (Exn case)
    subgoal                             ← body preserves I
      supply body_helper [runs_to_vcg]
      apply runs_to_vcg
      …
      done
    done
  done
```

Key facts:

* `runs_to_vcg` is tactic-extensible. `supply foo_spec [runs_to_vcg]`
  registers a named triple so the decomposer automatically discharges
  via it whenever `foo'` appears in the body, *without* unfolding
  `foo'_def` and *without* leaving a residual meta-implication.
  This is the AutoCorres2 analog of l4v's `ctac add: foo_ccorres`.
* Goal-size control comes from `supply if_split [split del]` and
  (for `runs_to_vcg` v2) `(nosplit) (no_unsafe_hyp_subst)` flags.

l4v's C-refinement proofs (`proof/crefine/`) use the `ccorres` /
`ctac` cascade instead, but the underlying shape — one leaf spec per
sequential C step, one invariant-per-loop — is identical.

## Target theorem (stated in VcdiffDec_Refine.thy, sorry)

```
lemma vcdiff_decode'_spec:
  fixes patch src out :: "8 word ptr"
    and patch_len src_len out_cap :: "32 word"
    and out_len :: "32 word ptr"
  assumes ptr_valid (heap_typing s) out_len
      and buf_valid s patch (unat patch_len)
      and buf_valid s src   (unat src_len)
      and buf_valid s out   (unat out_cap)
      and code_tbl_built_'' s ≠ 0
      and out/patch/src disjointness + out injectivity
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len ∙ s
           ⦃ λr t.
              case decode_spec (heap_bytes s patch (unat patch_len))
                               (heap_bytes s src   (unat src_len)) of
                Inl tgt ⇒ r = Result 0 ∧
                          unat (heap_w32 t out_len) = length tgt ∧
                          heap_bytes t out (length tgt) = tgt
              | Inr _  ⇒ (∃e. r = Result e ∧ e ≠ 0) ⦄"
```

Under AutoCorres2 the return type of `vcdiff_decode'` is `(unit, int)
exception_or_result`, so `VCD_OK` in the postcondition is written as
the integer `0`.

## Reuse audit (of the 169 lemmas already proved)

Roughly:

* **~11 leaf Hoare triples** wired in via `supply [runs_to_vcg]`:
  `read_byte'_spec`, `read_byte'_list_spec`, `read_varint'_spec`,
  `decode_address'_spec`, `build_code_table'_spec` (has 3 sorrys of
  its own, separate concern), `near_init_preserves_patch_heap`,
  `same_init_preserves_patch_heap`, `add_loop_correct`,
  `run_loop_correct`, `copy_loop_correct`.

* **~25 invariant-side helpers** consumed inside
  `decode_window_loop_correct`'s body subgoal:
  `decode_loop_inv{,D,_init}`, `decode_loop_inv_after_{add,run,copy}`,
  `decode_loop_inv_advance_inst{,_n}`, `inv_pop_byte_cursor`,
  `inv_inst_pop_byte`, `inv_inst_varint_bridge`,
  `inv_no_overflow_{data,tgt}`, `inv_data_rem_length`,
  `inv_tgt_length`, `exec_half_{add,run,copy}_conditions`,
  `exec_half_noop`, `resolve_size_{length,nonzero,varint}`,
  `code_tbl_matches_{lookup,first_half,second_half}`,
  `byte_to_hi_tag_{ity,isz}`, `cursor_advance_drop`,
  `remaining_bytes_length`, `buf_valid_mono`.

* **~30 ambient simp rules** (`heap_bytes_*`, `heap_w{8,32}_*`,
  `ptr_valid_*`, `buf_valid_*` under heap updates, `ptr_add_inject{,_nat}`,
  …). Tagged `[simp]` already.

* **~20 varint chaining / word-arithmetic helpers** cited inline:
  `read_varint'_chain{,_transfer}`, `read_varint'_{succeeds,reaches_*}`,
  `varint_decode_{loop_suffix,suffix,drop_rest,fits,pos_le}`,
  `varint_{rest_lt_2p32,next_position,pos_unat,chain_drop}`,
  `rest_len_le`, `word_eq_sub_of_nat`, `unat_same_slot_word`,
  `same_slot_bound`, `unat_{x_plus_1,add_no_overflow}`, etc.

* **2 pure-spec bridge lemmas** used in postcondition discharge:
  `parse_header_no_app`, `parse_window_no_source`.

* **~14 legacy error-case lemmas** (`vcdiff_decode'_{short,magic*,hdr,
  appheader,win_*}_*`) — probably dead weight under the monolith
  `runs_to_vcg` but harmless. Revisit in Step 5.

* **~10 lemmas that propped up the broken proof**
  (`inst_end_le_patch_len{,2,3}`, `inst_end_le_word`,
  `word_le_of_unat_le`, `pos_chain_le`,
  `runs_to_whileLoop_bind_drop6th{,'}`, `summand_le_from_sub_eq`,
  `inst_end_from_sizes{,'}`, `vcdiff_decode'_prefix_correct` itself) —
  unreferenced by the new plan. Delete in Step 5 after confirming no
  residual use.

**~88 lemmas actively reused.** The sunk work in the substantive
invariant/address-cache/code-table/instruction-loop infrastructure is
intact; only the top-level glue was wrong.

## Plan

### Step 0 — unblock the build ✅ (committed)

Replaced `vcdiff_decode'_prefix_correct`'s body with `sorry`.
`isabelle build CdeltaRefine` now completes in ~20s.

### Step 1 — state the target theorem ✅ (committed)

`vcdiff_decode'_spec` stated as sorry at the end of
`VcdiffDec_Refine.thy` with the real `decode_spec` postcondition.

### Step 2 — smoke-test the supply pattern ✅ (completed, not committed)

Re-proved the existing `vcdiff_decode'_win_ind_len5_nonok_built` with
`supply near/same_init_preserves_patch_heap [runs_to_vcg]; apply
runs_to_vcg`. Findings:

* `runs_to_vcg` ran in 30s (did not hang), and the init-loop steps
  were consumed automatically by the supplied triples. The supply
  pattern genuinely works and does not blow up the way the old
  `runs_to_weaken`-peel pattern did.
* Did **not close** the full lemma because the smoke test inherited
  its too-weak postcondition `r ≠ Result 0`; VCG propagated it as
  `∀v. r = Result v ⟶ v ≠ 0 ∧ …` which is unprovable without stronger
  constraint. **Lesson: VCG needs a semantic postcondition to guide
  decomposition.** Our real target theorem has one (`decode_spec =
  Inl tgt ⇒ r = Result 0`) so this is not a blocker — it's evidence
  the weak intermediate postconditions of the old proof were doubly
  wrong.
* **Key structural finding**: `decode_loop_inv_after_{add,run,copy}`
  are **not** Hoare triples. They're meta-level state-to-state
  implications ("inv at t + add_loop produced these changes ⇒ inv at
  t′"). They cannot be supplied as `[runs_to_vcg]` rules.

**Revised expectation for Step 3.** The outer-loop body subgoal is
**not** a single `runs_to_vcg` blast. It's:

```
subgoal                              ← body preserves I
  apply (rule runs_to_bind) ...      ← or: runs_to_vcg with
                                          add_loop_correct supplied
  …                                   ← monadic step discharged
  apply (rule decode_loop_inv_after_add)
   apply assumption                   ← inv at t
  …                                   ← side conditions from
                                          exec_half_add_conditions +
                                          inv_* lemmas
  done
```

The monadic step (add/run/copy_loop) is VCG-supplied; the invariant
preservation is a *manual rule application* in the resulting residual
subgoal. This matches l4v's `ctac` + subsequent `apply rule` pattern.

### Step 3 — prove the outer whileLoop inline (not as a separate lemma)

**Design change** (after inspecting the lifted `vcdiff_decode'_def`
dumped to `planning/vcdiff_decode_lifted.txt` and AutoCorres2's
`IsPrime_Ex.is_prime_faster_correct`): do **not** extract
`decode_window_loop_correct` as a standalone lemma.

Rationale: the outer whileLoop body is not a named constant. Stating
a standalone triple over it requires transcribing the ~80-line body
as a lambda in the lemma statement, which couples the proof to the
exact shape AutoCorres2 emits — any change to `vcdiff_dec.c` breaks
the statement. AutoCorres2's idiom (per `IsPrime_Ex`) is to apply
`runs_to_whileLoop_exn [where I = …, R = …]` *inline* as one of the
residual subgoals after the top-level `runs_to_vcg`, with
`decode_loop_inv` as the invariant. No separate lemma.

Proof plan for the inline outer-loop subgoal (one of the residual
subgoals of `vcdiff_decode'_spec`):

```
subgoal                                   ← outer while-loop obligation
  apply (rule runs_to_whileLoop_exn
    [where I = "λr t'. case r of
                 Exn _ ⇒ True
               | Result (ac, dc, ic, np, tp) ⇒
                   decode_loop_inv … dc ic ac tp np t' ∧
                   (∃dst. decode_loop (measure0 - unat (ic - inst_cursor_0))
                             src_seg (unat src_seg_len) tgt_len dst0
                           = Inl dst ∧
                          ds_tgt dst = heap_bytes t' out (unat tp))"
       and R = "measure (λ((_, _, ic, _, _), _). unat inst_end - unat ic)"])
  subgoal …      (wf, trivial)
  subgoal …      (init from decode_loop_inv_init)
  subgoal …      (exit ⇒ post: inst_cursor = inst_end + ds_tgt correspondence)
  subgoal …      (Exn vacuous)
  subgoal                                 ← body preserves I
    supply read_byte'_spec       [runs_to_vcg]
    supply read_varint'_spec     [runs_to_vcg]
    supply decode_address'_spec  [runs_to_vcg]
    supply add_loop_correct      [runs_to_vcg]
    supply run_loop_correct      [runs_to_vcg]
    supply copy_loop_correct     [runs_to_vcg]
    supply if_split [split del]
    apply runs_to_vcg
    …
    (* Residual subgoals: invariant preservation — discharged via
       decode_loop_inv_after_{add,run,copy} + decode_loop_inv_advance_inst
       + exec_half_*_conditions + inv_* numeric bridges. *)
    apply (rule decode_loop_inv_after_add) …
    …
    done
  done
```

The inner `which < 2` loop is handled by `runs_to_whileLoop_exn`
again (invariant: 0..2 counter, state evolves per half-instruction)
or by `whileLoop_unroll` if that's simpler. Decide during proof
based on what VCG leaves behind.

### Step 4 — monolithic `vcdiff_decode'_spec` proof

Since Step 3 no longer extracts a separate loop lemma, Steps 3 and 4
become one proof.  Overall shape:

```
theorem vcdiff_decode'_spec:
  …
  unfolding vcdiff_decode'_def
  supply read_byte'_spec                  [runs_to_vcg]
  supply read_varint'_spec                [runs_to_vcg]
  supply near_init_preserves_patch_heap   [runs_to_vcg]
  supply same_init_preserves_patch_heap   [runs_to_vcg]
  supply build_code_table'_spec           [runs_to_vcg]
  supply if_split [split del]
  apply runs_to_vcg
  subgoal … (magic-byte failure paths)
  subgoal … (header indicator)
  subgoal … (win_ind checks)
  subgoal … (section bounds + establish decode_loop_inv at entry)
  subgoal                                  ← the outer whileLoop
    apply (rule runs_to_whileLoop_exn [where I = decode_loop_inv … and R = …])
    subgoal … subgoal … subgoal …
    subgoal                                ← body preserves I
      supply add_loop_correct  [runs_to_vcg]
      supply run_loop_correct  [runs_to_vcg]
      supply copy_loop_correct [runs_to_vcg]
      supply decode_address'_spec [runs_to_vcg]
      apply runs_to_vcg
      …
      apply (rule decode_loop_inv_after_add) …
      done
    done
  subgoal … (post-loop cursor checks + final write + decode_spec = Inl tgt)
  subgoal … (Inr case discharges)
  done
```

Case-split on the value of `decode_spec patch src` at the top level
(via `case_tac` or by unfolding `decode_spec` + `parse_header` +
`parse_window` with `parse_header_no_app` / `parse_window_no_source`)
so each subgoal sees either `Inl tgt` or `Inr e` and discharges
accordingly.

**Size expectation.**  AutoCorres2 monolith proofs of comparable C
functions (e.g. `is_prime_faster_correct`) close in <50 lines when
the whileLoop has a well-chosen invariant.  `vcdiff_decode'` is
bigger (more sequential steps, more branches, a deeper loop nest)
but the invariant `decode_loop_inv` is already fully designed; much
of the work is discharging residual arithmetic/bounds subgoals.
Target: <500 lines of Isar total for the final `vcdiff_decode'_spec`.
If it trends significantly over, pause and reassess which side
lemmas are missing.

### Step 5 — cleanup

* Delete Group-H lemmas once confirmed unused:
  `inst_end_le_patch_len{,2,3}`, `inst_end_le_word`,
  `word_le_of_unat_le`, `pos_chain_le`,
  `runs_to_whileLoop_bind_drop6th{,'}`, `summand_le_from_sub_eq`,
  `inst_end_from_sizes{,'}`, `vcdiff_decode'_prefix_correct`.
* Reassess the ~14 legacy error-case lemmas; delete any that are
  fully subsumed by the monolith.
* Turn off `quick_and_dirty` in ROOT for `CdeltaRefine`.
* Full clean build, zero sorry / zero oops.
* Discharge the 3 remaining sorries in `build_code_table'_spec`
  (out-of-scope for the decode proof itself; separate milestone).

## Anti-patterns (do not repeat)

Concrete things that caused the old blow-up. Stop and ask if any of
these start appearing again:

1. **Manual `apply (rule runs_to_weaken[OF leaf_spec])` peel chains.**
   Use `supply leaf_spec [runs_to_vcg]` instead. Every manual
   `runs_to_weaken` inflates the next goal with a meta-implication.
2. **`apply (all \<open>… ; fail)?\<close>` chains more than 3 in a row.**
   If you need more, the supplied rule set is wrong — find the
   missing leaf spec or the mis-shaped invariant rather than
   brute-forcing decomposition.
3. **Intermediate postconditions of shape `∃ret. r = Result ret`.**
   Any reusable lemma needs a postcondition that names the semantic
   effect. (Exception: the legacy failure-case lemmas already in the
   file are fine — they're closed and we don't extend them.)
4. **Bespoke loop invariants duplicating a subset of
   `decode_loop_inv`.** Use `decode_loop_inv` directly. Otherwise the
   `_after_{add,run,copy}` preservation lemmas don't apply.
5. **`unfolding vcdiff_decode'_def` inside any sub-lemma.** Only the
   top-level `vcdiff_decode'_spec` unfolds it. Sub-lemmas work at the
   whileLoop / inner-loop level.
6. **Calling `runs_to_vcg` on a goal the user doesn't understand the
   structure of.** Before each `runs_to_vcg`, be able to predict the
   number and shape of subgoals it should produce. If it produces
   something surprising, stop and inspect — don't fire a second
   `runs_to_vcg` in hope.

## Build workflow

```
isabelle build -d . -o system_log=true -v CdeltaRefine \
  > .build-tmp/build.log 2>&1
```

Foreground only. The `system_log=true -v` flags surface timing lines
that indicate a stuck command (this is how the old proof's blow-up
was detected — running > 5 minutes on one tactic).
