# Refinement Layer Progress

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

### Step 3 — prove `decode_window_loop_correct`

Standalone lemma with postcondition in terms of `decode_loop_inv` at
exit + `ds_tgt`-matches-decoded-bytes:

```
lemma decode_window_loop_correct:
  assumes decode_loop_inv s0 patch patch_n src src_n out
                          src_seg_off src_seg_len tgt_len
                          data_end inst_end addr_end src_seg
                          data_cursor inst_cursor addr_cursor 0 0 t
      and [numeric bounds]
  shows "whileLoop C B (addr_cursor, data_cursor, inst_cursor, 0, 0) ∙ t
           ⦃ λr t'.
              case r of
                Result (ac, dc, ic, np, tp) ⇒
                  decode_loop_inv … ac dc ic np tp t' ∧
                  ¬ ic < inst_end ∧
                  [ds_tgt from final inv] = [decode_window-derived tgt]
              | Exn _ ⇒ False ⦄"
```

Proof: `runs_to_whileLoop_exn` with `decode_loop_inv` as the invariant
and `unat inst_end - unat inst_cursor` as the measure. Five subgoals:

1. wf — trivial.
2. init — from hypothesis.
3. `¬C ∧ I ⇒ Q` — ds_tgt correspondence at exit.
4. Exn — vacuous (body doesn't throw in the success path).
5. Body preserves I — `runs_to_vcg` with the Group-A inner-loop specs
   + Group-B `decode_loop_inv_after_{add,run,copy}`,
   `decode_loop_inv_advance_inst{,_n}`,
   `exec_half_{add,run,copy}_conditions`, and the code_tbl /
   byte_to_hi bridge lemmas all supplied.

The inner `for (which=0; which<2)` loop unrolls to two sequential
half-instruction dispatches via `whileLoop_unroll` or a dedicated
`runs_to_whileLoop_{res,exn}_bounded` helper. Check AutoCorres2 for a
pre-existing rule before writing our own.

### Step 4 — compose `vcdiff_decode'_spec`

Monolithic proof:

```
theorem vcdiff_decode'_spec:
  …
  unfolding vcdiff_decode'_def
  supply read_byte'_spec [runs_to_vcg]
  supply read_varint'_spec [runs_to_vcg]
  supply near_init_preserves_patch_heap [runs_to_vcg]
  supply same_init_preserves_patch_heap [runs_to_vcg]
  supply build_code_table'_spec [runs_to_vcg]
  supply decode_window_loop_correct [runs_to_vcg]
  supply if_split [split del]
  apply runs_to_vcg
  subgoal … (magic-byte failure paths)
  subgoal … (header indicator)
  subgoal … (win_ind checks)
  subgoal … (section bounds + decode_loop_inv at entry)
  subgoal … (post-loop cursor checks + final write + decode_spec = Inl tgt)
  subgoal … (Inr case discharges)
  done
```

Case-split on the value of `decode_spec patch src` at the top level
(via `case_tac` or by unfolding `decode_spec` + `parse_header` +
`parse_window` with `parse_header_no_app` / `parse_window_no_source`)
so that each subgoal sees either `Inl tgt` or `Inr e` and discharges
accordingly.

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
