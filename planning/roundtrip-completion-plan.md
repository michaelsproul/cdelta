# Roundtrip completion plan (2026-07-06)

## Progress log

**2026-07-06 (session 2).** **Work item 2 DONE**:
`encode_window_try_fused_copy_step_topdown_budget` is proved (sorry count
9 → 8). All in `VcdiffEnc_Serialize.thy`, full session rebuilt clean (~5.5min):

- Generalized `emit_copy'_state_rel_cache_frame_from_loop`: dropped the
  `copy_ge` premise; inner case split is now `4 ≤ copy_len ∧ copy_len ≤ 18`,
  so 1–3-byte remainder copies route to the large/varint leaf lemmas (which
  only need the negation). Needed because the fused branch emits a remainder
  of `m.len − 6 ∈ {1,2,3}` when `m.len ∈ {7,8,9}`.
- New `try_emit_add_copy'_mode_le5_success_heap_bytes2_cache_frame`
  (src/tgt frame + cache for the mode≤5 fused path, varint address write) —
  mirrors the gt5 one at ~4919.
- New keystone `try_emit_add_copy'_state_rel_cache_frame_from_loop`:
  loop-context packaging of the fused emit. Given budget-rel ingredients +
  spec-side `try_emit_add_copy_spec … = Some spec_st'` + section room from
  `length (enc_* spec_st') ≤ caps`, concludes Result f with
  `unat (fused_C f) = enc_tp spec_st' − enc_tp spec_st`, err OK,
  `state_rel t (s_C f) spec_st'`, cache_abs of `enc_cache spec_st'`,
  src/tgt frame, typing. Dispatches {mode≤5, mode>5} × {state_rel, cache,
  emitted_sections (for err/pos), frame} via runs_to_conj; all disjointness
  from `encode_window_loop_buffers_ok`.
- Pure helpers: `try_emit_add_copy_spec_Some_shape` (pending'=[], flushed
  invariant, data/inst length deltas), `try_emit_add_copy_spec_Some_partial_six`
  (partial fuse ⟹ consumed = 6, hence remainder ⟹ m.len ≥ 7 — this closes
  the inst linear-slack arithmetic), `emit_copy_spec_components`/`_cache_of_
  encode_address`/`_inst_growth` (≤ +6), `encode_window_loop_buffers_ok_heap_typing`
  (buffers_ok transports along heap_typing equality).
- The budget lemma itself: try_emit keystone → (if `fused_C f < m.len`)
  emit_copy' keystone at intermediate state (spec_st'' = `emit_copy_spec` of
  the remainder) → re-establish budget_rel. Budget via
  `encode_window_section_budget_match_step` with `spec_st'' =
  encode_window_full_step` (match_rel bridge gives `em_pos/em_len ?best =
  unat m.pos/m.len` via find_best_match_spec_sound + of_nat/unat).
  Addr room comes purely from the semantic budget (spec_st' ≤ spec_st'' ≤
  final ≤ caps); data/inst linear slacks re-proved from spec section lengths.

Proof-plumbing notes (reusable for item 1, flush_then_copy at 12851):
- `runs_to_liftE` must be applied to a liftE goal (rule), then weaken —
  it does NOT compose via OF.
- After `simp add: <branch booleans>`, nested do-blocks need `runs_to_bind`
  applied once per bind layer before weakening with the C-call lemma; the
  trailing pure control flow closes with
  `(auto simp: runs_to_bind_iff runs_to_condition_iff)`.
- `[of …]` instantiation order for locally-proved ⋀-facts follows first
  occurrence in the proposition, not binder order.
- Beware `simp` loops from `cn_def`+`tp'_eq` style circular rewrites — use
  linarith on the raw facts instead.

**Next: work item 1** — `encode_window_flush_then_copy_step_topdown_budget`
(now at 12851). The framed-flush helper described below is still the blocker;
the emit_copy' keystone + budget re-establishment pattern from this session
carries over directly (the None-branch: `try_emit_add_copy'_spec_none_noop` →
conditional `flush_pending'` (framed) → emit_copy' keystone → budget via the
same match-step lemma with `spec_st'' = flush_then_emit_copy_spec …`).

**2026-07-06 (session 1).** Confirmed the diagnosis below by building. Committed,
all in `proof/encoder-correctness/VcdiffEnc_Serialize.thy`, verified with
`quick_and_dirty` (session still has the pre-existing 9 sorries):

- `5942d88` — pure budget-step infrastructure + reusable flush helper:
  - `emit_inst_spec_sections_mono`, `flush_pending_spec_sections_mono`,
    `emit_copy_spec_sections_mono`, `flush_then_emit_copy_spec_sections_mono`
    (section-length monotonicity of the spec steps).
  - `encode_window_full_step_match_tp_le` (match step keeps `tp ≤ length tgt`,
    from `find_best_match_spec_sound`, no trace_inv needed).
  - `encode_window_full_loop_fuel_stable` (loop result independent of fuel once
    fuel > remaining) and `encode_window_full_loop_sections_mono`.
  - **`encode_window_section_budget_match_step`** — the KEY pure lemma: a
    match-branch spec step preserves `reaches_final` + section prefix budget.
    (Pending-byte analogue `encode_window_section_budget_buffer_pending_byte`
    already existed.)
  - **`flush_pending'_loop_from_final_fits`** + `encode_window_loop_buffers_ok_pending_ptr_valid`
    — reusable C flush lemma: discharges the flush_pending' branch emit_pre from
    "final section lengths + 64 ≤ caps" (data/inst) / "≤ cap" (addr). Lifted from
    the proved `encode_window_final_flush_topdown`. Used by BOTH flush-then-copy
    and final-flush-budget.
- `363bda2` — `try_emit_add_copy'_spec_none_noop`: spec None ⟹ C `try_emit_add_copy'`
  is a noop (fused=0, unchanged sections). Case split on pend_len/mode dispatching
  to the existing noop lemmas; spec success lemmas rule out the rest.

Scratch session for fast iteration: `.build-tmp/scratch/{ROOT,Scratch.thy}`,
build with `isabelle build -d . -d .build-tmp/scratch CdeltaScratch` (~12s once the
CdeltaEncoderCorrectness heap is warm; a full session rebuild is ~5.5–9min).

**2026-07-06 (session 1, cont.).** Committed `4932cdb`:
`emit_copy'_state_rel_cache_frame_from_loop` — the emit_copy' loop-context
keystone (reused by flush_then_copy AND try_fused). Produces enc_sections_state_rel
(exact emit_copy_spec), updated cache, and src/tgt frame, using EXACT section room
(budget grants no addr headroom), across all 4 {small,large}×{addr byte,varint}
cases, conjoining per-case state_rel + cache_abs + heap_bytes2_frame via
runs_to_conj. Disjointness premises discharged once as conditional facts (ibp,
avv, avid, siv, …) from encode_window_loop_buffers_ok.

**Next blocker for flush_then_copy:** the budget_rel result needs
`heap_bytes t src = src_bytes` (and tgt), which must survive the FLUSH. The
emit-chunk lemmas (`emit_pending_add/run_chunk_from_loop_buffers`) frame only the
`pending` buffer, not src/tgt. Fix: a FRAMED flush helper — extend
`flush_pending'_loop_from_final_fits` to also conclude
`heap_bytes_word t src 0 src_len = heap_bytes_word s src 0 src_len` (and tgt), via
`flush_pending'_enc_sections_state_rel_branch_pre_frame` (VcdiffEnc_Emit 15251)
with `P = src/tgt frame`, discharging run_pre/tail_pre's P by conjoining
`emit_add'_loop_buffers_heap_word_cache_frame` / `emit_run'_..._frame`
(Serialize 3334/3511, which frame arbitrary out-buffers disjoint from data/inst,
out1=src out2=tgt). Convert heap_bytes_word↔heap_bytes via `heap_bytes_word_zero`
(Writers 1422). This framed flush also unblocks final_flush_budget (task 4).

**Remaining for sorry #1 (flush_then_copy_budget), still open:** the C-side
assembly. Needs an `emit_copy'` loop-context helper giving
`enc_sections_state_rel u … (emit_copy_spec …)` — dispatches to the four
`emit_copy'_{small,large}_addr_{byte,varint}_success_enc_sections_state_rel`
lemmas (VcdiffEnc_Emit ~8268), each with ~25 disjointness/validity premises
discharged from `encode_window_loop_buffers_ok` + inst_pos+6/addr_pos+5 room
(same discharge pattern as the fused proof's `loop_frame_facts`, ~6390–6733).
Then assemble the branch: `try_noop` → (skip fused branch) → conditional
`flush_pending'_loop_from_final_fits` → `emit_copy'` helper → re-establish
`encode_window_loop_budget_rel` with `spec_st' = flush_then_emit_copy_spec …`
(= the full step; budget via `encode_window_section_budget_match_step`).
The flush room facts come from the budget_rel linear data/inst slack
(`data_pos + pend_len + (tgt_len−tp) + 64 ≤ data_cap`) + `flush_pending_loop_spec_growth`;
addr room is just `addr_pos ≤ addr_cap` (flush doesn't touch addr).

---


Status assessment and the concrete path to a sorry-free
`vcdiff_encode'_then_decode_roundtrip_topdown` (C encoder → C decoder roundtrip).

## Where we actually are

All 9 remaining `sorry`s live in `proof/encoder-correctness/VcdiffEnc_Serialize.thy`.
Everything else (decoder refinement, spec roundtrip, C-roundtrip glue in
`proof/c-roundtrip/VcdiffC_Roundtrip.thy`) is sorry-free and already wired:
the final theorem rests solely on `enc.vcdiff_encode'_writes_encode_spec_topdown`.

There are currently **two parallel lemma towers** for the encode-window phase:

| non-budget tower (old) | budget tower (new) | status |
|---|---|---|
| `encode_window_pending_byte_step_topdown` | `..._budget` (8714) | both proved |
| `encode_window_try_fused_copy_step_topdown` (6049, proved) | `..._budget` (8971) | **budget sorried** |
| `encode_window_flush_then_copy_step_topdown` (8309, **sorried**) | `..._budget` (9007) | **both sorried** |
| `encode_window_match_step_topdown` / `loop_body` | `..._budget` (9043/9121) | proved (modulo above) |
| `encode_window_while_loop_topdown` (9370, **sorried** at 9443) | `..._budget` (9259) | **both sorried** |
| `encode_window_final_flush_topdown` (9446, proved) | `..._budget` (9300) | **budget sorried** |
| `encode_window_phase_core_topdown` (10286, proved) | `..._budget` (9340) | **budget sorried** |
| `vcdiff_encode'_encode_window_phase_topdown` (10448, proved) | `..._budget` (10510) | **budget sorried** |
| `vcdiff_encode'_writes_encode_spec_topdown` (11245, proved) | `..._budget` (11364) | **budget sorried** |

## The key fact driving everything

The old loop invariant `encode_window_loop_rel` carries a *linear* capacity bound
per section:

    pos + pend_len + (tgt_len - tp) + 64 <= cap

**This is not inductive for the addr section.** A plain COPY advances `tp` by
`match_len >= MIN_MATCH = 4` but can write a 5-byte address varint (addresses go
up to `src_len + tp < 2^32`). Net budget change +1 per iteration. (The fused
ADD+COPY branch happens to be fine — `tp` advances by `add_sz + len >= 5` — which
is exactly why `try_fused_copy_step_topdown` got proved and
`flush_then_copy_step_topdown` got stuck.)

Worse, this is not just a weak invariant — **the non-budget top-level theorem is
false as stated**. Its only capacity assumption is `encoder_buffers_ok`, i.e.
`tgt_len + 64 <= addr_cap`. An adversarial input (≥256 MiB, tiled 4-byte matches
with cache-missing ≥2^28 addresses) makes the final addr section ≈ 1.25×tgt_len,
so the C encoder legitimately returns ENC_OVERFLOW and the unconditional success
postcondition fails. `sections_fit_32` doesn't save it (it only bounds sections by
2^32). Consequently the two theorems in `VcdiffC_Roundtrip.thy` are also false as
currently stated, despite being locally sorry-free.

**Conclusion: do NOT try to prove sorries 8343 and 9443. They are unprovable.**

The `_budget` tower is the correct fix: replace the addr linear bound with a
semantic budget (`encode_window_loop_budget_rel`):

- `encode_window_spec_reaches_final`: running the pure loop from the current
  spec state reaches `encode_window_final_spec_state` (gives monotone growth
  toward known final sections);
- `encode_window_section_prefix_budget`: current section lengths ≤ final lengths;
- `encoder_final_section_caps_ok`: final spec section lengths ≤ the C caps —
  a **new top-level assumption** that must be threaded up to the C-roundtrip
  theorems. It cannot be derived from `encoder_buffers_ok` (see above).

`encode_window_initial_loop_budget_rel` (5763) is already proved, so initial
establishment is done.

## Decisions

1. **Single invariant**: the budget tower is the only path forward. The
   non-budget step/loop lemmas that are false (`flush_then_copy_step_topdown`
   8309, `while_loop_topdown` 9370) get **deleted**, not proved. Once the budget
   tower is complete, delete the rest of the redundant non-budget tower
   (`match_step`, `loop_body`, `phase_core`, `encode_window_phase`,
   `writes_encode_spec` non-budget versions) and rename the `_budget` lemmas to
   the plain names, so `VcdiffC_Roundtrip.thy` churn is minimal.
2. **Thread `final_caps` up**: add
   `encoder_final_section_caps_ok src_bytes tgt_bytes data_cap inst_cap addr_cap`
   as an assumption of `vcdiff_encode'_writes_encode_spec_topdown` (post-rename),
   `vcdiff_encode'_writes_encode_spec_roundtrip_context`, and
   `vcdiff_encode'_then_decode_roundtrip_topdown`. The decoder-side theorem
   (`vcdiff_encoded_patch_decodes_to_target_topdown`) does not need it.
3. Keep the retained linear data/inst terms in `encode_window_loop_budget_rel`
   for now (they *are* inductive — flushes are self-funded by the released
   `pend_len` term — and they let the existing data/inst capacity discharges be
   reused). Optional cleanup later: derive them from the semantic budget instead.

## Work items, in order

Ordered hardest-first to de-risk; each item ends with `VcdiffEnc_Serialize.thy`
still elaborating (keep the remaining sorries in place until their turn).

### 1. `encode_window_flush_then_copy_step_topdown_budget` (9007) — the hard core
The only genuinely *new* proof left. Structure:
- Flush pending: use the existing flush-pending machinery
  (`flush_pending'_enc_sections_state_rel_topdown`, see
  `planning/flush-pending-loop-spec.md`); discharge its `emit_pre`
  (section-cursor capacity etc.) from the budget invariant rather than the dead
  linear addr bound.
- Emit COPY: reuse the leaf emit/address/opcode lemmas already proved for the
  fused branch (VcdiffEnc_Emit / VcdiffEnc_Writers) — the addr-capacity
  obligation (`addr_pos + this_step_addr_bytes <= addr_cap`) comes from the
  semantic budget: post-step state still reaches final, so post-step
  `addr` length ≤ final length ≤ `addr_cap`.
- Budget preservation: mirror the pattern of the proved
  `encode_window_section_budget_buffer_pending_byte` (8634): a pure lemma that
  the flush-then-copy spec step preserves `reaches_final` (fuel/determinism
  argument on `encode_window_full_loop`) + prefix budget.

### 2. `encode_window_try_fused_copy_step_topdown_budget` (8971)
Port of the proved non-budget lemma (6049). The C-side reasoning is identical;
only the capacity discharges change (budget instead of the linear addr term) and
budget preservation is appended (same pure pattern as item 1). Mechanical but
long — resist re-deriving anything the 6049 proof already establishes; lift its
`have` blocks wholesale.

### 3. `encode_window_while_loop_topdown_budget` (9259)
Standard `runs_to` whileLoop induction, measure `unat tgt_len - unat tp` (already
the measure in the proved `loop_body_topdown_budget`). Obligations:
- Invariant: ∃spec_st. budget_rel ∧ match_rel preserved (heap typing on
  src/index arrays unchanged by loop body) ∧ loop_buffers_ok preserved.
- `∃m. find_best_match' … = Some m`: from `find_best_match'_eq_find_best_match_spec`
  (VcdiffEnc_Match 6387) via the index post.
- `pend_len < pending_cap` before each body run: from
  `pend_len <= tp < tgt_len <= pending_cap`.
- Exit: at `tp = tgt_len`, need
  `flush_pending_spec … spec_st = encode_window_final_spec_state …` — small pure
  lemma: unfold `reaches_final` with remaining fuel 1.

### 4. `encode_window_final_flush_topdown_budget` (9300)
Adapt the proved `encode_window_final_flush_topdown` (9446, ~840 lines). Final
flush touches only data + inst, whose linear terms were retained in budget_rel,
so the existing proof body should replay nearly verbatim; check whether it ever
uses the addr linear term (it shouldn't) and drop that dependence.

### 5. Glue: 9340, 10510, 11364
`phase_core_topdown_budget`, `vcdiff_encode'_encode_window_phase_topdown_budget`,
`vcdiff_encode'_writes_encode_spec_topdown_budget` — each mirrors an
already-proved non-budget twin (10286, 10448, 11245); initial budget comes from
`encode_window_initial_loop_budget_rel` + the `final_caps` assumption.

### 6. Rewire and delete
- Rename `_budget` top theorem to `vcdiff_encode'_writes_encode_spec_topdown`
  (with `final_caps` assumption); delete the false non-budget tower
  (8309, and the chain 8345→11245 non-budget versions).
- Add `final_caps` to the two encoder-facing lemmas/theorems in
  `VcdiffC_Roundtrip.thy`.
- Sanity check: confirm the harness / callers allocate section buffers large
  enough that `final_caps` holds on the benchmark corpus (it's an assumption,
  not proved — but it should at least be *true* for real runs; if the harness
  allocates only `tgt_len + 64`, note that adversarial inputs exist where the
  encoder correctly reports overflow, which the theorem simply doesn't cover).

### 7. Acceptance gates
- `isabelle build -d . -o system_log=true -v CdeltaCRoundtrip` (log to file).
- `rg "^\s*(sorry|oops)" proof spec` → empty.
- Flip `quick_and_dirty = false` in ROOT for CdeltaEncoderCorrectness,
  CdeltaSpecRoundtrip, CdeltaRefine, CdeltaCRoundtrip; full rebuild of
  `CdeltaCRoundtrip`. This is the real "done" signal — until then sorried lemmas
  pass silently.
- Update `planning/encoder-correctness.md` with the budget-invariant rationale
  (currently undocumented anywhere).

## Guardrails (rabbit-hole avoidance)

- Do **not** attempt sorries 8343 / 9443 — delete them (they are false; see key
  fact above). Any effort there is wasted.
- Do not strengthen `encoder_buffers_ok` to imply `final_caps` — it can't
  without grossly over-allocating (addr worst case ~1.25×tgt_len); keep
  `final_caps` an explicit semantic assumption.
- Do not touch the decoder side, Spec_Roundtrip, or the pure spec layer except
  to add the small pure budget-preservation lemmas of items 1–3.
- Per the long-standing guardrail: semantic facts belong in pure bridge lemmas,
  not in the C loop invariant; the budget invariant already respects this
  (`reaches_final` is a pure statement about `spec_st`).
- No new one-off length special cases; if a capacity subgoal doesn't fall out of
  the semantic budget, the budget lemma is missing a pure corollary — add it
  there.
