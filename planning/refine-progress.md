# Refinement Layer Progress

## Status (2026-05-06)

Phase B Step 2 (decoder refinement). Leaf helpers, error-case lemmas, and
instruction loop lemmas (ADD, RUN) are proved. COPY loop (overlapping copy)
and prefix refinement remain.

## Completed (current theory state)

In [proof/decoder-refine/VcdiffDec_Refine.thy](../proof/decoder-refine/VcdiffDec_Refine.thy):

* `read_byte'_spec` and `read_byte'_list_spec` — proved.
* `read_varint'_spec` — proved (line 337, full functional correctness).
* `decode_address'_spec` — proved (line 975, all four address modes, sorry-free).
* `build_code_table'_spec` — proved (line 1789, 6 nested loops, table-match
  invariant, postcondition `code_tbl_built_'' s' = 1`).
* ~30 error-case lemmas for `vcdiff_decode'` (short patch, magic bytes, hdr
  indicator, window indicator, app-header skip, cache-init paths).
* Cache-init loop preservation lemmas (`near_init_loop_res_w32_ptr`,
  `same_init_loop_res_w32_ptr`).
* Phase 1 infrastructure: `bufs_disjoint`, `heap_bytes_update_disjoint`,
  `heap_bytes_update_outside`, `buf_valid_heap_w8_update_any`,
  `heap_w32_heap_w8_update`, `ptr_valid_heap_w8_update`, `heap_bytes_extend`.
* Varint chaining: `varint_decode_loop_suffix`, `varint_decode_suffix`,
  `varint_decode_drop_rest`, `varint_next_position`, `init_loops_preserve_patch`.
* Pointer injectivity: `ptr_add_inject`, `ptr_add_inject_nat`.
* `parse_header_no_app` — proved (header parse correspondence).
* `parse_window_no_source` — proved (window parse correspondence).
* **`add_loop_correct`** — proved (ADD instruction inner loop, sorry-free).
* **`run_loop_correct`** — proved (RUN instruction inner loop, sorry-free).
* `copy_loop_prefix`, `copy_loop_nth` — proved (helper lemmas for COPY).

Build status: **clean** (`isabelle build -d . -v -o system_log=true CdeltaRefine`).

## Goal

```
theorem vcdiff_decode'_spec:
  assumes [full preconditions]
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len . s
    { \<lambda>r t. case decode_spec (heap_bytes s patch (unat patch_len))
                             (heap_bytes s src (unat src_len)) of
        Inl tgt => r = Result VCD_OK \<and>
                   heap_bytes t out (length tgt) = tgt \<and>
                   heap_w32 t out_len = of_nat (length tgt)
      | Inr _ => r \<noteq> Result VCD_OK }"
```

## Plan

### Phase 1 — Output-write infrastructure (1-2 days)

The C decoder reads from `patch`/`src` and writes to `out`. Every byte write to
`out` must not invalidate what we know about `patch`/`src`.

**1a. Disjointness predicate:**

```
definition bufs_disjoint :: "8 word ptr => nat => 8 word ptr => nat => bool" where
  "bufs_disjoint p pn q qn =
     (\<forall>i < pn. \<forall>j < qn. p +p int i \<noteq> q +p int j)"
```

**1b. Preservation lemmas for `heap_w8_update`:**

- `heap_bytes_heap_w8_update_disjoint`: reading `heap_bytes s patch n` is
  unchanged after writing to a pointer in the `out` region (given disjointness).
- `buf_valid_heap_w8_update`: writing to `out` preserves `buf_valid` for
  `patch`/`src`.
- `heap_w32_heap_w8_update`: writing a byte doesn't affect `heap_w32` of
  `out_len` (type separation).

**1c. Output-region lemmas:**

- Writing `out[tgt_pos + j] = v` extends `heap_bytes t out (tgt_pos + j + 1)`
  by one byte.
- Inductive output-write invariant for the ADD/RUN/COPY inner `for` loops.

### Phase 2 — Header + window parse refinement (3-5 days)

Factor the linear prefix of `vcdiff_decode'` (everything before
`while (inst_cursor < inst_end)`) into a standalone lemma:

```
lemma vcdiff_decode'_prefix_refine:
  assumes [buf_valid, ptr_valid, disjoint, well-formed patch]
  shows "\<exists>t' data_cursor inst_cursor addr_cursor ...
    [C execution reaches the main loop in state t'] \<and>
    parse_header (heap_bytes s patch (unat patch_len)) = Inl rest \<and>
    parse_window rest = Inl (win, tail) \<and>
    data_cursor = ... \<and> inst_cursor = ... \<and> addr_cursor = ... \<and>
    [cache zero-initialized] \<and> [code_tbl_built = 1]"
```

**Sub-lemmas (each ~30-50 lines, mechanical VCG):**

| Lemma | C code section | Spec counterpart |
|-------|---------------|-----------------|
| `header_magic_refine` | `patch[0..3]` checks + `hi` byte | `parse_header` magic + hdr_indicator |
| `app_header_skip_refine` | Optional varint + skip | `parse_header` app-data branch |
| `window_meta_refine` | `win_ind`, src_seg varints, `dlen`, `tgt_len`, `di`, section lengths | `parse_window` |
| `section_cursors_refine` | Arithmetic: `data_pos`, `inst_pos`, `addr_pos` | Take/drop offsets into `pw_data`/`pw_inst`/`pw_addr` |

Each is a sequential chain of `read_varint'_spec` / `read_byte'_spec`
applications. Use `obtain`/`note` Isar style to name intermediate states.

### Phase 3 — Main decode loop invariant (7-10 days, critical path)

**3a. Define the loop invariant:**

```
definition decode_loop_inv where
  "decode_loop_inv s0 t patch src out
     data_end_n inst_end_n addr_end_n src_seg_len_n tgt_len_n
     data_cursor inst_cursor addr_cursor tgt_pos near_ptr
     dst \<equiv>
       ds_inst_rem dst = heap_bytes t patch [inst_cursor..inst_end] \<and>
       ds_data_rem dst = heap_bytes t patch [data_cursor..data_end] \<and>
       ds_addr_rem dst = heap_bytes t patch [addr_cursor..addr_end] \<and>
       ds_tgt dst = heap_bytes t out [0..tgt_pos] \<and>
       ds_cache dst = cache_from_arrays t near_ptr \<and>
       [buf_valid / ptr_valid preserved] \<and>
       [patch/src heap unchanged from s0] \<and>
       [cursor bounds: data_cursor \<le> data_end, etc.]"
```

**3b. Loop body — outer while:**

The C has `while (inst_cursor < inst_end)` wrapping `for (which=0; which<2)`.
Since the inner for-loop always executes exactly 2 iterations, **unroll it** to
two sequential half-instruction dispatches.

Each iteration:
1. `read_byte` to get opcode -> look up `code_tbl[op]`
2. First half-instruction dispatch (typ1/sz1/md1)
3. Second half-instruction dispatch (typ2/sz2/md2)

**3c. Three instruction branches (per half):**

| Branch | Key reasoning | Effort |
|--------|--------------|--------|
| **ADD** | `for j` byte-copy from data section to output. `heap_bytes` extension + disjointness. | 2-3 days |
| **RUN** | `for j` fill output with single byte. Simpler than ADD. | 1-2 days |
| **COPY** | Calls `decode_address'`, then `for j` with src-vs-output dispatch. Overlapping copy via `copy_loop`. **Hardest sub-lemma.** | 3-4 days |

**3d. COPY overlap invariant (hardest piece):**

The C does:
```c
for (j = 0; j < sz; j++) {
    a = addr + j;
    if (a < src_seg_len) byte = src[src_seg_off + a];
    else byte = out[a - src_seg_len];  // may read earlier output
    out[tgt_pos + j] = byte;
}
```

The spec: `copy_loop src_seg (ds_tgt st) addr sz`. Refinement needs induction:
```
\<forall>k < j.
  heap_w8 t (out +p (tgt_pos + k)) =
  copy_loop src_seg (ds_tgt st) addr sz ! k
```

Case split on `addr + k < src_seg_len` vs reading from output-so-far. Likely
~100 lines of Isar. May need an auxiliary `copy_loop_nth` lemma in the pure
spec layer.

**3e. Termination:**

Measure: `inst_end - inst_cursor` (strictly decreasing, each iteration advances
`inst_cursor` by at least 1 via `read_byte`).

### Phase 4 — Post-checks + composition (2-3 days)

**4a. Final consistency checks after loop exit:**

- `tgt_pos = tgt_len` <-> `length (ds_tgt final_st) = pw_tgt_len win`
- `data_cursor = data_end` <-> `ds_data_rem final_st = []`
- `addr_cursor = addr_end` <-> `ds_addr_rem final_st = []`

Follow directly from loop invariant cursor-bounds clauses.

**4b. Final write:** `*out_len = tgt_pos` (one `heap_w32_update`).

**4c. Composition:**

Combine Phase 2 (prefix reaches loop entry) + Phase 3 (loop maintains invariant
and terminates) + Phase 4a/4b (post-loop checks + final write) into
`vcdiff_decode'_spec`. Never unfold the full `vcdiff_decode'_def` in the final
theorem; compose modular sub-lemmas via `runs_to_weaken` and `runs_to_bind`.

Error path: when `decode_spec` returns `Inr _`, show C returns non-zero. Mostly
follows from existing error-case lemmas.

### Phase 5 — Cleanup + final build (1 day)

- Remove `quick_and_dirty = true` from ROOT session options.
- Full clean build: `isabelle build -d . -o system_log=true -v CdeltaRefine`
- Verify no sorry/oops in output.

## Dependency Graph

```
Phase 1 (disjointness infra)
    |
    |---> Phase 3 (loop invariant + branches)
    |         |
    |         \---> Phase 4 (post-checks + composition)
    |                   |
Phase 2 (header parse) -/
    |
    \---> Phase 4 ---> Phase 5 (cleanup)
```

Phases 1 and 2 are independent and can proceed in parallel.

## Effort Estimate

| Phase | Days | Notes |
|-------|------|-------|
| 1. Output-write infra | 1-2 | Mostly mechanical lemmas |
| 2. Header/window parse | 3-5 | Sequential VCG, tedious but predictable |
| 3. Main loop + branches | 7-10 | COPY overlap is the hard part |
| 4. Post-checks + compose | 2-3 | Straightforward given 2+3 |
| 5. Cleanup | 1 | Build verification |
| **Total** | **~3 weeks** | |

## Key Risks

1. **COPY overlap semantics** — if `copy_loop`'s recursive definition doesn't
   unfold cleanly against the C's imperative loop, may need an auxiliary
   `copy_loop_nth` characterization lemma in the pure spec layer.

2. **`runs_to_vcg` blowup** — the full `vcdiff_decode'_def` unfolding is
   enormous. Mitigation: never unfold the full definition in the final theorem;
   compose modular sub-lemmas using `runs_to_weaken` and `runs_to_bind`.

3. **Word-arithmetic congestion** — the window-parse section has ~15 variables
   in scope, all `32 word`. Explicit `unat`/`uint` reasoning will dominate.
   Mitigation: establish nat-level facts early with `have` blocks, then cast.

## Build workflow

Keep builds serialized and logged:

```bash
isabelle build -d . -o system_log=true -v CdeltaRefine > cdelta-refine-build.log 2>&1
```
