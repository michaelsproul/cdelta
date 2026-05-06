# Refinement Layer Progress

## Status (2026-05-06)

Phase B Step 2 (decoder refinement) has moved past leaf lemmas and now has a
full proof for `build_code_table'_spec`. This includes the previously open
ADD+COPY inner-loop obligations from `insights.md` step (1).

## Completed (current theory state)

In [proof/decoder-refine/VcdiffDec_Refine.thy](/home/michael/Programming/cdelta/proof/decoder-refine/VcdiffDec_Refine.thy):

* `read_byte'_spec` and `read_byte'_list_spec` are proved.
* `read_varint'_spec` is present and proved (`line 337`).
* `decode_address'_spec` is present and proved (`line 975`).
* `build_code_table'_spec` is proved (`line 1789`), including:
  * table-shape relation via `code_tbl_matches` / `code_tbl_matches_upto`;
  * loop-chain coverage through COPY+ADD rows;
  * postcondition `code_tbl_built_'' s' = 1` and table-match invariant.

This confirms GPT-5.5’s step (1) as done.

## Remaining Decoder-Refinement Debt

1. Main theorem for `vcdiff_decode'` is still TODO (the section starts near
   `line 2452`).
2. Header/window parsing correspondence lemmas are not yet isolated as
   standalone proof islands.
3. Instruction-loop invariant for the top-level decode loop is not yet encoded
   as a reusable predicate (`decode_loop_abs` style from insights).

## Notes on stale TODO comments

The file still contains comment-level TODO text around older milestones (e.g.
`read_varint` commentary and intermediate build-code-table comments), but there
are no `sorry`/`oops` markers in this theory.

## Next Proof Order (updated from insights)

1. Start `vcdiff_decode'` with a **success-only** theorem under well-formed
   encoder-produced patches and explicit no-overflow/no-Adler assumptions.
2. Add reusable infrastructure before the main loop:
   section-slice lemmas (`heap_bytes`/`take`/`drop` cursor relations), output
   write preservation lemmas, and cache-init correspondence lemmas.
3. Prove header parsing and window metadata parsing as separate lemmas.
4. Introduce a named decode-loop invariant tying C cursors/cache/output bytes
   to the pure `decode_loop` state, then discharge ADD/RUN/COPY branches
   incrementally.

## Build workflow

Keep builds serialized and logged:

```bash
isabelle build -d . -o system_log=true -v CdeltaRefine > cdelta-refine-build.log 2>&1
```
