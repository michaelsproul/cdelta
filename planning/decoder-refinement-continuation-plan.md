# Decoder Refinement Continuation Plan

## Summary

Update 2026-05-25: `CdeltaRefine` builds again under the current
`quick_and_dirty` setting after factoring the no-source/no-Adler concrete
inner-body preservation proof into `decode_inner_body_preserves_no_source`.
Both no-source/no-Adler outer-loop call sites now reuse that helper instead
of carrying separate 4.5k-line body proofs.  The remaining residual there is
still localized to the success-tail weakening after the outer loop.

Update 2026-05-25 later: the app-header/code-table-built no-source payload
branch now has a staged payload fact (`app_no_source_payload_stage`) and the
read-byte, payload varint, dlen-length, and payload-size guards are discharged.
The success-loop application in that branch is now closed via
`outer_whileLoop_correct_success_abstract`; the entry proof reconstructs the
no-source payload slices from the staged facts, and the loop body reuses
`decode_inner_body_preserves_no_source`.

The rescue branch is structurally viable, but the current theorem is not
integrity-safe because the pure decoder accepts some patches the C decoder
rejects. Align the pure spec with the C decoder first, then continue from the
proved `decode_loop_inv_plus_exit`, `outer_whileLoop_correct_abstract`, and
`decode_loop_inv_plus_advance` lemmas.

Validated facts:

- `CdeltaRefine` builds under current `quick_and_dirty`.
- The latest docs are stale in places: the three outer-loop API lemmas listed
  as sorries are now proved.
- Remaining active proof debt in `proof/decoder-refine/VcdiffDec_Refine.thy`
  is now two localized `sorry`s:
  - no-source/no-Adler success-tail weakening after the factored body proof,
  - the Inr rejection case.
  Older notes about `build_code_table'_preserves_typing` and
  `vcdiff_decode'_prefix_correct` being active sorries are stale.
- The main spec mismatch is broader than leftover data/address bytes:
  `parse_window` also ignores `dlen` consistency and does not model Adler32
  positioning the same way as the C parser.

## Key Changes

- Tighten `spec/pure/Decoder_Spec.thy` to match the C parser:
  - In `parse_window`, use `dlen` to require the exact C delta layout:
    `dlen = consumed_after_lengths + adler_len + data_len + inst_len + addr_len`.
  - Preserve C's accepted `win_ind` shape: source bit and Adler bit allowed,
    target/unknown bits rejected.
  - If Adler bit is set, skip 4 bytes before `data`; do not treat Adler bytes
    as data.
  - Keep `parsed_window` fields unchanged unless proof pressure shows storing
    `adler_len` is necessary.
- Tighten `apply_window`:
  - After `decode_loop` succeeds, require `length ds_tgt = pw_tgt_len`,
    `ds_data_rem = []`, and `ds_addr_rem = []`.
  - Return `E_SIZE` if target length, data consumption, or address consumption
    is wrong.
- Update spec lemmas affected by the parser change:
  - Repair `parse_window_no_source`, `parse_window_with_source`, and roundtrip
    parse lemmas with exact `dlen` premises.
  - Add extraction lemmas from `decode_spec = Inl tgt` giving exact final
    data/address exhaustion.
- Strengthen `decode_loop_inv_plus_exit` to return output equality,
  `unat tgt_pos = tgt_len`, `data_cursor = data_end`, and
  `addr_cursor = addr_end`.

## Proof Work

- App-header/code-table-built no-source payload success loop is closed. The
  next residual is the no-app `parse_window_prefix' ... 5` success path; the
  stale build-code-table branch closes from `code_tbl_ready`, leaving the
  already-built prefix obligation before the final cursor/write checks.
- Update 2026-05-25: the no-app prefix obligation is now split far enough that
  the stale sibling closes from the no-app header/drop-5 facts.  Expanding the
  remaining sibling exposes the source-window path first, so the next useful
  refactor is a fixed-position no-app/source prefix bridge analogous to the
  app-header source staging facts, not another copy of the outer-loop body.
- A reusable no-app/no-source heap bridge,
  `noapp_no_source_prefix_decodes_heap`, now turns
  `parse_window (drop 5 ...)` plus the concrete no-source bit into the dlen,
  target-length, DI, data, instruction, and address varint chain.  Use it to
  stage the no-source/no-Adler payload facts instead of copying the app-header
  prefix proof.
- The no-app bridge now has two cursor-alignment helpers:
  `noapp_no_source_tgt_decode_some_heap` for the target-length read, and
  `noapp_no_source_payload_stage_heap` for the dlen/tgt cursor drops plus the
  staged payload chain.  These are placed after `varint_decode_drop_rest` so
  they can reuse the common varint suffix/drop alignment fact.
- Remove the no-app/no-source/no-Adler `sorry` by splitting the exposed
  `parse_window_prefix'` obligation, applying the new prefix bridge, then
  replaying the exit-weakening/post-loop cursor proof against the record-shaped
  cursor state (`addr_pos_C v`, `data_pos_C v`, `inst_pos_C v`).
- Continue reusing `decode_inner_body_preserves_no_source` for no-source loop
  bodies; avoid reintroducing expanded inner-body proofs.
- Finish the Inr case by contrapositive: if C returns `Result 0`, the tightened
  `decode_spec` returns `Inl` with matching output.

## Test Plan

- Run spec builds with fresh verbose logs:
  `isabelle build -o system_log=true -v -d . CdeltaSpecBase CdeltaSpecRoundtrip`.
- Run refinement builds with fresh verbose logs:
  `isabelle build -o system_log=true -v -d . CdeltaRefine`.
- Before completion, `rg -n "sorry|oops" proof spec` should show no remaining
  active proof holes.

## Assumptions

- Target contract is full decoder refinement against a C-aligned pure spec, not
  encoder-only refinement.
- Adler32 is parsed/skipped to match C, but checksum validation is not added
  because the C decoder does not validate it.
- `out_cap_enough` remains for now; removing it is a later theorem-strengthening
  task after functional refinement is closed.
