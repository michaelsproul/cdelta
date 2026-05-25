# Decoder Refinement Continuation Plan

## Summary

Update 2026-05-25: `CdeltaRefine` builds again under the current
`quick_and_dirty` setting after replacing the final no-source/no-Adler
inner-body `apply fail` with the completed copied body-preservation proof
shape.  The copied proof discharges the concrete opcode/which-loop body
for that branch; the remaining residual there is now localized to the
success-tail weakening after the outer loop.

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
  is now three localized `sorry`s:
  - app-header/code-table-built no-source payload residual,
  - no-source/no-Adler success-tail weakening after the copied body proof,
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

- Close the app-header/code-table-built no-source payload residual at the old
  local branch.  The nearby completed no-source/no-Adler proof now gives the
  body-preservation shape to replay, but the pre-loop payload/position bridge
  still needs to be connected.
- Remove the new success-tail `sorry` after the copied no-source/no-Adler body
  proof by replaying the exit-weakening/post-loop cursor proof against the
  record-shaped cursor state (`addr_pos_C v`, `data_pos_C v`, `inst_pos_C v`).
- Factor the concrete outer-loop body preservation once.  The latest copied
  proof confirms the branch shape scales, but the duplication is now very
  expensive for both maintenance and build time.
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
