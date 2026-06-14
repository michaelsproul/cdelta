# Encoder Correctness Parallel Proof Split

## 2026-06-14 status

This document records the old parallelization plan for the direct
`section_decodes` encoder proof. The active plan is now to prove a
non-degenerate pure encoder spec and then prove that the C encoder refines that
spec. See `planning/encoder-refinement-strategy.md`.

The theory split and helper ownership are still useful as an implementation
map, but the final shared interface should move from direct decode correctness
to C-vs-pure encoder simulation.

## Status

`proof/encoder-correctness/VcdiffEnc_Correct.thy` has been split into
parallel-owned theories.  The split is build-clean and introduces no
`sorry`/`oops`.

Build targets verified:

```bash
isabelle build -d . CdeltaEncoderCorrectness
isabelle build -d . CdeltaSpecRoundtrip
isabelle build -o quick_and_dirty=false -d . CdeltaRefine
rg -n "^\s*(sorry|oops)\b" proof spec
```

## Theory Ownership

| Theory | Owner | Responsibility |
| --- | --- | --- |
| `VcdiffEnc_Writers.thy` | Writer agent | Shared heap-byte, buffer-validity, disjointness, and write helper lemmas. |
| `VcdiffEnc_Wire.thy` | Wire agent | Section-decoding predicates and wire-level ADD/RUN/COPY/fused-opcode lemmas. |
| `VcdiffEnc_Cache_Opcode.thy` | Cache/opcode agent | `emit_address`, opcode selector, cache-reset/update, and `best_mode` correspondence. |
| `VcdiffEnc_Match.thy` | Match agent | Match validity facts for `build_index`, `common_prefix`, and `find_best_match`. |
| `VcdiffEnc_Emit.thy` | Emit agent | `emit_add`, `emit_run`, `emit_copy`, `flush_pending`, and `try_emit_add_copy` invariant preservation. |
| `VcdiffEnc_Window.thy` | Window agent | Main `encode_window` loop invariant and success theorem over emitted sections. |
| `VcdiffEnc_Serialize.thy` | Serialize agent | C `serialize` and top-level patch-byte theorem. |
| `VcdiffEnc_Correct.thy` | Integrator | Final composition theorem. |

## Shared Interfaces

- Historical direct-proof interface:
  `section_decodes_prefix`, `section_decodes`, and `enc_sections_inv` connect
  emitted heap sections to decode correctness.
- New refinement interface:
  emitted C section prefixes should equal the corresponding fields of a pure
  encoder state (`data_sec`, `inst_sec`, `addr_sec`, `pending`, `cache`,
  `index`, and cursors).
- `match_valid` is the target shape for match-finder correctness.
- `encoder_loop_inv` is the pure prefix/pending split used by the future C
  loop invariant.

The final encoder theorem should prove byte equality with the non-degenerate
pure `encode_spec` on success. The `decode_spec` result is then obtained by
the spec roundtrip theorem, not by the C encoder proof itself.

## Current Frontier

- `VcdiffEnc_Emit.thy` now proves emitted-section preservation for ADD, RUN,
  and all COPY branches.
- `VcdiffEnc_Emit.thy` also proves `enc_sections_inv` preservation for ADD,
  RUN, and all COPY branches.  COPY varint branches currently expose explicit
  assumptions equating C `varint_bytes32` output with pure `varint_encode`
  bytes.
- Byte writes, byte-sequence writes, varint writes, and both forms of
  `emit_address'` now have cache-frame lemmas.
- ADD, RUN, and all four COPY branches now have combined `enc_sections_inv` +
  `enc_cache_abs` + `enc_cache_wf` success wrappers.  The
  pending-length-zero `try_emit_add_copy'` path and zero-length
  `flush_pending'` path have no-op combined wrappers as well.
- The next shared interface should use that combined shape for non-empty
  `flush_pending`, fused ADD+COPY, and the window loop.  Avoid broad direct
  `write_varint'` loop cache-invariant proofs: they are semantically
  straightforward but too slow in this session.  Prefer the existing
  writer-level cache-field frame theorem or composition of existing writer
  preservation facts.
- The remaining arithmetic bridge is a reusable theorem of the form
  `varint_size' v s = Some n ==> varint_bytes32 v n = varint_encode (unat v)`.

## Worktree Setup

Create worktrees only after the split is committed or otherwise available at a
stable branch point:

```bash
git checkout -b enc-proof-spine
git worktree add ../cdelta-enc-wire -b agent/enc-wire enc-proof-spine
git worktree add ../cdelta-enc-cache -b agent/enc-cache-opcode enc-proof-spine
git worktree add ../cdelta-enc-writers -b agent/enc-writers enc-proof-spine
git worktree add ../cdelta-enc-match -b agent/enc-match enc-proof-spine
git worktree add ../cdelta-enc-emit -b agent/enc-emit enc-proof-spine
git worktree add ../cdelta-enc-window -b agent/enc-window enc-proof-spine
```

Recommended merge order:

1. Merge Wire, Cache/Opcode, Writers/Serialize, and Match.
2. Merge Emit after the shared wire/cache facts are stable.
3. Merge Window after Emit and Match are stable.
4. Merge Serialize and final `VcdiffEnc_Correct` composition.

Each agent branch must pass:

```bash
isabelle build -d . CdeltaEncoderCorrectness
rg -n "^\s*(sorry|oops)\b" proof spec
```
