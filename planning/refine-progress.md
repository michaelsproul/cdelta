# Refinement Layer Progress

## Status

Phase B Step 2 (decoder refinement) is in early stages. Scaffold is up;
one leaf lemma (read_byte) proved; the remaining work is documented in
TODO comments inside `refine/VcdiffDec_Refine.thy` and summarised here.

## What's proved

`refine/VcdiffDec_Refine.thy`:
* `heap_bytes`, `buf_valid` — adapter predicates between the C's
  `buf :: 8 word ptr` + `len :: 32 word` view and the spec's
  `byte list` view.
* `read_byte'_spec` — reader-monad equation: under `ptr_valid` for the
  accessed index, `read_byte' buf len pos s` equals an explicit
  `Some (pr_t_C ...)` based on `pos < len` and `heap_w8 s (buf +ₚ uint pos)`.
* `read_byte'_list_spec` — same, indexed via `heap_bytes ... ! unat pos`.

`spec/Varint.thy`:
* `varint_acc_step` — bit-arithmetic helper. Under `unat v < 2^25`,
  `unat ((v << 7) OR UCAST(b AND 0x7F)) = unat v * 128 + unat (b AND 0x7F)`.
  The refinement invariant for `read_varint'` needs this.

## Proof infrastructure observed

* `runs_to_whileLoop_exn` (from AutoCorres2/lib/Spec_Monad.thy:4205) is
  the right while-loop rule for loops that throw. `runs_to_whileLoop3`
  (3-tuple state) doesn't work because the loop body contains throws.
* `word_plus_and_or` (HOL/Library/Word.thy:3711) is
  `(x AND y) + (x OR y) = x + y`. Combined with `x AND y = 0`, gives
  `x OR y = x + y`. Used in `varint_acc_step`.
* AutoCorres-generated struct constructors lack qualifier prefix:
  `pr_t_C pos val err`, not `⦇pr_t_C.pos_C = pos, …⦈`.
* Struct field `err_C :: 32 signed word`; `VCD_*` abbreviations match.

## Next: read_varint'_spec

The contract:
```
{{ ∀i<unat len. ptr_valid (heap_typing s) (buf +ₚ int i);
   pos ≤ len;
   unat len ≤ length (heap_bytes s buf (unat len)) }}
  read_varint' buf len pos
{{ λrv s'.
   s' = s ∧
   (case varint_decode (drop (unat pos) (heap_bytes s buf (unat len))) of
      Some (v, rest) ⇒
        v < 2^32 ∧
        rv = Result (pr_t_C (len - of_nat (length rest)) (of_nat v) VCD_OK)
    | None ⇒ ∃cur e. rv = Result (pr_t_C cur 0 e) ∧ e ≠ VCD_OK) }}
```

The invariant for the `whileLoop` on `(cur, i, v)`:

```
I (Result (cur, i, v)) s =
  s' = s ∧
  cur = pos + of_nat (unat i) ∧
  pos ≤ cur ∧ cur ≤ len ∧
  i ≤ 5 ∧
  unat v < 128 ^ unat i ∧
  varint_decode_loop (5 - unat i) (unat v)
    (drop (unat cur) (heap_bytes s buf (unat len)))
  = varint_decode (drop (unat pos) (heap_bytes s buf (unat len)))
```

And on Exn path: the Exn carries a `pr_t_C` whose fields match the
postcondition's case analysis on `varint_decode`.

Proof sketch (numbered per `runs_to_whileLoop_exn` subgoals):
1. `wf R` for `R = measure (λ((cur,i,v),_). 5 - unat i)`: by `wf_measure`.
2. `I (Result (pos,0,0)) s`: immediate. `cur = pos + 0`, `i = 0`, both
   bounds are reflexive / trivial; `v = 0 < 128^0 = 1`; the
   `varint_decode_loop` equality holds by `take (unat pos + 0) = take (unat pos)`.
3. `¬ (i < 5) ∧ I (Result (cur,i,v)) s ⟹ P (Result (cur,i,v)) s`.
   If `i = 5`, fuel ran out; `varint_decode` must have returned None
   (since `varint_decode_loop 0 _ _ = None`). But the function then
   does `throw ...`, so the post on `Result` shouldn't fire here.
4. `I (Exn a) s ⟹ P (Exn a) s`: the Exn carries the early-return value.
   Need sub-invariant on what `a` can be (derived from which throw path).
5. Loop body Hoare triple. Case-split on each possible throw:
   - `throw (pr_t_C cur 0 -1)` when `cur ≥ len` — truncation.
     Precondition lets us show `unat cur ≤ unat len`, contradicting
     `cur ≥ len` unless `cur = len`. Then `drop (unat cur) (heap_bytes ...)
     = []`; `varint_decode_loop _ _ [] = None`. Correct.
   - `throw (pr_t_C cur 0 -11)` on overflow check `i = 4 ∧ v AND 0xFE000000 ≠ 0`.
     By invariant `unat v < 128^4 = 2^28`. `v AND 0xFE000000 ≠ 0` means
     `unat v ≥ 2^25`. Then the next step `v' = v * 128 + ...` would
     exceed `2^32`, matching `varint_decode_loop`'s `acc' < 2^32` check
     failing.
   - `throw (pr_t_C cur v 0)` when continuation bit clear — success.
     By `varint_acc_step`, new `unat v' = unat v * 128 + unat (b & 0x7F)`,
     matching `varint_decode_loop`'s `acc'` computation.
   - Fall through (continuation bit set): measure decreases
     `5 - unat (i+1) < 5 - unat i`; new `(cur+1, i+1, v')` satisfies
     invariant (bit-arithmetic via `varint_acc_step`).

Effort estimate: 2-4 days of careful proof engineering once the shape
is clear. Most time in the `varint_decode_loop` equation-chasing.

## After read_varint': decode_address'

`decode_address' patch addr_end pos here mode near_ptr` returns an
`ar_t_C` updating near_arr / same_arr file-scope caches.

Contract shape:
```
{{ buffer valid; mode < 9; cache_invariant s near_ptr; ... }}
  decode_address' patch addr_end pos here mode near_ptr
{{ λrv s'.
    case decode_address c mode here (drop (unat pos) (heap_bytes s ...)) of
      None ⇒ rv = Result (ar_t_C pos 0 near_ptr e) ∧ e ≠ VCD_OK
    | Some (addr, rest, c') ⇒
        rv = Result (ar_t_C (addr_end - of_nat (length rest))
                            (of_nat addr) new_near_ptr VCD_OK) ∧
        cache_invariant s' new_near_ptr ∧
        c' = cache_of_heap s' }}
```

where `c = cache_of_heap s` and `cache_of_heap` extracts the
`cache` record from the file-scope arrays.

Dependencies: `read_byte'_spec`, `read_varint'_spec`.

## After decode_address': build_code_table'

`build_code_table'` is a one-shot builder: fills `code_tbl[256][6]`
with the default table contents.

Contract:
```
{{ True }}
  build_code_table' ()
{{ λ_ s'. code_tbl_built s' = 1 ∧ code_table_matches s' default_entry }}
```

where `code_table_matches` decodes the 256×6 byte array into a function
`nat ⇒ half_inst × half_inst` matching `default_entry`.

Mechanical proof: four nested loops in the C, each with a simple
invariant.

## vcdiff_decode' main loop

The biggest piece. Top-level Hoare triple:
```
{{ ptr_validity for patch, src, out, out_len; disjointness;
   patch_len, src_len, out_cap < 2^32 }}
  vcdiff_decode' patch patch_len src src_len out out_cap out_len
{{ λrv s'.
    case decode_spec (heap_bytes s patch (unat patch_len))
                     (heap_bytes s src (unat src_len)) of
      Inl tgt ⇒
        rv = Result VCD_OK ∧
        heap_bytes s' out (length tgt) = tgt ∧
        heap_w32 s' out_len = of_nat (length tgt) ∧
        (heap outside affected regions unchanged)
    | Inr _ ⇒ rv ≠ Result VCD_OK }}
```

Proof structure:
1. Header parse: 5 bytes, matches `parse_header`.
2. Adler-32 skip (optional).
3. Window header parsing (win_ind, src_seg_len, src_seg_off, dlen,
   tgt_len, Delta_Indicator, data_len, inst_len, addr_len).
4. Code table initialization (if not already built).
5. Cache initialization (near_arr, same_arr zeroed; near_ptr = 0).
6. Main dispatch loop.
7. Post-loop size checks.

The main loop invariant ties the C's cursor positions and scratch
state to the spec's `decode_loop` state via
`encode_window_loop_decode_loop` from the spec layer. Approximate
shape:
```
I s =
  let data_bytes = heap_bytes s patch ... in
    (inst_cursor ≤ inst_end ∧
     tgt_pos ≤ tgt_len ∧
     data_cursor ≤ data_end ∧
     addr_cursor ≤ addr_end ∧
     decode_loop (unat (inst_end - inst_cursor))
                 src_seg src_seg_len tgt_len
                 ⦇ds_data_rem = drop_into_data,
                   ds_inst_rem = drop_into_inst,
                   ds_addr_rem = drop_into_addr,
                   ds_cache    = cache_of_heap s near_ptr,
                   ds_tgt      = heap_bytes s out tgt_pos⦈
     = Inl ⦇final decoder state⦈)
```

Effort: ~2 weeks for the loop invariant alone.

## Step 3 / Step 4 prep

The encoder side (Step 3) is even harder because the C encoder uses a
hash index + best-match search with no pure spec-level analogue. The
plan is to prove only that the C encoder's output, viewed as an
instruction list, satisfies `valid_insts` — then cite the already-proved
`roundtrip_generic` to get the end-to-end theorem.

Step 4 (composition) is a few days of bookkeeping once Step 2 and 3
are done.

## Build cycle

`isabelle build -d spec -d spec/roundtrip -d decoder -d refine CdeltaRefine`
takes ~6 minutes from a clean cache because AutoCorres re-lifts
`vcdiff_dec.c` each time. Iteration is slow; tight dev loops benefit
from the MCP or `isabelle jedit` jumps.

## Known pitfalls (observed during initial work)

* Running multiple concurrent `isabelle build` sessions on overlapping
  session trees triggers `SQLITE_READONLY_DBMOVED` errors. Serialize
  builds.
* `quick_and_dirty = true` at the ROOT level propagates to
  AutoCorres2's own theories and breaks some of their internal proofs.
  Keep the refinement session at `quick_and_dirty = false`; use `oops`
  for intermediate dev states.
* `IS_VALID(8 word) s p` is pure syntactic sugar for
  `ptr_valid (heap_typing s) p` — no `IS_VALID_def` fact exists.
* The AutoCorres-generated `pr_t_C` / `ar_t_C` struct constructors
  have NO qualifier prefix in their field names; use positional form
  `pr_t_C pos val err` or `pr_t_C.make` (if defined).
* Struct fields holding C `int` are `32 signed word`, not `32 word`.
* `is_up` is a simp fact (not `is_up.intros`) for ucasts.
