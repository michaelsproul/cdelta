(*
  Pure VCDIFF encoder spec.

  Mirrors encoder/vcdiff_enc.c at the functional level. The structure is:

    encode_spec src tgt
      = let insts = generate_instructions src tgt   -- match finder
            (data, inst_bytes, addr_bytes, _cache)
              = encode_window insts (length src)
        in serialize src tgt data inst_bytes addr_bytes

  The matcher is non-deterministic in the sense that any `raw_inst list`
  that reproduces `tgt` when executed against `src` is a valid output; we
  specify the *output format* here and defer the matching algorithm to a
  concrete function whose only required property is "exec_inst_list src
  insts [] = tgt". That loose coupling is what lets us prove roundtrip
  correctness without having to mirror the exact greedy-matcher details
  of the C.
*)
theory Encoder_Spec
  imports
    Bytes
    Varint
    AddressCache
    CodeTable
    Instructions
begin

unbundle bit_operations_syntax

(* ---------- Instruction generation (abstract) ---------- *)
(*
  Any function satisfying `generate_instructions_valid` is acceptable for
  the spec. We expose a constant that's fixed later by a concrete
  algorithm; the correctness statement is independent.
*)
definition generates_target :: "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list \<Rightarrow> bool" where
  "generates_target src tgt insts = (exec_inst_list src insts [] = tgt)"

(*
  Concrete matcher: produce a single `RAdd tgt` instruction for the
  entire target. This is a degenerate but valid matcher — it satisfies
  generates_target for any (src, tgt) pair. A smarter matcher with COPY
  and RUN instructions would refine this but the roundtrip theorem holds
  for any matcher satisfying `generates_target`.
*)
definition generate_instructions :: "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list" where
  "generate_instructions src tgt = [RAdd tgt]"

lemma generate_instructions_correct:
  "generates_target src tgt (generate_instructions src tgt)"
  by (simp add: generates_target_def generate_instructions_def)

(* ---------- Per-instruction encoding ---------- *)

(*
  Encode one instruction into the three sections. Returns the updated
  sections and the updated address cache. Simplified: always emit single
  opcodes (no ADD+COPY/COPY+ADD fusion). Fusion is an optimisation the
  concrete C encoder does but it's not required for correctness and
  avoiding it keeps the spec small.
*)
fun encode_one ::
    "raw_inst \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cache \<Rightarrow>
     byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
     byte list \<times> byte list \<times> byte list \<times> cache \<times> nat" where
  "encode_one (RAdd bs) src_len tgt_pos c data inst addr =
     (let (op, needs_sz) = find_single_add_opcode (length bs);
          inst' = inst @ [word_of_nat op] @
                   (if needs_sz then varint_encode (length bs) else []);
          data' = data @ bs
      in (data', inst', addr, c, tgt_pos + length bs))"
| "encode_one (RRun b n) src_len tgt_pos c data inst addr =
     (let (op, needs_sz) = find_single_run_opcode n;
          inst' = inst @ [word_of_nat op] @
                   (if needs_sz then varint_encode n else []);
          data' = data @ [b]
      in (data', inst', addr, c, tgt_pos + n))"
| "encode_one (RCopy a n) src_len tgt_pos c data inst addr =
     (let here = src_len + tgt_pos;
          (mode, abytes, c') = encode_address c a here;
          (op, needs_sz) = find_single_copy_opcode n mode;
          inst' = inst @ [word_of_nat op] @
                   (if needs_sz then varint_encode n else []);
          addr' = addr @ abytes
      in (data, inst', addr', c', tgt_pos + n))"

fun encode_window_loop ::
    "raw_inst list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cache \<Rightarrow>
     byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
     byte list \<times> byte list \<times> byte list \<times> cache" where
  "encode_window_loop [] src_len tgt_pos c data inst addr =
     (data, inst, addr, c)"
| "encode_window_loop (i # is) src_len tgt_pos c data inst addr =
     (let (data', inst', addr', c', tgt_pos') =
        encode_one i src_len tgt_pos c data inst addr
      in encode_window_loop is src_len tgt_pos' c' data' inst' addr')"

definition encode_window ::
    "raw_inst list \<Rightarrow> nat \<Rightarrow> byte list \<times> byte list \<times> byte list \<times> cache" where
  "encode_window insts src_len =
     encode_window_loop insts src_len 0 cache_init [] [] []"

(* ---------- Wire format ---------- *)

definition magic_bytes :: "byte list" where
  "magic_bytes = [0xD6, 0xC3, 0xC4, 0x00]"

(*
  Serialize the single-window VCDIFF patch. Layout (from vcdiff_enc.c's
  serialize function):
    4-byte magic + 0x00 version byte
    1 byte Hdr_Indicator = 0
    1 byte Win_Indicator = 0x01 if src non-empty else 0x00
    [ varint(src_len) varint(0) ] when Win_Indicator & 0x01
    varint(dlen)
    varint(tgt_len)
    1 byte Delta_Indicator = 0
    varint(data_len) varint(inst_len) varint(addr_len)
    data || inst || addr
  where dlen = varint_size(tgt_len)+1+varint_size(data_len)+varint_size(inst_len)+varint_size(addr_len)+data_len+inst_len+addr_len.
*)
definition serialize ::
    "byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list" where
  "serialize src tgt data inst addr =
     (let has_src = (length src > 0);
          win_ind = (if has_src then 0x01 else 0x00 :: byte);
          dlen    = varint_size (length tgt) + 1
                  + varint_size (length data)
                  + varint_size (length inst)
                  + varint_size (length addr)
                  + length data + length inst + length addr;
          src_desc = (if has_src
                      then varint_encode (length src) @ varint_encode 0
                      else [])
      in magic_bytes @ [0x00, win_ind] @ src_desc
       @ varint_encode dlen
       @ varint_encode (length tgt)
       @ [0x00]
       @ varint_encode (length data)
       @ varint_encode (length inst)
       @ varint_encode (length addr)
       @ data @ inst @ addr)"

(* ---------- Top-level ---------- *)

definition encode_spec :: "byte list \<Rightarrow> byte list \<Rightarrow> byte list" where
  "encode_spec src tgt =
     (let insts = generate_instructions src tgt;
          result = encode_window insts (length src);
          data = fst result;
          inst = fst (snd result);
          addr = fst (snd (snd result))
      in serialize src tgt data inst addr)"

end
