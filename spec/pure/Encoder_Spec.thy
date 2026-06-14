(*
  Pure VCDIFF encoder spec.

  Mirrors spec/cenc/vcdiff_enc.c at the functional level. The structure is:

    encode_spec src tgt
      = let insts = generate_instructions src tgt   -- match finder
            (data, inst_bytes, addr_bytes, _cache)
              = encode_window insts (length src)
        in serialize src tgt data inst_bytes addr_bytes

  The current concrete generator is the first non-degenerate step: it emits a
  RUN when the whole target is one repeated byte of length at least four,
  otherwise it emits one ADD. This is intentionally smaller than the C matcher,
  but it breaks the old single-ADD spec shape and gives the pure roundtrip
  theorem a real RUN path to compose through. COPY matching and opcode fusion
  can be added behind the same `generate_instructions` boundary.
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

(* ---------- Instruction generation ---------- *)

definition generates_target :: "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list \<Rightarrow> bool" where
  "generates_target src tgt insts = (exec_inst_list src insts [] = tgt)"

(*
  Baseline matcher retained for regression tests and the old proof notes. It
  is no longer the main `encode_spec` path.
*)
definition generate_instructions_degenerate ::
    "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list" where
  "generate_instructions_degenerate src tgt = [RAdd tgt]"

lemma generate_instructions_degenerate_correct:
  "generates_target src tgt (generate_instructions_degenerate src tgt)"
  by (simp add: generates_target_def generate_instructions_degenerate_def)

(*
  First non-degenerate generator. If the whole target is one byte repeated at
  least four times, emit a RUN. Otherwise emit a single ADD. This deliberately
  starts smaller than the C matcher while changing the public spec away from
  the old always-ADD encoder.
*)
definition all_bytes_eq :: "byte \<Rightarrow> byte list \<Rightarrow> bool" where
  "all_bytes_eq b bs = list_all (\<lambda>x. x = b) bs"

definition generate_run_instructions :: "byte list \<Rightarrow> raw_inst list" where
  "generate_run_instructions tgt =
     (case tgt of
        [] \<Rightarrow> []
      | b # bs \<Rightarrow>
          if 4 \<le> length tgt \<and> all_bytes_eq b bs
          then [RRun b (length tgt)]
          else [RAdd tgt])"

definition generate_instructions :: "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list" where
  "generate_instructions src tgt = generate_run_instructions tgt"

lemma generate_run_instructions_exec:
  "exec_inst_list src (generate_run_instructions tgt) acc = acc @ tgt"
proof (cases tgt)
  case Nil
  then show ?thesis by (simp add: generate_run_instructions_def)
next
  case (Cons b bs)
  show ?thesis
  proof (cases "4 \<le> length tgt \<and> all_bytes_eq b bs")
    case True
    have bs_rep: "bs = replicate (length bs) b"
      using True by (induction bs) (auto simp: all_bytes_eq_def)
    have tgt_rep: "tgt = replicate (length tgt) b"
      using Cons bs_rep by simp
    show ?thesis
      using Cons True tgt_rep
      by (simp add: generate_run_instructions_def append_assoc)
  next
    case False
    have norun: "\<not> (4 \<le> length (b # bs) \<and> all_bytes_eq b bs)"
      using False Cons by simp
    then show ?thesis
      using Cons norun by (auto simp: generate_run_instructions_def)
  qed
qed

lemma generate_run_instructions_wf_aux:
  "wf_insts_aux src (generate_run_instructions tgt) acc"
  by (cases tgt) (auto simp: generate_run_instructions_def)

lemma generate_run_instructions_valid:
  "valid_insts src tgt (generate_run_instructions tgt)"
  by (simp add: valid_insts_def wf_insts_def generate_run_instructions_exec
                generate_run_instructions_wf_aux)

lemma generate_instructions_correct:
  "generates_target src tgt (generate_instructions src tgt)"
  by (simp add: generates_target_def generate_instructions_def
                generate_run_instructions_exec)

(* ---------- C-shaped full encoder spec skeleton ---------- *)

definition hash_bits :: nat where "hash_bits = 16"
definition hash_size :: nat where "hash_size = 2 ^ hash_bits"
definition hash_mask :: nat where "hash_mask = hash_size - 1"
definition max_chain :: nat where "max_chain = 16"
definition min_match :: nat where "min_match = 4"
definition min_run :: nat where "min_run = 4"

type_synonym source_index = "nat list list"

record enc_match =
  em_pos :: nat
  em_len :: nat

definition no_match :: enc_match where
  "no_match = \<lparr> em_pos = 0, em_len = 0 \<rparr>"

definition hash4_spec :: "byte list \<Rightarrow> nat \<Rightarrow> nat" where
  "hash4_spec bs pos =
     (((unat (bs ! pos))
       + 256 * unat (bs ! (pos + 1))
       + 65536 * unat (bs ! (pos + 2))
       + 16777216 * unat (bs ! (pos + 3)))
      * 2654435761) mod 2 ^ 32"

definition hash_bucket_spec :: "byte list \<Rightarrow> nat \<Rightarrow> nat" where
  "hash_bucket_spec bs pos = hash4_spec bs pos mod hash_size"

definition source_positions_spec :: "byte list \<Rightarrow> nat list" where
  "source_positions_spec src =
     (if length src < min_match then [] else [0..<length src - min_match + 1])"

definition build_index_spec :: "byte list \<Rightarrow> source_index" where
  "build_index_spec src =
     map (\<lambda>h. filter (\<lambda>p. hash_bucket_spec src p = h) (source_positions_spec src))
       [0..<hash_size]"

fun common_prefix_fuel ::
    "nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat" where
  "common_prefix_fuel 0 a apos b bpos = 0"
| "common_prefix_fuel (Suc fuel) a apos b bpos =
     (if apos < length a \<and> bpos < length b \<and> a ! apos = b ! bpos
      then Suc (common_prefix_fuel fuel a (apos + 1) b (bpos + 1))
      else 0)"

definition common_prefix_spec ::
    "byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "common_prefix_spec a apos aend b bpos bend =
     common_prefix_fuel (min (aend - apos) (bend - bpos))
       (take aend a) apos (take bend b) bpos"

definition index_bucket_spec :: "source_index \<Rightarrow> nat \<Rightarrow> nat list" where
  "index_bucket_spec index h = (if h < length index then index ! h else [])"

definition choose_match_spec ::
    "byte list \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> enc_match \<Rightarrow> enc_match" where
  "choose_match_spec src tgt tp cand best =
     (let l = common_prefix_spec src cand (length src) tgt tp (length tgt) in
      if cand + min_match \<le> length src \<and> min_match \<le> l \<and> em_len best < l
      then \<lparr> em_pos = cand, em_len = l \<rparr>
      else best)"

definition find_best_match_spec ::
    "byte list \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> source_index \<Rightarrow> enc_match" where
  "find_best_match_spec src tgt tp index =
     (if length src < min_match \<or> length tgt - tp < min_match then no_match
      else
        let h = hash_bucket_spec tgt tp;
            candidates = take max_chain (index_bucket_spec index h)
        in foldl (\<lambda>best cand. choose_match_spec src tgt tp cand best)
             no_match candidates)"

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

(* ---------- Accumulator-prefix properties ---------- *)

lemma encode_one_prefix:
  obtains d ib ab c' tp'
  where "encode_one i sl tp c data inst addr = (data @ d, inst @ ib, addr @ ab, c', tp')"
    and "encode_one i sl tp c [] [] [] = (d, ib, ab, c', tp')"
proof (cases i)
  case (RAdd bs)
  obtain op needs_sz where fop: "find_single_add_opcode (length bs) = (op, needs_sz)"
    by (cases "find_single_add_opcode (length bs)") auto
  let ?ib = "[word_of_nat op] @ (if needs_sz then varint_encode (length bs) else [])"
  show ?thesis
    using that[of bs ?ib "[]" c "tp + length bs"]
    by (simp add: RAdd fop split_def Let_def)
next
  case (RCopy a n)
  obtain mode abytes c' where ea: "encode_address c a (sl + tp) = (mode, abytes, c')"
    by (cases "encode_address c a (sl + tp)") auto
  obtain op needs_sz where fop: "find_single_copy_opcode n mode = (op, needs_sz)"
    by (cases "find_single_copy_opcode n mode") auto
  let ?ib = "[word_of_nat op] @ (if needs_sz then varint_encode n else [])"
  show ?thesis
    using that[of "[]" ?ib abytes c' "tp + n"]
    by (simp add: RCopy ea fop split_def Let_def)
next
  case (RRun b n)
  obtain op needs_sz where fop: "find_single_run_opcode n = (op, needs_sz)"
    by (cases "find_single_run_opcode n") auto
  let ?ib = "[word_of_nat op] @ (if needs_sz then varint_encode n else [])"
  show ?thesis
    using that[of "[b]" ?ib "[]" c "tp + n"]
    by (simp add: RRun fop split_def Let_def)
qed

lemma encode_window_loop_prefix:
  "\<exists>d ib ab c'.
     encode_window_loop insts sl tp c data inst addr = (data @ d, inst @ ib, addr @ ab, c')
   \<and> encode_window_loop insts sl tp c [] [] [] = (d, ib, ab, c')"
proof (induction insts arbitrary: tp c data inst addr)
  case Nil
  then show ?case by auto
next
  case (Cons i rest)
  obtain d0 ib0 ab0 c0 tp0 where
    eo: "encode_one i sl tp c data inst addr = (data @ d0, inst @ ib0, addr @ ab0, c0, tp0)" and
    eo0: "encode_one i sl tp c [] [] [] = (d0, ib0, ab0, c0, tp0)"
    by (rule encode_one_prefix)
  obtain d1 ib1 ab1 c1 where
    ih0: "encode_window_loop rest sl tp0 c0 [] [] [] = (d1, ib1, ab1, c1)"
    using Cons.IH[of tp0 c0 "[]" "[]" "[]"] by auto
  have ih: "encode_window_loop rest sl tp0 c0 (data @ d0) (inst @ ib0) (addr @ ab0) =
           ((data @ d0) @ d1, (inst @ ib0) @ ib1, (addr @ ab0) @ ab1, c1)"
    using Cons.IH[of tp0 c0 "data @ d0" "inst @ ib0" "addr @ ab0"] ih0 by auto
  have ih0': "encode_window_loop rest sl tp0 c0 d0 ib0 ab0 =
                (d0 @ d1, ib0 @ ib1, ab0 @ ab1, c1)"
    using Cons.IH[of tp0 c0 d0 ib0 ab0] ih0 by auto
  show ?case
    using eo eo0 ih ih0' by (simp add: split_def Let_def)
qed

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

(* ---------- C-shaped stateful encoder spec ---------- *)

record enc_full_state =
  enc_tp      :: nat
  enc_flushed :: nat
  enc_pending :: "byte list"
  enc_data    :: "byte list"
  enc_inst    :: "byte list"
  enc_addr    :: "byte list"
  enc_cache   :: cache
  enc_trace   :: "raw_inst list"

definition enc_full_init :: enc_full_state where
  "enc_full_init =
     \<lparr> enc_tp = 0
     , enc_flushed = 0
     , enc_pending = []
     , enc_data = []
     , enc_inst = []
     , enc_addr = []
     , enc_cache = cache_init
     , enc_trace = [] \<rparr>"

definition emit_inst_spec ::
    "nat \<Rightarrow> raw_inst \<Rightarrow> enc_full_state \<Rightarrow> enc_full_state" where
  "emit_inst_spec src_len i st =
     (let (data', inst', addr', cache', flushed') =
        encode_one i src_len (enc_flushed st) (enc_cache st)
          (enc_data st) (enc_inst st) (enc_addr st)
      in st \<lparr> enc_data := data'
              , enc_inst := inst'
              , enc_addr := addr'
              , enc_cache := cache'
              , enc_flushed := flushed'
              , enc_trace := enc_trace st @ [i] \<rparr>)"

definition emit_insts_spec ::
    "nat \<Rightarrow> raw_inst list \<Rightarrow> enc_full_state \<Rightarrow> enc_full_state" where
  "emit_insts_spec src_len insts st =
     foldl (\<lambda>s i. emit_inst_spec src_len i s) st insts"

record pending_scan =
  ps_add      :: "byte list"
  ps_run_byte :: "byte option"
  ps_run_len  :: nat
  ps_out      :: "raw_inst list"

definition pending_scan_init :: pending_scan where
  "pending_scan_init =
     \<lparr> ps_add = [], ps_run_byte = None, ps_run_len = 0, ps_out = [] \<rparr>"

definition append_add_inst :: "byte list \<Rightarrow> raw_inst list \<Rightarrow> raw_inst list" where
  "append_add_inst bs out = (if bs = [] then out else out @ [RAdd bs])"

definition close_pending_run :: "pending_scan \<Rightarrow> pending_scan" where
  "close_pending_run s =
     (case ps_run_byte s of
        None \<Rightarrow> s
      | Some b \<Rightarrow>
          if min_run \<le> ps_run_len s
          then s \<lparr> ps_add := []
                 , ps_run_byte := None
                 , ps_run_len := 0
                 , ps_out := append_add_inst (ps_add s) (ps_out s)
                     @ [RRun b (ps_run_len s)] \<rparr>
          else s \<lparr> ps_add := ps_add s @ replicate (ps_run_len s) b
                 , ps_run_byte := None
                 , ps_run_len := 0 \<rparr>)"

definition pending_scan_step :: "pending_scan \<Rightarrow> byte \<Rightarrow> pending_scan" where
  "pending_scan_step s b =
     (case ps_run_byte s of
        None \<Rightarrow> s \<lparr> ps_run_byte := Some b, ps_run_len := 1 \<rparr>
      | Some rb \<Rightarrow>
          if b = rb
          then s \<lparr> ps_run_len := ps_run_len s + 1 \<rparr>
          else (close_pending_run s)
                 \<lparr> ps_run_byte := Some b, ps_run_len := 1 \<rparr>)"

definition flush_pending_insts :: "byte list \<Rightarrow> raw_inst list" where
  "flush_pending_insts pending =
     (let s = close_pending_run (foldl pending_scan_step pending_scan_init pending)
      in append_add_inst (ps_add s) (ps_out s))"

definition flush_pending_spec ::
    "nat \<Rightarrow> enc_full_state \<Rightarrow> enc_full_state" where
  "flush_pending_spec src_len st =
     (emit_insts_spec src_len (flush_pending_insts (enc_pending st)) st)
       \<lparr> enc_pending := [] \<rparr>"

definition buffer_pending_byte_spec ::
    "byte \<Rightarrow> enc_full_state \<Rightarrow> enc_full_state" where
  "buffer_pending_byte_spec b st =
     st \<lparr> enc_tp := enc_tp st + 1
        , enc_pending := enc_pending st @ [b] \<rparr>"

definition emit_copy_spec ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> enc_full_state \<Rightarrow> enc_full_state" where
  "emit_copy_spec src_len addr len st =
     (emit_inst_spec src_len (RCopy addr len) st)
       \<lparr> enc_tp := enc_tp st + len \<rparr>"

definition fused_copy_len_spec :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "fused_copy_len_spec mode copy_len =
     (if mode \<le> 5 then
        if min_match \<le> copy_len then Some (min copy_len 6) else None
      else if mode \<le> 8 \<and> copy_len = 4 then Some 4
      else None)"

definition try_emit_add_copy_spec ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> enc_full_state \<Rightarrow> enc_full_state option" where
  "try_emit_add_copy_spec src_len copy_addr copy_len st =
     (let add_bs = enc_pending st;
          add_len = length add_bs;
          here = src_len + enc_tp st;
          (mode, abytes, cache') = encode_address (enc_cache st) copy_addr here
      in if 1 \<le> add_len \<and> add_len \<le> 4 \<and> min_match \<le> copy_len then
           case fused_copy_len_spec mode copy_len of
             None \<Rightarrow> None
           | Some csz \<Rightarrow>
               (case find_add_copy_opcode add_len csz mode of
                  None \<Rightarrow> None
                | Some op \<Rightarrow>
                    Some (st \<lparr> enc_tp := enc_tp st + csz
                             , enc_flushed := enc_flushed st + add_len + csz
                             , enc_pending := []
                             , enc_data := enc_data st @ add_bs
                             , enc_inst := enc_inst st @ [word_of_nat op]
                             , enc_addr := enc_addr st @ abytes
                             , enc_cache := cache'
                             , enc_trace := enc_trace st
                                 @ [RAdd add_bs, RCopy copy_addr csz] \<rparr>))
         else None)"

definition flush_then_emit_copy_spec ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> enc_full_state \<Rightarrow> enc_full_state" where
  "flush_then_emit_copy_spec src_len copy_addr copy_len st =
     (let st' = (if enc_pending st = [] then st else flush_pending_spec src_len st)
      in emit_copy_spec src_len copy_addr copy_len st')"

fun encode_window_full_loop ::
    "nat \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> source_index \<Rightarrow>
     enc_full_state \<Rightarrow> enc_full_state" where
  "encode_window_full_loop 0 src tgt index st =
     (if enc_tp st < length tgt then st else flush_pending_spec (length src) st)"
| "encode_window_full_loop (Suc fuel) src tgt index st =
     (if enc_tp st \<ge> length tgt then flush_pending_spec (length src) st
      else
        let m = find_best_match_spec src tgt (enc_tp st) index in
        if em_len m < min_match then
          encode_window_full_loop fuel src tgt index
            (buffer_pending_byte_spec (tgt ! enc_tp st) st)
        else
          let st' =
            (case try_emit_add_copy_spec (length src) (em_pos m) (em_len m) st of
               Some fused \<Rightarrow>
                 let consumed = enc_tp fused - enc_tp st in
                 if consumed < em_len m
                 then emit_copy_spec (length src) (em_pos m + consumed)
                        (em_len m - consumed) fused
                 else fused
             | None \<Rightarrow>
                 flush_then_emit_copy_spec (length src) (em_pos m) (em_len m) st)
          in encode_window_full_loop fuel src tgt index st')"

record enc_full_result =
  efr_data  :: "byte list"
  efr_inst  :: "byte list"
  efr_addr  :: "byte list"
  efr_cache :: cache
  efr_trace :: "raw_inst list"

definition enc_full_result_of_state :: "enc_full_state \<Rightarrow> enc_full_result" where
  "enc_full_result_of_state st =
     \<lparr> efr_data = enc_data st
     , efr_inst = enc_inst st
     , efr_addr = enc_addr st
     , efr_cache = enc_cache st
     , efr_trace = enc_trace st \<rparr>"

definition encode_window_full_spec ::
    "byte list \<Rightarrow> byte list \<Rightarrow> enc_full_result" where
  "encode_window_full_spec src tgt =
     (let index = build_index_spec src;
          st = encode_window_full_loop (length tgt + 1) src tgt index enc_full_init
      in enc_full_result_of_state st)"

definition encode_spec_full :: "byte list \<Rightarrow> byte list \<Rightarrow> byte list" where
  "encode_spec_full src tgt =
     (let r = encode_window_full_spec src tgt
      in serialize src tgt (efr_data r) (efr_inst r) (efr_addr r))"

(* ---------- Top-level ---------- *)

definition serialize_from_insts ::
    "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list \<Rightarrow> byte list" where
  "serialize_from_insts src tgt insts =
     (let result = encode_window insts (length src);
          data = fst result;
          inst = fst (snd result);
          addr = fst (snd (snd result))
      in serialize src tgt data inst addr)"

definition encode_spec_degenerate :: "byte list \<Rightarrow> byte list \<Rightarrow> byte list" where
  "encode_spec_degenerate src tgt =
     serialize_from_insts src tgt (generate_instructions_degenerate src tgt)"

definition encode_spec_run :: "byte list \<Rightarrow> byte list \<Rightarrow> byte list" where
  "encode_spec_run src tgt =
     serialize_from_insts src tgt (generate_instructions src tgt)"

definition encode_spec :: "byte list \<Rightarrow> byte list \<Rightarrow> byte list" where
  "encode_spec src tgt = encode_spec_full src tgt"

lemma encode_spec_run_alt:
  "encode_spec_run src tgt =
     (let insts = generate_instructions src tgt;
          result = encode_window insts (length src);
          data = fst result;
          inst = fst (snd result);
          addr = fst (snd (snd result))
      in serialize src tgt data inst addr)"
  by (simp add: encode_spec_run_def serialize_from_insts_def)

lemma encode_spec_alt:
  "encode_spec src tgt =
     (let r = encode_window_full_spec src tgt
      in serialize src tgt (efr_data r) (efr_inst r) (efr_addr r))"
  by (simp add: encode_spec_def encode_spec_full_def)

end
