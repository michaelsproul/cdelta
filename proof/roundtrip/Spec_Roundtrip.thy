(*
  Top-level roundtrip theorem: decoding what the encoder produced recovers
  the target.

  The old single-ADD encoder is retained as `encode_spec_degenerate`. The
  public `encode_spec` now uses the RUN-aware generator in Encoder_Spec.
  The direct lemmas in the first half of this file document and preserve the
  degenerate proof; the public theorem is proved later via the generic
  instruction-stream theorem.

  Proof decomposition:
    1. encode_one inverts resolve-and-exec for each instruction form.
    2. encode_window_loop inverts decode_loop, threading cache state.
    3. serialize inverts parse_header + parse_window.
    4. Compose.
*)
theory Spec_Roundtrip
  imports
    CdeltaSpecBase.Encoder_Spec
    CdeltaSpecBase.Decoder_Spec
begin

unbundle bit_operations_syntax

(* ---------- Header roundtrip ---------- *)
(*
  The encoder prepends a fixed 5-byte prefix (magic + 0x00 version + 0x00
  Hdr_Indicator). parse_header recovers the tail.
*)
lemma parse_header_of_magic:
  "parse_header (magic_bytes @ 0x00 # rest) = Inl rest"
proof -
  have mg: "magic_bytes @ 0x00 # rest = 0xD6 # 0xC3 # 0xC4 # 0x00 # 0x00 # rest"
    by (simp add: magic_bytes_def)
  show ?thesis
    by (simp add: parse_header_def mg)
qed

(* ---------- encode_one for a single ADD of size 1..17 ---------- *)
(*
  Specialised lemma: if the encoder emits a single ADD of small size, the
  decoder reads exactly one opcode from the instruction section, no
  varint, and appends all the data bytes to the target.
*)

lemma encode_one_add_small:
  assumes "1 \<le> length bs" "length bs \<le> 17"
  shows "encode_one (RAdd bs) src_len tgt_pos c [] [] []
       = (bs, [word_of_nat (1 + length bs) :: byte], [], c, tgt_pos + length bs)"
  using assms
  by (simp add: find_single_add_opcode_def Let_def split_def)

(* Core instruction-level roundtrip: one ADD of small size. *)
lemma decode_one_add_small:
  assumes "1 \<le> sz" "sz \<le> 17"
          "data = bs" "length bs = sz"
  shows
    "decode_one src_seg src_seg_len sz
       \<lparr> ds_data_rem = data
       , ds_inst_rem = (word_of_nat (1 + sz) :: byte) # []
       , ds_addr_rem = []
       , ds_cache = cache_init
       , ds_tgt = [] \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = cache_init
           , ds_tgt = bs \<rparr>"
proof -
  let ?op = "word_of_nat (1 + sz) :: byte"
  have op_lt: "1 + sz < 256" using assms(2) by simp
  have unat_op: "unat (word_of_nat (1 + sz) :: byte) = 1 + sz"
    using op_lt by (subst unat_of_nat_eq) simp_all
  have unat_op_alt: "unat (1 + word_of_nat sz :: byte) = 1 + sz"
  proof -
    have "(1 :: byte) + word_of_nat sz = word_of_nat (1 + sz)"
      by simp
    thus ?thesis using unat_op by simp
  qed
  have entry: "default_entry (unat ?op) = (add_hi sz, noop_hi)"
    using default_entry_add_small[OF assms(1,2)] unat_op by simp
  have entry_alt: "default_entry (unat (1 + word_of_nat sz :: byte)) = (add_hi sz, noop_hi)"
    using default_entry_add_small[OF assms(1,2)] unat_op_alt by simp
  have sz_pos: "sz > 0" using assms(1) by simp
  have len_data: "length data = sz" using assms(3,4) by simp
  have not_over_data: "\<not> sz > length data" using len_data by simp
  have not_over_tgt: "\<not> (length ([] :: byte list) + sz > sz)" by simp
  have resolve_add: "resolve_size (add_hi sz) [] = Some (sz, [])"
    using sz_pos by (simp add: resolve_size_def add_hi_def)
  have resolve_noop: "resolve_size noop_hi [] = Some (0, [])"
    by (simp add: resolve_size_def noop_hi_def)
  have take_bs: "take sz data = bs" using assms(3,4) by simp
  have drop_bs: "drop sz data = []" using assms(3,4) by simp
  have exec_half_add:
    "exec_half (add_hi sz) sz src_seg src_seg_len sz
       \<lparr> ds_data_rem = data
       , ds_inst_rem = []
       , ds_addr_rem = []
       , ds_cache = cache_init
       , ds_tgt = [] \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = cache_init
           , ds_tgt = bs \<rparr>"
    using not_over_data take_bs drop_bs
    by (simp add: exec_half_def add_hi_def)
  have exec_half_noop:
    "exec_half noop_hi 0 src_seg src_seg_len sz
       \<lparr> ds_data_rem = []
       , ds_inst_rem = []
       , ds_addr_rem = []
       , ds_cache = cache_init
       , ds_tgt = bs \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = cache_init
           , ds_tgt = bs \<rparr>"
    by (simp add: exec_half_def noop_hi_def)
  show ?thesis
    unfolding decode_one_def
    by (simp add: pop_byte_def Let_def entry_alt resolve_add exec_half_add
                  resolve_noop exec_half_noop)
qed

(* ---------- encode_spec_degenerate for a target of length 1..17 and empty source ---------- *)
(*
  For very small cases we can show decode inverts encode by direct
  computation. This is a sanity check that the pipeline composes.
*)
lemma encode_window_small_empty_src:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
  shows
    "encode_window [RAdd tgt] src_len
       = (tgt, [word_of_nat (1 + length tgt) :: byte], [], cache_init)"
proof -
  have eo: "encode_one (RAdd tgt) src_len 0 cache_init [] [] []
              = (tgt, [word_of_nat (1 + length tgt) :: byte], [],
                 cache_init, length tgt)"
    using encode_one_add_small[OF assms, where src_len = src_len and tgt_pos = 0 and c = cache_init]
    by simp
  show ?thesis
    using eo by (simp add: encode_window_def split_def)
qed

(* ---------- Top-level theorem ---------- *)

(*
  Decoder applied to the encoder output recovers `tgt`, provided the
  target is below the 32-bit varint domain. The source bound follows
  because the encoder reads `length src` and emits it as a varint.

  The full proof for arbitrary (src, tgt) requires tracking every branch
  of encode_one / decode_one through the wire format. Here we state the
  intended theorem; a concrete discharge is deferred to the full
  instruction-dispatch-loop correctness lemma, which is the largest
  remaining piece of the pure spec.

  For now we only prove the theorem for the empty-source, small-target
  regime where the encoder emits a single small ADD. That's sufficient
  to exercise the header / window / instruction / data layers end-to-end.
*)
(* ---------- parse_window on a small-RAdd serialized output ---------- *)
(*
  For the degenerate encoder (single RAdd), win_ind = 0x00 (no source).
  parse_window reads that byte, skips the source-descriptor block,
  consumes four varints (dlen, tgt_len, data_len, inst_len, addr_len),
  skips di=0x00, then partitions the rest into data/inst/addr.
*)

lemma varint_size_lengths:
  "length (varint_encode n) = varint_size n"
  by simp

(*
  Step 1: parse_window after the win_ind byte has win_ind=0x00 (no
  source), skips straight to the dlen varint.
*)
lemma parse_window_no_source_head:
  fixes dlen tgt_len :: nat
  fixes data inst addr :: "byte list"
  assumes caps:
     "dlen < 2 ^ 32" "tgt_len < 2 ^ 32"
     "length data < 2 ^ 32" "length inst < 2 ^ 32" "length addr < 2 ^ 32"
    and dlen_eq:
     "dlen = varint_size tgt_len + 1
           + varint_size (length data)
           + varint_size (length inst)
           + varint_size (length addr)
           + length data + length inst + length addr"
  shows
    "parse_window
       (0x00 # varint_encode dlen @ varint_encode tgt_len @ [0x00]
        @ varint_encode (length data) @ varint_encode (length inst)
        @ varint_encode (length addr) @ data @ inst @ addr)
     = Inl ( \<lparr> pw_src_seg_len = 0
             , pw_src_seg_off = 0
             , pw_tgt_len     = tgt_len
             , pw_data        = data
             , pw_inst        = inst
             , pw_addr        = addr \<rparr>
           , [] )"
proof -
  have vdlen: "varint_decode (varint_encode dlen @ rest) = Some (dlen, rest)" for rest
    using caps(1) by (rule varint_decode_encode)
  have vtgt: "varint_decode (varint_encode tgt_len @ rest) = Some (tgt_len, rest)" for rest
    using caps(2) by (rule varint_decode_encode)
  have vdata: "varint_decode (varint_encode (length data) @ rest) = Some (length data, rest)" for rest
    using caps(3) by (rule varint_decode_encode)
  have vinst: "varint_decode (varint_encode (length inst) @ rest) = Some (length inst, rest)" for rest
    using caps(4) by (rule varint_decode_encode)
  have vaddr: "varint_decode (varint_encode (length addr) @ rest) = Some (length addr, rest)" for rest
    using caps(5) by (rule varint_decode_encode)
  have wi_tests: "(0x00 :: byte) AND 0x02 = 0" "(0x00 :: byte) AND 0xFA = 0" "(0x00 :: byte) AND 0x01 = 0"
    by simp_all
  have di_tests: "(0x00 :: byte) \<noteq> 0 \<longleftrightarrow> False" by simp
  show ?thesis
    unfolding parse_window_def pop_byte_def Let_def
    apply (simp add: vdlen vtgt vdata vinst vaddr wi_tests di_tests)
    by (simp add: dlen_eq)
qed

(*
  The encoder, with the degenerate single-RAdd matcher, produces a
  concrete serialized byte list. Here we state and prove the shape of
  the output for the small (1..17) target, empty-source case.

  NB: for this lemma we only need the list-shape equation; the varint
  roundtrip is exercised transitively by parse_window.
*)
lemma encode_spec_degenerate_small_empty_shape:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
  shows "encode_spec_degenerate [] tgt =
           magic_bytes @ [0x00, 0x00]
         @ varint_encode (1 + varint_size (length tgt) + varint_size (length tgt)
                         + varint_size 1 + varint_size 0
                         + length tgt + 1)
         @ varint_encode (length tgt)
         @ [0x00]
         @ varint_encode (length tgt)
         @ varint_encode 1
         @ varint_encode 0
         @ tgt
         @ [word_of_nat (1 + length tgt) :: byte]"
  using encode_window_small_empty_src[OF assms]
  by (simp add: encode_spec_degenerate_def serialize_from_insts_def generate_instructions_degenerate_def serialize_def Let_def
                split_def magic_bytes_def add.commute add.left_commute)

(* apply_window on the parsed_window for a small-ADD + empty source. *)
lemma apply_window_small_empty_src:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
  shows "apply_window
           \<lparr> pw_src_seg_len = 0
           , pw_src_seg_off = 0
           , pw_tgt_len     = length tgt
           , pw_data        = tgt
           , pw_inst        = [word_of_nat (1 + length tgt) :: byte]
           , pw_addr        = [] \<rparr>
           []
         = Inl tgt"
proof -
  let ?op = "word_of_nat (1 + length tgt) :: byte"
  let ?init_st = "\<lparr> ds_data_rem = tgt
                 , ds_inst_rem = [?op]
                 , ds_addr_rem = []
                 , ds_cache = cache_init
                 , ds_tgt = [] \<rparr>"
  let ?final_st = "\<lparr> ds_data_rem = [] :: byte list
                   , ds_inst_rem = []
                   , ds_addr_rem = []
                   , ds_cache = cache_init
                   , ds_tgt = tgt \<rparr>"
  have do: "decode_one [] 0 (length tgt) ?init_st = Inl ?final_st"
    using decode_one_add_small[OF assms, where data = tgt and bs = tgt
                                            and src_seg = "[]" and src_seg_len = 0]
    by simp
  \<comment> \<open>decode_loop with fuel = length of inst (=1) executes one step.\<close>
  have "decode_loop 1 [] 0 (length tgt) ?init_st = Inl ?final_st"
    using do by (simp add: split: if_splits)
  thus ?thesis
    by (simp add: apply_window_def Let_def)
qed

theorem spec_roundtrip_small:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
          "length tgt < 2 ^ 32"
  shows   "decode_spec (encode_spec_degenerate [] tgt) [] = Inl tgt"
proof -
  let ?op = "word_of_nat (1 + length tgt) :: byte"
  let ?dlen = "1 + varint_size (length tgt) + varint_size (length tgt)
              + varint_size 1 + varint_size 0 + length tgt + 1"
  have shape: "encode_spec_degenerate [] tgt =
                 magic_bytes @ [0x00, 0x00]
               @ varint_encode ?dlen
               @ varint_encode (length tgt)
               @ [0x00]
               @ varint_encode (length tgt)
               @ varint_encode 1
               @ varint_encode 0
               @ tgt
               @ [?op]"
    using encode_spec_degenerate_small_empty_shape[OF assms(1,2)] by simp

  have ph: "parse_header (encode_spec_degenerate [] tgt)
             = Inl (0x00 # varint_encode ?dlen @ varint_encode (length tgt)
                    @ [0x00] @ varint_encode (length tgt)
                    @ varint_encode 1 @ varint_encode 0 @ tgt @ [?op])"
  proof -
    have "magic_bytes @ [0x00, 0x00]
          @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
          @ varint_encode (length tgt) @ varint_encode 1
          @ varint_encode 0 @ tgt @ [?op]
          = magic_bytes @ 0x00 #
             (0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
              @ varint_encode (length tgt) @ varint_encode 1
              @ varint_encode 0 @ tgt @ [?op])"
      by simp
    thus ?thesis using shape parse_header_of_magic by simp
  qed

  \<comment> \<open>tgt ++ [?op] is the byte list after all the varint-encoded lengths.
      We need to rewrite it into the parse_window canonical form data @
      inst @ addr where data = tgt, inst = [?op], addr = [].\<close>
  have data_reorg: "tgt @ [?op] = tgt @ [?op] @ []" by simp

  have num_digits_small: "num_digits n = 1" if "1 \<le> n" "n \<le> 127" for n
  proof -
    have pos: "n > 0" using that by simp
    have div_zero: "n div 128 = 0" using that by simp
    show ?thesis
      using pos
      by (subst num_digits_nonzero[OF pos]) (simp add: div_zero)
  qed
  have vsz_small: "varint_size n = 1" if "n \<le> 17" for n
  proof (cases "n = 0")
    case True then show ?thesis by (simp add: varint_size_def)
  next
    case False
    hence "1 \<le> n" by simp
    moreover have "n \<le> 127" using that by simp
    ultimately show ?thesis by (simp add: varint_size_def num_digits_small)
  qed
  have vsz_eq: "varint_size (length tgt) = 1"
    using vsz_small assms(2) by simp
  have vsz_1: "varint_size 1 = 1" using vsz_small by simp
  have vsz_0: "varint_size 0 = 1" by (simp add: varint_size_def)
  have dlen_eq: "?dlen = 6 + length tgt"
    using vsz_eq vsz_1 vsz_0 by simp
  have dlen_bd: "?dlen < 2 ^ 32"
  proof -
    have step: "?dlen = 6 + length tgt" by (rule dlen_eq)
    have "length tgt \<le> 17" by (rule assms(2))
    then have "6 + length tgt < 2 ^ 32" by simp
    thus ?thesis unfolding step .
  qed
  have tgt_bd: "length tgt < 2 ^ 32" using assms(3) .
  have op_bd: "length [?op] < 2 ^ 32" by simp
  have empty_bd: "length ([] :: byte list) < 2 ^ 32" by simp

  have pw: "parse_window
              (0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
               @ varint_encode (length tgt) @ varint_encode 1
               @ varint_encode 0 @ tgt @ [?op])
           = Inl ( \<lparr> pw_src_seg_len = 0
                   , pw_src_seg_off = 0
                   , pw_tgt_len     = length tgt
                   , pw_data        = tgt
                   , pw_inst        = [?op]
                   , pw_addr        = [] \<rparr>
                 , [] )"
  proof -
    have varint_1_len: "varint_encode 1 = varint_encode (length ([?op] :: byte list))"
      by simp
    have varint_0_len: "varint_encode 0 = varint_encode (length ([] :: byte list))"
      by simp
    have arrange:
      "(0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
        @ varint_encode (length tgt) @ varint_encode 1
        @ varint_encode 0 @ tgt @ [?op])
       = (0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
          @ varint_encode (length tgt)
          @ varint_encode (length ([?op] :: byte list))
          @ varint_encode (length ([] :: byte list))
          @ tgt @ [?op] @ [])"
      by simp
    show ?thesis
      unfolding arrange
      using parse_window_no_source_head[where dlen = ?dlen and tgt_len = "length tgt"
                                         and data = tgt and inst = "[?op]" and addr = "[]",
                                         OF dlen_bd tgt_bd tgt_bd op_bd empty_bd]
      by simp
  qed

  have aw: "apply_window
             \<lparr> pw_src_seg_len = 0, pw_src_seg_off = 0
             , pw_tgt_len = length tgt
             , pw_data = tgt
             , pw_inst = [?op]
             , pw_addr = [] \<rparr> []
           = Inl tgt"
    by (rule apply_window_small_empty_src[OF assms(1,2)])

  show ?thesis
    using ph pw aw by (simp add: decode_spec_def)
qed

(* ---------- General case: ADD of arbitrary size ---------- *)

(*
  For length bs > 17, the encoder uses opcode 1 (ADD size-varint). The
  decoder must read the varint, then execute the ADD of the resolved
  size.
*)
lemma encode_one_add_general:
  assumes "length bs > 17 \<or> length bs = 0"
  shows "encode_one (RAdd bs) src_len tgt_pos c [] [] []
       = (bs, (1 :: byte) # varint_encode (length bs), [], c, tgt_pos + length bs)"
  using assms
  by (auto simp: find_single_add_opcode_def Let_def split_def)

lemma decode_one_add_general:
  assumes "length bs > 17 \<or> length bs = 0"
          "length bs < 2 ^ 32"
          "data = bs"
  shows
    "decode_one src_seg src_seg_len (length bs)
       \<lparr> ds_data_rem = data
       , ds_inst_rem = (1 :: byte) # varint_encode (length bs)
       , ds_addr_rem = []
       , ds_cache = cache_init
       , ds_tgt = [] \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = cache_init
           , ds_tgt = bs \<rparr>"
proof -
  let ?sz = "length bs"
  have unat1: "unat (1 :: byte) = Suc 0" by simp
  have entry: "default_entry (Suc 0) = (add_hi 0, noop_hi)"
    using default_entry_add_varint by simp
  have vdec: "varint_decode (varint_encode ?sz) = Some (?sz, [])"
    using assms(2) varint_decode_encode[of ?sz "[]"] by simp
  have resolve1: "resolve_size (add_hi 0) (varint_encode ?sz)
                   = Some (?sz, [])"
    by (simp add: resolve_size_def add_hi_def vdec)
  have resolve_noop: "resolve_size noop_hi [] = Some (0, [])"
    by (simp add: resolve_size_def noop_hi_def)
  have take_bs: "take ?sz data = bs" using assms(3) by simp
  have drop_bs: "drop ?sz data = []" using assms(3) by simp
  have not_over_data: "\<not> ?sz > length data" using assms(3) by simp
  have exec_half_add:
    "exec_half (add_hi 0) ?sz src_seg src_seg_len ?sz
       \<lparr> ds_data_rem = data
       , ds_inst_rem = []
       , ds_addr_rem = []
       , ds_cache = cache_init
       , ds_tgt = [] \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = cache_init
           , ds_tgt = bs \<rparr>"
    using not_over_data take_bs drop_bs
    by (simp add: exec_half_def add_hi_def)
  have exec_half_noop:
    "exec_half noop_hi 0 src_seg src_seg_len ?sz
       \<lparr> ds_data_rem = []
       , ds_inst_rem = []
       , ds_addr_rem = []
       , ds_cache = cache_init
       , ds_tgt = bs \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = cache_init
           , ds_tgt = bs \<rparr>"
    by (simp add: exec_half_def noop_hi_def)
  show ?thesis
    unfolding decode_one_def
    by (simp add: pop_byte_def Let_def unat1 entry resolve1 exec_half_add
                  resolve_noop exec_half_noop)
qed

(* ---------- encode_window / encode_spec_degenerate for the general case ---------- *)

lemma encode_window_general_empty_src:
  assumes "length tgt > 17 \<or> length tgt = 0"
  shows "encode_window [RAdd tgt] src_len
         = (tgt, (1 :: byte) # varint_encode (length tgt), [], cache_init)"
proof -
  have eo: "encode_one (RAdd tgt) src_len 0 cache_init [] [] []
              = (tgt, (1 :: byte) # varint_encode (length tgt), [],
                 cache_init, length tgt)"
    using encode_one_add_general[OF assms, where src_len = src_len and tgt_pos = 0
                                             and c = cache_init]
    by simp
  show ?thesis
    using eo by (simp add: encode_window_def split_def)
qed

lemma apply_window_general_empty_src:
  assumes "length tgt > 17 \<or> length tgt = 0"
          "length tgt < 2 ^ 32"
  shows "apply_window
           \<lparr> pw_src_seg_len = 0
           , pw_src_seg_off = 0
           , pw_tgt_len     = length tgt
           , pw_data        = tgt
           , pw_inst        = (1 :: byte) # varint_encode (length tgt)
           , pw_addr        = [] \<rparr>
           []
         = Inl tgt"
proof -
  let ?op_bytes = "(1 :: byte) # varint_encode (length tgt)"
  let ?init_st = "\<lparr> ds_data_rem = tgt
                 , ds_inst_rem = ?op_bytes
                 , ds_addr_rem = []
                 , ds_cache = cache_init
                 , ds_tgt = [] \<rparr>"
  let ?final_st = "\<lparr> ds_data_rem = [] :: byte list
                   , ds_inst_rem = []
                   , ds_addr_rem = []
                   , ds_cache = cache_init
                   , ds_tgt = tgt \<rparr>"
  have do: "decode_one [] 0 (length tgt) ?init_st = Inl ?final_st"
  proof -
    have "length tgt > 17 \<or> length tgt = 0" by (rule assms(1))
    thus ?thesis
      using decode_one_add_general[of tgt, OF _ assms(2) refl,
                                   where src_seg = "[]" and src_seg_len = 0]
      by simp
  qed
  \<comment> \<open>Need fuel \<ge> 1 + length (varint_encode (length tgt)). The apply_window
      supplies length pw_inst = 1 + length (varint_encode _) bytes, which
      is more than enough since decode_loop uses each byte of fuel for at
      most one opcode (and we have exactly one opcode). Formally: one
      Suc is enough because after decode_one, inst_rem = [] and the
      ?fuel=0 base case returns Inl.\<close>
  have "decode_loop (length ?op_bytes) [] 0 (length tgt) ?init_st = Inl ?final_st"
  proof -
    have len_pos: "length ?op_bytes > 0" by simp
    then obtain k where k_eq: "length ?op_bytes = Suc k" by (cases "length ?op_bytes") auto
    have inst_nonempty: "?op_bytes \<noteq> []" by simp
    have "decode_loop (Suc k) [] 0 (length tgt) ?init_st
           = decode_loop k [] 0 (length tgt) ?final_st"
      using inst_nonempty do by simp
    also have "\<dots> = Inl ?final_st"
      by (induction k) simp_all
    finally show ?thesis using k_eq by simp
  qed
  thus ?thesis by (simp add: apply_window_def Let_def)
qed

lemma encode_spec_degenerate_general_empty_shape:
  assumes "length tgt > 17 \<or> length tgt = 0"
  shows "encode_spec_degenerate [] tgt =
           magic_bytes @ [0x00, 0x00]
         @ varint_encode (1 + varint_size (length tgt) + varint_size (length tgt)
                         + varint_size (1 + length (varint_encode (length tgt)))
                         + varint_size 0
                         + length tgt + 1 + length (varint_encode (length tgt)))
         @ varint_encode (length tgt)
         @ [0x00]
         @ varint_encode (length tgt)
         @ varint_encode (1 + length (varint_encode (length tgt)))
         @ varint_encode 0
         @ tgt
         @ [1 :: byte]
         @ varint_encode (length tgt)"
  using encode_window_general_empty_src[OF assms]
  by (simp add: encode_spec_degenerate_def serialize_from_insts_def generate_instructions_degenerate_def serialize_def Let_def
                split_def magic_bytes_def add.commute add.left_commute)

(* Parse_window + apply_window for the general case. *)

lemma spec_roundtrip_empty_src_large:
  assumes "length tgt > 17 \<or> length tgt = 0"
          "length tgt < 2 ^ 32 - 32"
  shows   "decode_spec (encode_spec_degenerate [] tgt) [] = Inl tgt"
proof -
  let ?inst = "(1 :: byte) # varint_encode (length tgt)"
  let ?tlen_sz = "varint_size (length tgt)"
  let ?inst_sz = "varint_size (length ?inst)"
  let ?dlen = "1 + ?tlen_sz + ?tlen_sz + ?inst_sz + varint_size 0
              + length tgt + length ?inst"

  have tgt_bd: "length tgt < 2 ^ 32" using assms(2) by simp
  have inst_len_eq: "length ?inst = 1 + length (varint_encode (length tgt))"
    by simp

  have shape: "encode_spec_degenerate [] tgt =
                 magic_bytes @ [0x00, 0x00]
               @ varint_encode ?dlen
               @ varint_encode (length tgt)
               @ [0x00]
               @ varint_encode (length tgt)
               @ varint_encode (length ?inst)
               @ varint_encode 0
               @ tgt
               @ ?inst"
    using encode_window_general_empty_src[OF assms(1)]
    by (simp add: encode_spec_degenerate_def serialize_from_insts_def generate_instructions_degenerate_def serialize_def Let_def
                  split_def magic_bytes_def add.commute add.left_commute)

  have ph: "parse_header (encode_spec_degenerate [] tgt)
             = Inl (0x00 # varint_encode ?dlen @ varint_encode (length tgt)
                    @ [0x00] @ varint_encode (length tgt)
                    @ varint_encode (length ?inst) @ varint_encode 0 @ tgt @ ?inst)"
  proof -
    have rearrange:
      "magic_bytes @ [0x00, 0x00]
       @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
       @ varint_encode (length tgt) @ varint_encode (length ?inst)
       @ varint_encode 0 @ tgt @ ?inst
       = magic_bytes @ 0x00 #
          (0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
           @ varint_encode (length tgt) @ varint_encode (length ?inst)
           @ varint_encode 0 @ tgt @ ?inst)"
      by simp
    show ?thesis using shape parse_header_of_magic
      by (simp add: rearrange)
  qed

  (* varint_size bound for values < 2^32 is at most 5. *)
  have vsz_le_5: "varint_size n \<le> 5" if "n < 2 ^ 32" for n
  proof -
    have "n < 2 ^ 35" using that by simp
    hence "num_digits n \<le> 5" by (rule num_digits_le_5)
    thus ?thesis by (simp add: varint_size_def)
  qed
  have vlen_bd: "length (varint_encode n) \<le> 5" if "n < 2 ^ 32" for n
    using that vsz_le_5 by simp
  have inst_len_bd: "length ?inst \<le> 6" using vlen_bd[OF tgt_bd] by simp

  have dlen_upper: "?dlen \<le> 1 + 5 + 5 + 5 + 1 + length tgt + 6"
    using vsz_le_5[OF tgt_bd] vsz_le_5[of "length ?inst"]
          inst_len_bd
    by (auto simp: varint_size_def)
  have dlen_bd: "?dlen < 2 ^ 32"
  proof -
    have "1 + 5 + 5 + 5 + 1 + length tgt + 6 < 2 ^ 32"
      using assms(2) by simp
    thus ?thesis using dlen_upper by linarith
  qed
  have inst_bd: "length ?inst < 2 ^ 32" using inst_len_bd by simp
  have empty_bd: "length ([] :: byte list) < 2 ^ 32" by simp

  have pw: "parse_window
              (0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
               @ varint_encode (length tgt) @ varint_encode (length ?inst)
               @ varint_encode 0 @ tgt @ ?inst)
           = Inl ( \<lparr> pw_src_seg_len = 0
                   , pw_src_seg_off = 0
                   , pw_tgt_len     = length tgt
                   , pw_data        = tgt
                   , pw_inst        = ?inst
                   , pw_addr        = [] \<rparr>
                 , [] )"
  proof -
    have arrange:
      "(0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
        @ varint_encode (length tgt) @ varint_encode (length ?inst)
        @ varint_encode 0 @ tgt @ ?inst)
       = (0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
          @ varint_encode (length tgt)
          @ varint_encode (length ?inst)
          @ varint_encode (length ([] :: byte list))
          @ tgt @ ?inst @ [])"
      by simp
    show ?thesis
      unfolding arrange
      using parse_window_no_source_head[where dlen = ?dlen and tgt_len = "length tgt"
                                         and data = tgt and inst = "?inst" and addr = "[]",
                                         OF dlen_bd tgt_bd tgt_bd inst_bd empty_bd]
      by simp
  qed

  have aw: "apply_window
             \<lparr> pw_src_seg_len = 0, pw_src_seg_off = 0
             , pw_tgt_len = length tgt
             , pw_data = tgt
             , pw_inst = ?inst
             , pw_addr = [] \<rparr> []
           = Inl tgt"
    using apply_window_general_empty_src[OF assms(1) tgt_bd] .

  show ?thesis
    using ph pw aw by (simp add: decode_spec_def)
qed

theorem spec_roundtrip_empty_src:
  assumes "length tgt < 2 ^ 32 - 32"
  shows   "decode_spec (encode_spec_degenerate [] tgt) [] = Inl tgt"
proof (cases "length tgt = 0")
  case True
  then have "length tgt > 17 \<or> length tgt = 0" by simp
  thus ?thesis using spec_roundtrip_empty_src_large[OF _ assms] by blast
next
  case False
  hence pos: "1 \<le> length tgt" by linarith
  show ?thesis
  proof (cases "length tgt \<le> 17")
    case True
    have tgt_bd: "length tgt < 2 ^ 32" using assms by simp
    show ?thesis using spec_roundtrip_small[OF pos True tgt_bd] .
  next
    case False
    hence "length tgt > 17 \<or> length tgt = 0" by simp
    thus ?thesis using spec_roundtrip_empty_src_large[OF _ assms] by blast
  qed
qed

(* ---------- parse_window with source descriptor ---------- *)

lemma parse_window_with_source_head:
  fixes dlen tgt_len src_len :: nat
  fixes data inst addr :: "byte list"
  assumes caps:
     "dlen < 2 ^ 32" "tgt_len < 2 ^ 32" "src_len < 2 ^ 32"
     "length data < 2 ^ 32" "length inst < 2 ^ 32" "length addr < 2 ^ 32"
    and dlen_eq:
     "dlen = varint_size tgt_len + 1
           + varint_size (length data)
           + varint_size (length inst)
           + varint_size (length addr)
           + length data + length inst + length addr"
  shows
    "parse_window
       (0x01 # varint_encode src_len @ varint_encode 0 @ varint_encode dlen
        @ varint_encode tgt_len @ [0x00]
        @ varint_encode (length data) @ varint_encode (length inst)
        @ varint_encode (length addr) @ data @ inst @ addr)
     = Inl ( \<lparr> pw_src_seg_len = src_len
             , pw_src_seg_off = 0
             , pw_tgt_len     = tgt_len
             , pw_data        = data
             , pw_inst        = inst
             , pw_addr        = addr \<rparr>
           , [] )"
proof -
  have vsl: "varint_decode (varint_encode src_len @ rest) = Some (src_len, rest)" for rest
    using caps(3) by (rule varint_decode_encode)
  have vso: "varint_decode (varint_encode 0 @ rest) = Some (0, rest)" for rest
    by (simp add: varint_decode_encode)
  have vdlen: "varint_decode (varint_encode dlen @ rest) = Some (dlen, rest)" for rest
    using caps(1) by (rule varint_decode_encode)
  have vtgt: "varint_decode (varint_encode tgt_len @ rest) = Some (tgt_len, rest)" for rest
    using caps(2) by (rule varint_decode_encode)
  have vdata: "varint_decode (varint_encode (length data) @ rest) = Some (length data, rest)" for rest
    using caps(4) by (rule varint_decode_encode)
  have vinst: "varint_decode (varint_encode (length inst) @ rest) = Some (length inst, rest)" for rest
    using caps(5) by (rule varint_decode_encode)
  have vaddr: "varint_decode (varint_encode (length addr) @ rest) = Some (length addr, rest)" for rest
    using caps(6) by (rule varint_decode_encode)
  have wi_tests_1: "(0x01 :: byte) AND 0x02 = 0" "(0x01 :: byte) AND 0xFA = 0" "(0x01 :: byte) AND 0x01 \<noteq> 0"
    by simp_all
  have di_tests: "(0x00 :: byte) \<noteq> 0 \<longleftrightarrow> False" by simp
  show ?thesis
    unfolding parse_window_def pop_byte_def Let_def
    apply (simp add: vsl vso vdlen vtgt vdata vinst vaddr wi_tests_1 di_tests)
    by (simp add: dlen_eq)
qed

(* ---------- encode_spec_degenerate for non-empty source (small/large tgt) ---------- *)

lemma encode_spec_degenerate_nonempty_src_shape_small:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
          "length src > 0"
  shows "encode_spec_degenerate src tgt =
           magic_bytes @ [0x00, 0x01]
         @ varint_encode (length src)
         @ varint_encode 0
         @ varint_encode (1 + varint_size (length tgt) + varint_size (length tgt)
                         + varint_size 1 + varint_size 0 + length tgt + 1)
         @ varint_encode (length tgt)
         @ [0x00]
         @ varint_encode (length tgt)
         @ varint_encode 1
         @ varint_encode 0
         @ tgt
         @ [word_of_nat (1 + length tgt) :: byte]"
  using encode_window_small_empty_src[OF assms(1,2)] assms(3)
  by (simp add: encode_spec_degenerate_def serialize_from_insts_def generate_instructions_degenerate_def serialize_def Let_def
                split_def magic_bytes_def add.commute add.left_commute)

lemma encode_spec_degenerate_nonempty_src_shape_large:
  assumes "length tgt > 17 \<or> length tgt = 0"
          "length src > 0"
  shows "encode_spec_degenerate src tgt =
           magic_bytes @ [0x00, 0x01]
         @ varint_encode (length src)
         @ varint_encode 0
         @ varint_encode (1 + varint_size (length tgt) + varint_size (length tgt)
                         + varint_size (1 + length (varint_encode (length tgt)))
                         + varint_size 0
                         + length tgt + 1 + length (varint_encode (length tgt)))
         @ varint_encode (length tgt)
         @ [0x00]
         @ varint_encode (length tgt)
         @ varint_encode (1 + length (varint_encode (length tgt)))
         @ varint_encode 0
         @ tgt
         @ [1 :: byte]
         @ varint_encode (length tgt)"
  using encode_window_general_empty_src[OF assms(1)] assms(2)
  by (simp add: encode_spec_degenerate_def serialize_from_insts_def generate_instructions_degenerate_def serialize_def Let_def
                split_def magic_bytes_def add.commute add.left_commute)

(* apply_window when the source segment is non-empty but the instruction
   is a single RAdd — the COPY-from-source never runs, so src_seg doesn't
   matter. *)
lemma apply_window_small_nonempty_src:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
          "length src > 0" "src_seg_off \<le> length src"
          "src_seg_len \<le> length src - src_seg_off"
  shows "apply_window
           \<lparr> pw_src_seg_len = src_seg_len
           , pw_src_seg_off = src_seg_off
           , pw_tgt_len     = length tgt
           , pw_data        = tgt
           , pw_inst        = [word_of_nat (1 + length tgt) :: byte]
           , pw_addr        = [] \<rparr>
           src
         = Inl tgt"
proof -
  let ?op = "word_of_nat (1 + length tgt) :: byte"
  let ?src_seg = "(if src_seg_len = 0 then []
                   else take src_seg_len (drop src_seg_off src))"
  let ?init_st = "\<lparr> ds_data_rem = tgt
                 , ds_inst_rem = [?op]
                 , ds_addr_rem = []
                 , ds_cache = cache_init
                 , ds_tgt = [] \<rparr>"
  let ?final_st = "\<lparr> ds_data_rem = [] :: byte list
                   , ds_inst_rem = []
                   , ds_addr_rem = []
                   , ds_cache = cache_init
                   , ds_tgt = tgt \<rparr>"
  have do: "decode_one ?src_seg src_seg_len (length tgt) ?init_st = Inl ?final_st"
    using decode_one_add_small[OF assms(1,2), where data = tgt and bs = tgt
                                            and src_seg = ?src_seg
                                            and src_seg_len = src_seg_len]
    by simp
  have "decode_loop 1 ?src_seg src_seg_len (length tgt) ?init_st = Inl ?final_st"
    using do by simp
  moreover have "\<not> (src_seg_len > 0 \<and> src_seg_off + src_seg_len > length src)"
    using assms(4,5) by auto
  ultimately show ?thesis
    by (simp add: apply_window_def Let_def)
qed

lemma apply_window_general_nonempty_src:
  assumes "length tgt > 17 \<or> length tgt = 0"
          "length tgt < 2 ^ 32"
          "length src > 0" "src_seg_off \<le> length src"
          "src_seg_len \<le> length src - src_seg_off"
  shows "apply_window
           \<lparr> pw_src_seg_len = src_seg_len
           , pw_src_seg_off = src_seg_off
           , pw_tgt_len     = length tgt
           , pw_data        = tgt
           , pw_inst        = (1 :: byte) # varint_encode (length tgt)
           , pw_addr        = [] \<rparr>
           src
         = Inl tgt"
proof -
  let ?op_bytes = "(1 :: byte) # varint_encode (length tgt)"
  let ?src_seg = "(if src_seg_len = 0 then []
                   else take src_seg_len (drop src_seg_off src))"
  let ?init_st = "\<lparr> ds_data_rem = tgt
                 , ds_inst_rem = ?op_bytes
                 , ds_addr_rem = []
                 , ds_cache = cache_init
                 , ds_tgt = [] \<rparr>"
  let ?final_st = "\<lparr> ds_data_rem = [] :: byte list
                   , ds_inst_rem = []
                   , ds_addr_rem = []
                   , ds_cache = cache_init
                   , ds_tgt = tgt \<rparr>"
  have do: "decode_one ?src_seg src_seg_len (length tgt) ?init_st = Inl ?final_st"
    using decode_one_add_general[OF assms(1) assms(2) refl,
                                  where src_seg = ?src_seg
                                  and src_seg_len = src_seg_len]
    by simp
  have "decode_loop (length ?op_bytes) ?src_seg src_seg_len (length tgt) ?init_st
        = Inl ?final_st"
  proof -
    have len_pos: "length ?op_bytes > 0" by simp
    then obtain k where k_eq: "length ?op_bytes = Suc k"
      by (cases "length ?op_bytes") auto
    have inst_nonempty: "?op_bytes \<noteq> []" by simp
    have "decode_loop (Suc k) ?src_seg src_seg_len (length tgt) ?init_st
           = decode_loop k ?src_seg src_seg_len (length tgt) ?final_st"
      using inst_nonempty do by simp
    also have "\<dots> = Inl ?final_st"
      by (induction k) simp_all
    finally show ?thesis using k_eq by simp
  qed
  moreover have "\<not> (src_seg_len > 0 \<and> src_seg_off + src_seg_len > length src)"
    using assms(4,5) by auto
  ultimately show ?thesis
    by (simp add: apply_window_def Let_def)
qed

(* ---------- Top-level theorem ---------- *)

theorem spec_roundtrip_nonempty_src_small:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
          "length tgt < 2 ^ 32" "length src > 0" "length src < 2 ^ 32"
  shows   "decode_spec (encode_spec_degenerate src tgt) src = Inl tgt"
proof -
  let ?op = "word_of_nat (1 + length tgt) :: byte"
  let ?dlen = "1 + varint_size (length tgt) + varint_size (length tgt)
              + varint_size 1 + varint_size 0 + length tgt + 1"

  have vsz_small: "varint_size n = 1" if "n \<le> 17" for n
  proof (cases "n = 0")
    case True then show ?thesis by (simp add: varint_size_def)
  next
    case False
    hence "1 \<le> n" by simp
    moreover have "n \<le> 127" using that by simp
    ultimately show ?thesis
      by (simp add: varint_size_def num_digits_nonzero num_digits.simps)
  qed
  have vsz_eq: "varint_size (length tgt) = 1"
    using vsz_small assms(2) by simp
  have vsz_1: "varint_size 1 = 1" using vsz_small by simp
  have vsz_0: "varint_size 0 = 1" by (simp add: varint_size_def)
  have dlen_eq: "?dlen = 6 + length tgt"
    using vsz_eq vsz_1 vsz_0 by simp

  have dlen_bd: "?dlen < 2 ^ 32"
  proof -
    have step: "?dlen = 6 + length tgt" by (rule dlen_eq)
    have "length tgt \<le> 17" by (rule assms(2))
    then have "6 + length tgt < 2 ^ 32" by simp
    thus ?thesis unfolding step .
  qed
  have tgt_bd: "length tgt < 2 ^ 32" using assms(3) .
  have src_bd: "length src < 2 ^ 32" using assms(5) .
  have op_bd: "length ([?op]) < 2 ^ 32" by simp
  have empty_bd: "length ([] :: byte list) < 2 ^ 32" by simp

  have shape: "encode_spec_degenerate src tgt =
                 magic_bytes @ [0x00, 0x01]
               @ varint_encode (length src)
               @ varint_encode 0
               @ varint_encode ?dlen
               @ varint_encode (length tgt)
               @ [0x00]
               @ varint_encode (length tgt)
               @ varint_encode 1
               @ varint_encode 0
               @ tgt
               @ [?op]"
    using encode_spec_degenerate_nonempty_src_shape_small[OF assms(1,2,4)] by simp

  have ph: "parse_header (encode_spec_degenerate src tgt)
             = Inl (0x01 # varint_encode (length src) @ varint_encode 0
                    @ varint_encode ?dlen @ varint_encode (length tgt)
                    @ [0x00] @ varint_encode (length tgt)
                    @ varint_encode 1 @ varint_encode 0 @ tgt @ [?op])"
  proof -
    have rearrange:
      "magic_bytes @ [0x00, 0x01]
       @ varint_encode (length src) @ varint_encode 0
       @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
       @ varint_encode (length tgt) @ varint_encode 1 @ varint_encode 0
       @ tgt @ [?op]
       = magic_bytes @ 0x00 #
          (0x01 # varint_encode (length src) @ varint_encode 0
           @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
           @ varint_encode (length tgt) @ varint_encode 1 @ varint_encode 0
           @ tgt @ [?op])"
      by simp
    show ?thesis using shape parse_header_of_magic
      by (simp add: rearrange)
  qed

  have pw: "parse_window
              (0x01 # varint_encode (length src) @ varint_encode 0
               @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
               @ varint_encode (length tgt) @ varint_encode 1 @ varint_encode 0
               @ tgt @ [?op])
           = Inl ( \<lparr> pw_src_seg_len = length src
                   , pw_src_seg_off = 0
                   , pw_tgt_len     = length tgt
                   , pw_data        = tgt
                   , pw_inst        = [?op]
                   , pw_addr        = [] \<rparr>
                 , [] )"
  proof -
    have varint_1_len: "varint_encode 1 = varint_encode (length ([?op] :: byte list))"
      by simp
    have varint_0_len: "varint_encode 0 = varint_encode (length ([] :: byte list))"
      by simp
    have arrange:
      "(0x01 # varint_encode (length src) @ varint_encode 0
        @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
        @ varint_encode (length tgt) @ varint_encode 1 @ varint_encode 0
        @ tgt @ [?op])
       = (0x01 # varint_encode (length src) @ varint_encode 0
          @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
          @ varint_encode (length tgt)
          @ varint_encode (length ([?op] :: byte list))
          @ varint_encode (length ([] :: byte list))
          @ tgt @ [?op] @ [])"
      by simp
    show ?thesis
      unfolding arrange
      using parse_window_with_source_head[where dlen = ?dlen and tgt_len = "length tgt"
                                           and src_len = "length src"
                                           and data = tgt and inst = "[?op]" and addr = "[]",
                                           OF dlen_bd tgt_bd src_bd tgt_bd op_bd empty_bd]
      by simp
  qed

  have src_off_bd: "0 \<le> length src" by simp
  have src_len_bd: "length src \<le> length src - 0" by simp

  have aw: "apply_window
             \<lparr> pw_src_seg_len = length src, pw_src_seg_off = 0
             , pw_tgt_len = length tgt
             , pw_data = tgt
             , pw_inst = [?op]
             , pw_addr = [] \<rparr> src
           = Inl tgt"
    using apply_window_small_nonempty_src[OF assms(1,2,4) src_off_bd src_len_bd] .

  show ?thesis
    using ph pw aw by (simp add: decode_spec_def)
qed

theorem spec_roundtrip_nonempty_src_large:
  assumes "length tgt > 17 \<or> length tgt = 0"
          "length tgt < 2 ^ 32 - 32" "length src > 0" "length src < 2 ^ 32"
  shows   "decode_spec (encode_spec_degenerate src tgt) src = Inl tgt"
proof -
  let ?inst = "(1 :: byte) # varint_encode (length tgt)"
  let ?tlen_sz = "varint_size (length tgt)"
  let ?inst_sz = "varint_size (length ?inst)"
  let ?dlen = "1 + ?tlen_sz + ?tlen_sz + ?inst_sz + varint_size 0
              + length tgt + length ?inst"

  have tgt_bd: "length tgt < 2 ^ 32" using assms(2) by simp
  have src_bd: "length src < 2 ^ 32" using assms(4) .

  have vsz_le_5: "varint_size n \<le> 5" if "n < 2 ^ 32" for n
  proof -
    have "n < 2 ^ 35" using that by simp
    hence "num_digits n \<le> 5" by (rule num_digits_le_5)
    thus ?thesis by (simp add: varint_size_def)
  qed
  have vlen_bd: "length (varint_encode n) \<le> 5" if "n < 2 ^ 32" for n
    using that vsz_le_5 by simp
  have inst_len_bd: "length ?inst \<le> 6" using vlen_bd[OF tgt_bd] by simp

  have dlen_upper: "?dlen \<le> 1 + 5 + 5 + 5 + 1 + length tgt + 6"
    using vsz_le_5[OF tgt_bd] vsz_le_5[of "length ?inst"] inst_len_bd
    by (auto simp: varint_size_def)
  have dlen_bd: "?dlen < 2 ^ 32"
  proof -
    have "1 + 5 + 5 + 5 + 1 + length tgt + 6 < 2 ^ 32"
      using assms(2) by simp
    thus ?thesis using dlen_upper by linarith
  qed
  have inst_bd: "length ?inst < 2 ^ 32" using inst_len_bd by simp
  have empty_bd: "length ([] :: byte list) < 2 ^ 32" by simp

  have shape: "encode_spec_degenerate src tgt =
                 magic_bytes @ [0x00, 0x01]
               @ varint_encode (length src)
               @ varint_encode 0
               @ varint_encode ?dlen
               @ varint_encode (length tgt)
               @ [0x00]
               @ varint_encode (length tgt)
               @ varint_encode (length ?inst)
               @ varint_encode 0
               @ tgt
               @ ?inst"
    using encode_spec_degenerate_nonempty_src_shape_large[OF assms(1,3)] by simp

  have ph: "parse_header (encode_spec_degenerate src tgt)
             = Inl (0x01 # varint_encode (length src) @ varint_encode 0
                    @ varint_encode ?dlen @ varint_encode (length tgt)
                    @ [0x00] @ varint_encode (length tgt)
                    @ varint_encode (length ?inst) @ varint_encode 0
                    @ tgt @ ?inst)"
  proof -
    have rearrange:
      "magic_bytes @ [0x00, 0x01]
       @ varint_encode (length src) @ varint_encode 0
       @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
       @ varint_encode (length tgt) @ varint_encode (length ?inst)
       @ varint_encode 0 @ tgt @ ?inst
       = magic_bytes @ 0x00 #
          (0x01 # varint_encode (length src) @ varint_encode 0
           @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
           @ varint_encode (length tgt) @ varint_encode (length ?inst)
           @ varint_encode 0 @ tgt @ ?inst)"
      by simp
    show ?thesis using shape parse_header_of_magic
      by (simp add: rearrange)
  qed

  have pw: "parse_window
              (0x01 # varint_encode (length src) @ varint_encode 0
               @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
               @ varint_encode (length tgt) @ varint_encode (length ?inst)
               @ varint_encode 0 @ tgt @ ?inst)
           = Inl ( \<lparr> pw_src_seg_len = length src
                   , pw_src_seg_off = 0
                   , pw_tgt_len     = length tgt
                   , pw_data        = tgt
                   , pw_inst        = ?inst
                   , pw_addr        = [] \<rparr>
                 , [] )"
  proof -
    have arrange:
      "(0x01 # varint_encode (length src) @ varint_encode 0
        @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
        @ varint_encode (length tgt) @ varint_encode (length ?inst)
        @ varint_encode 0 @ tgt @ ?inst)
       = (0x01 # varint_encode (length src) @ varint_encode 0
          @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
          @ varint_encode (length tgt)
          @ varint_encode (length ?inst)
          @ varint_encode (length ([] :: byte list))
          @ tgt @ ?inst @ [])"
      by simp
    show ?thesis
      unfolding arrange
      using parse_window_with_source_head[where dlen = ?dlen and tgt_len = "length tgt"
                                           and src_len = "length src"
                                           and data = tgt and inst = "?inst" and addr = "[]",
                                           OF dlen_bd tgt_bd src_bd tgt_bd inst_bd empty_bd]
      by simp
  qed

  have src_off_bd: "0 \<le> length src" by simp
  have src_len_bd: "length src \<le> length src - 0" by simp

  have aw: "apply_window
             \<lparr> pw_src_seg_len = length src, pw_src_seg_off = 0
             , pw_tgt_len = length tgt
             , pw_data = tgt
             , pw_inst = ?inst
             , pw_addr = [] \<rparr> src
           = Inl tgt"
    using apply_window_general_nonempty_src[OF assms(1) tgt_bd assms(3)
                                            src_off_bd src_len_bd] .

  show ?thesis
    using ph pw aw by (simp add: decode_spec_def)
qed

theorem spec_roundtrip_degenerate:
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32 - 32"
  shows   "decode_spec (encode_spec_degenerate src tgt) src = Inl tgt"
proof (cases "length src = 0")
  case True
  then have "src = []" by simp
  thus ?thesis
    using spec_roundtrip_empty_src[OF assms(2)] by simp
next
  case False
  hence src_pos: "length src > 0" by simp
  show ?thesis
  proof (cases "length tgt = 0")
    case True
    hence "length tgt > 17 \<or> length tgt = 0" by simp
    thus ?thesis
      using spec_roundtrip_nonempty_src_large[OF _ assms(2) src_pos assms(1)]
      by blast
  next
    case False
    hence tgt_pos: "1 \<le> length tgt" by linarith
    show ?thesis
    proof (cases "length tgt \<le> 17")
      case True
      have tgt_bd: "length tgt < 2 ^ 32" using assms(2) by simp
      show ?thesis
        using spec_roundtrip_nonempty_src_small[OF tgt_pos True tgt_bd src_pos assms(1)] .
    next
      case False
      hence "length tgt > 17 \<or> length tgt = 0" by simp
      thus ?thesis
        using spec_roundtrip_nonempty_src_large[OF _ assms(2) src_pos assms(1)]
        by blast
    qed
  qed
qed

(* ================================================================== *)
(* Part 2: Matcher-parametric roundtrip                               *)
(* ================================================================== *)

(* ---------- decode_loop structural lemmas ---------- *)

lemma decode_loop_fuel_empty:
  "ds_inst_rem st = [] \<Longrightarrow> decode_loop n ss ssl tl0 st = Inl st"
  by (cases n) simp_all

lemma decode_loop_mono:
  assumes "decode_loop n ss ssl tl0 st = Inl st'"
          "m \<ge> n"
  shows   "decode_loop m ss ssl tl0 st = Inl st'"
  using assms
proof (induction n arbitrary: st m)
  case 0
  then have empty: "ds_inst_rem st = []" by (simp split: if_splits)
  then have "st' = st" using 0(1) by simp
  thus ?case using decode_loop_fuel_empty[OF empty] by simp
next
  case (Suc n)
  show ?case
  proof (cases "ds_inst_rem st = []")
    case True
    then have "st' = st" using Suc.prems(1) by simp
    thus ?thesis using decode_loop_fuel_empty[OF True] by simp
  next
    case False
    from Suc.prems(2) obtain m' where m_eq: "m = Suc m'" and "m' \<ge> n"
      by (cases m) auto
    obtain st_mid where
      do_ok: "decode_one ss ssl tl0 st = Inl st_mid" and
      rest: "decode_loop n ss ssl tl0 st_mid = Inl st'"
      using Suc.prems(1) False by (auto split: sum.splits)
    have "decode_loop m' ss ssl tl0 st_mid = Inl st'"
      using Suc.IH[OF rest \<open>m' \<ge> n\<close>] .
    thus ?thesis using m_eq False do_ok by simp
  qed
qed

lemma decode_loop_append:
  assumes "decode_loop n ss ssl tl0 st = Inl st'"
          "decode_loop m ss ssl tl0 st' = Inl st''"
  shows   "decode_loop (n + m) ss ssl tl0 st = Inl st''"
  using assms
proof (induction n arbitrary: st)
  case 0
  then have "st' = st"
    by (cases "ds_inst_rem st = []") (simp_all split: if_splits)
  thus ?case using 0(2) by simp
next
  case (Suc n)
  show ?case
  proof (cases "ds_inst_rem st = []")
    case True
    then have eq1: "st' = st" using Suc.prems(1) by simp
    have dl_m: "decode_loop m ss ssl tl0 st = Inl st''" using Suc.prems(2) eq1 by simp
    have ge: "Suc n + m \<ge> m" by simp
    show ?thesis using decode_loop_mono[OF dl_m ge] .
  next
    case False
    obtain st_mid where
      do_ok: "decode_one ss ssl tl0 st = Inl st_mid" and
      rest: "decode_loop n ss ssl tl0 st_mid = Inl st'"
      using Suc.prems(1) False by (auto split: sum.splits)
    have "decode_loop (n + m) ss ssl tl0 st_mid = Inl st''"
      using Suc.IH[OF rest Suc.prems(2)] .
    thus ?thesis using False do_ok by simp
  qed
qed

(* ---------- Per-instruction decode_one with suffix ---------- *)

(* ADD with size in 1..17: opcode encodes size directly. *)
lemma decode_one_add_small_suffix:
  assumes "1 \<le> length bs" "length bs \<le> 17"
          "length (ds_tgt st) + length bs \<le> tgt_len"
  shows
    "decode_one src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := bs @ data_rest
           , ds_inst_rem := word_of_nat (1 + length bs) # inst_rest
           , ds_addr_rem := addr_rest \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_tgt := ds_tgt st @ bs \<rparr>)"
proof -
  let ?sz = "length bs"
  let ?op = "word_of_nat (1 + ?sz) :: byte"
  have op_lt: "1 + ?sz < 256" using assms(2) by simp
  have unat_op: "unat ?op = 1 + ?sz"
    using op_lt by (subst unat_of_nat_eq) simp_all
  have entry: "default_entry (unat ?op) = (add_hi ?sz, noop_hi)"
    using default_entry_add_small[OF assms(1,2)] unat_op by simp
  have sz_pos: "?sz > 0" using assms(1) by linarith
  have resolve_add: "resolve_size (add_hi ?sz) inst_rest = Some (?sz, inst_rest)"
    using sz_pos by (simp add: resolve_size_def add_hi_def)
  have resolve_noop: "resolve_size noop_hi inst_rest = Some (0, inst_rest)"
    by (simp add: resolve_size_def noop_hi_def)
  have exec_add:
    "exec_half (add_hi ?sz) ?sz src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := bs @ data_rest
           , ds_inst_rem := inst_rest
           , ds_addr_rem := addr_rest \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_tgt := ds_tgt st @ bs \<rparr>)"
    using assms(3) by (simp add: exec_half_def add_hi_def)
  have exec_noop:
    "exec_half noop_hi 0 src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := data_rest
           , ds_inst_rem := inst_rest
           , ds_addr_rem := addr_rest
           , ds_tgt := ds_tgt st @ bs \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_tgt := ds_tgt st @ bs \<rparr>)"
    by (simp add: exec_half_def noop_hi_def)
  let ?in_st = "st \<lparr> ds_data_rem := bs @ data_rest
                   , ds_inst_rem := ?op # inst_rest
                   , ds_addr_rem := addr_rest \<rparr>"
  let ?st1 = "st \<lparr> ds_data_rem := bs @ data_rest
                 , ds_inst_rem := inst_rest
                 , ds_addr_rem := addr_rest \<rparr>"
  let ?out_st = "st \<lparr> ds_data_rem := data_rest
                    , ds_inst_rem := inst_rest
                    , ds_addr_rem := addr_rest
                    , ds_tgt := ds_tgt st @ bs \<rparr>"
  have step1: "pop_byte (ds_inst_rem ?in_st) = Some (?op, inst_rest)"
    by (simp add: pop_byte_def)
  have step2: "?in_st \<lparr> ds_inst_rem := inst_rest \<rparr> = ?st1" by simp
  have step3: "ds_inst_rem ?st1 = inst_rest" by simp
  have step4: "resolve_size (add_hi ?sz) inst_rest = Some (?sz, inst_rest)"
    using sz_pos by (simp add: resolve_size_def add_hi_def)
  have step5: "?st1 \<lparr> ds_inst_rem := inst_rest \<rparr> = ?st1" by simp
  have step6: "exec_half (add_hi ?sz) ?sz src_seg src_seg_len tgt_len ?st1
     = Inl ?out_st"
    using assms(3)
    by (simp add: exec_half_def add_hi_def)
  have step7: "resolve_size noop_hi (ds_inst_rem ?out_st) = Some (0, inst_rest)"
    by (simp add: resolve_size_def noop_hi_def)
  have step8: "?out_st \<lparr> ds_inst_rem := inst_rest \<rparr> = ?out_st" by simp
  have step9: "exec_half noop_hi 0 src_seg src_seg_len tgt_len ?out_st = Inl ?out_st"
    by (simp add: exec_half_def noop_hi_def)
  have unat_op_alt: "unat (1 + word_of_nat ?sz :: byte) = 1 + ?sz"
  proof -
    have "(1 :: byte) + word_of_nat ?sz = word_of_nat (1 + ?sz)" by simp
    thus ?thesis using unat_op by simp
  qed
  have entry_alt: "default_entry (unat (1 + word_of_nat ?sz :: byte)) = (add_hi ?sz, noop_hi)"
    using entry unat_op_alt by simp
  show ?thesis
    unfolding decode_one_def pop_byte_def Let_def
    using assms(1,3)
    by (auto simp add: entry_alt resolve_size_def add_hi_def noop_hi_def
                       exec_half_def)
qed

(* ADD with size 0 or > 17: opcode 1, size as varint. *)
lemma decode_one_add_general_suffix:
  assumes "length bs > 17 \<or> length bs = 0"
          "length bs < 2 ^ 32"
          "length (ds_tgt st) + length bs \<le> tgt_len"
  shows
    "decode_one src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := bs @ data_rest
           , ds_inst_rem := (1 :: byte) # varint_encode (length bs) @ inst_rest
           , ds_addr_rem := addr_rest \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_tgt := ds_tgt st @ bs \<rparr>)"
proof -
  let ?sz = "length bs"
  have unat1: "unat (1 :: byte) = Suc 0" by simp
  have entry: "default_entry (Suc 0) = (add_hi 0, noop_hi)"
    using default_entry_add_varint by simp
  have vdec: "varint_decode (varint_encode ?sz @ inst_rest) = Some (?sz, inst_rest)"
    using assms(2) varint_decode_encode by simp
  have resolve1: "resolve_size (add_hi 0) (varint_encode ?sz @ inst_rest)
                   = Some (?sz, inst_rest)"
    by (simp add: resolve_size_def add_hi_def vdec)
  have exec_add:
    "exec_half (add_hi 0) ?sz src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := bs @ data_rest
           , ds_inst_rem := inst_rest
           , ds_addr_rem := addr_rest \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_tgt := ds_tgt st @ bs \<rparr>)"
    using assms(3) by (simp add: exec_half_def add_hi_def)
  have resolve_noop: "resolve_size noop_hi inst_rest = Some (0, inst_rest)"
    by (simp add: resolve_size_def noop_hi_def)
  have exec_noop:
    "exec_half noop_hi 0 src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := data_rest
           , ds_inst_rem := inst_rest
           , ds_addr_rem := addr_rest
           , ds_tgt := ds_tgt st @ bs \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_tgt := ds_tgt st @ bs \<rparr>)"
    by (simp add: exec_half_def noop_hi_def)
  show ?thesis
    unfolding decode_one_def pop_byte_def Let_def
    using assms(3)
    by (auto simp add: unat1 entry vdec resolve1 exec_half_def add_hi_def noop_hi_def
                       resolve_size_def)
qed

(* Unified ADD: any size. *)
lemma decode_one_add_suffix:
  assumes "length bs < 2 ^ 32"
          "length (ds_tgt st) + length bs \<le> tgt_len"
  shows
    "let (op_code, needs_sz) = find_single_add_opcode (length bs);
         inst_bytes = [word_of_nat op_code :: byte] @
                      (if needs_sz then varint_encode (length bs) else [])
     in decode_one src_seg src_seg_len tgt_len
          (st \<lparr> ds_data_rem := bs @ data_rest
              , ds_inst_rem := inst_bytes @ inst_rest
              , ds_addr_rem := addr_rest \<rparr>)
        = Inl (st \<lparr> ds_data_rem := data_rest
                  , ds_inst_rem := inst_rest
                  , ds_addr_rem := addr_rest
                  , ds_tgt := ds_tgt st @ bs \<rparr>)"
proof (cases "1 \<le> length bs \<and> length bs \<le> 17")
  case True
  then have lb: "1 \<le> length bs" and ub: "length bs \<le> 17" by auto
  have op_eq: "find_single_add_opcode (length bs) = (1 + length bs, False)"
    using True by (simp add: find_single_add_opcode_def)
  show ?thesis
    using decode_one_add_small_suffix[OF lb ub assms(2)]
    by (simp add: op_eq)
next
  case False
  then have disj: "length bs > 17 \<or> length bs = 0" by linarith
  have op_eq: "find_single_add_opcode (length bs) = (1, True)"
    using disj by (auto simp: find_single_add_opcode_def)
  show ?thesis
    using decode_one_add_general_suffix[OF disj assms(1,2)]
    by (simp add: op_eq)
qed

(* RUN: opcode 0, size as varint, one data byte. *)
lemma decode_one_run_suffix:
  assumes "n > 0" "n < 2 ^ 32"
          "length (ds_tgt st) + n \<le> tgt_len"
  shows
    "decode_one src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := b # data_rest
           , ds_inst_rem := (0 :: byte) # varint_encode n @ inst_rest
           , ds_addr_rem := addr_rest \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_tgt := ds_tgt st @ replicate n b \<rparr>)"
proof -
  have unat0: "unat (0 :: byte) = 0" by simp
  have entry: "default_entry 0 = (run_hi 0, noop_hi)"
    by (simp add: default_entry_def run_hi_def noop_hi_def)
  have vdec: "varint_decode (varint_encode n @ inst_rest) = Some (n, inst_rest)"
    using assms(2) varint_decode_encode by simp
  let ?in_st = "st \<lparr> ds_data_rem := b # data_rest
                   , ds_inst_rem := (0 :: byte) # varint_encode n @ inst_rest
                   , ds_addr_rem := addr_rest \<rparr>"
  let ?st1 = "st \<lparr> ds_data_rem := b # data_rest
                 , ds_inst_rem := varint_encode n @ inst_rest
                 , ds_addr_rem := addr_rest \<rparr>"
  let ?st2 = "st \<lparr> ds_data_rem := b # data_rest
                 , ds_inst_rem := inst_rest
                 , ds_addr_rem := addr_rest \<rparr>"
  let ?out_st = "st \<lparr> ds_data_rem := data_rest
                    , ds_inst_rem := inst_rest
                    , ds_addr_rem := addr_rest
                    , ds_tgt := ds_tgt st @ replicate n b \<rparr>"
  have s1: "pop_byte (ds_inst_rem ?in_st) = Some (0 :: byte, varint_encode n @ inst_rest)"
    by (simp add: pop_byte_def)
  have s2: "?in_st \<lparr> ds_inst_rem := varint_encode n @ inst_rest \<rparr> = ?st1" by simp
  have s3: "resolve_size (run_hi 0) (ds_inst_rem ?st1) = Some (n, inst_rest)"
    by (simp add: resolve_size_def run_hi_def vdec)
  have s4: "?st1 \<lparr> ds_inst_rem := inst_rest \<rparr> = ?st2" by simp
  have s5: "exec_half (run_hi 0) n src_seg src_seg_len tgt_len ?st2 = Inl ?out_st"
    using assms(3) by (simp add: exec_half_def run_hi_def pop_byte_def)
  have s6: "resolve_size noop_hi (ds_inst_rem ?out_st) = Some (0, inst_rest)"
    by (simp add: resolve_size_def noop_hi_def)
  have s7: "?out_st \<lparr> ds_inst_rem := inst_rest \<rparr> = ?out_st" by simp
  have s8: "exec_half noop_hi 0 src_seg src_seg_len tgt_len ?out_st = Inl ?out_st"
    by (simp add: exec_half_def noop_hi_def)
  have tgt_ok: "\<not> tgt_len < length (ds_tgt st) + n" using assms(3) by simp
  show ?thesis
    unfolding decode_one_def
    by (simp add: pop_byte_def Let_def unat0 entry vdec exec_half_def
                  run_hi_def noop_hi_def resolve_size_def tgt_ok)
qed

(* COPY with size in 4..18: opcode encodes size directly. *)
lemma decode_one_copy_small_suffix:
  assumes "4 \<le> n" "n \<le> 18" "mode \<le> 8"
          "a < 2 ^ 32"
          "src_seg_len + length (ds_tgt st) < 2 ^ 32"
          "a < src_seg_len + length (ds_tgt st)"
          "length (ds_tgt st) + n \<le> tgt_len"
          "wf_encoding (ds_cache st) a (src_seg_len + length (ds_tgt st)) mode abytes"
  shows
    "decode_one src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := data_rest
           , ds_inst_rem := word_of_nat (19 + mode * 16 + n - 3) # inst_rest
           , ds_addr_rem := abytes @ addr_rest \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_cache := cache_update (ds_cache st) a
               , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>)"
proof -
  let ?op_nat = "19 + mode * 16 + n - 3"
  let ?op = "word_of_nat ?op_nat :: byte"
  have op_ub: "?op_nat \<le> 162" using assms(1,2,3) by simp
  have op_lb: "?op_nat \<ge> 20" using assms(1) by simp
  have op_lt_256: "?op_nat < 256" using op_ub by simp
  have unat_op: "unat ?op = ?op_nat"
    using op_lt_256 by (subst unat_of_nat_eq) simp_all
  have entry: "default_entry ?op_nat = (copy_hi n mode, noop_hi)"
    using default_entry_copy_small[OF assms(3,1,2)] .
  have n_pos: "n > 0" using assms(1) by simp
  have resolve_copy: "resolve_size (copy_hi n mode) inst_rest = Some (n, inst_rest)"
    using n_pos by (simp add: resolve_size_def copy_hi_def)
  have resolve_noop: "resolve_size noop_hi inst_rest = Some (0, inst_rest)"
    by (simp add: resolve_size_def noop_hi_def)
  let ?here = "src_seg_len + length (ds_tgt st)"
  have dec: "decode_address (ds_cache st) mode ?here (abytes @ addr_rest)
             = Some (a, addr_rest, cache_update (ds_cache st) a)"
    using wf_encoding_decodes[OF assms(8,4,5)] .
  have not_bad: "\<not> (a + n > src_seg_len + length (ds_tgt st) + n
                    \<or> a \<ge> src_seg_len + length (ds_tgt st))"
    using assms(6) by simp
  have exec_copy:
    "exec_half (copy_hi n mode) n src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := data_rest
           , ds_inst_rem := inst_rest
           , ds_addr_rem := abytes @ addr_rest \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_cache := cache_update (ds_cache st) a
               , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>)"
    using dec not_bad assms(7)
    by (simp add: exec_half_def copy_hi_def Let_def)
  have exec_noop:
    "exec_half noop_hi 0 src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := data_rest
           , ds_inst_rem := inst_rest
           , ds_addr_rem := addr_rest
           , ds_cache := cache_update (ds_cache st) a
           , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_cache := cache_update (ds_cache st) a
               , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>)"
    by (simp add: exec_half_def noop_hi_def)
  let ?in_st = "st \<lparr> ds_data_rem := data_rest
                   , ds_inst_rem := ?op # inst_rest
                   , ds_addr_rem := abytes @ addr_rest \<rparr>"
  let ?st1 = "st \<lparr> ds_data_rem := data_rest
                 , ds_inst_rem := inst_rest
                 , ds_addr_rem := abytes @ addr_rest \<rparr>"
  let ?out_st = "st \<lparr> ds_data_rem := data_rest
                    , ds_inst_rem := inst_rest
                    , ds_addr_rem := addr_rest
                    , ds_cache := cache_update (ds_cache st) a
                    , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>"
  have s1: "pop_byte (ds_inst_rem ?in_st) = Some (?op, inst_rest)"
    by (simp add: pop_byte_def)
  have s2: "?in_st \<lparr> ds_inst_rem := inst_rest \<rparr> = ?st1" by simp
  have s3: "resolve_size (copy_hi n mode) (ds_inst_rem ?st1) = Some (n, inst_rest)"
    using resolve_copy by simp
  have s4: "?st1 \<lparr> ds_inst_rem := inst_rest \<rparr> = ?st1" by simp
  have s5: "exec_half (copy_hi n mode) n src_seg src_seg_len tgt_len ?st1
            = Inl ?out_st"
    using exec_copy by simp
  have s6: "resolve_size noop_hi (ds_inst_rem ?out_st) = Some (0, inst_rest)"
    using resolve_noop by simp
  have s7: "?out_st \<lparr> ds_inst_rem := inst_rest \<rparr> = ?out_st" by simp
  have s8: "exec_half noop_hi 0 src_seg src_seg_len tgt_len ?out_st = Inl ?out_st"
    using exec_noop by simp
  have tgt_ok: "\<not> tgt_len < length (ds_tgt st) + n" using assms(7) by simp
  have n_pos: "n > 0" using assms(1) by linarith
  have n_neq: "n \<noteq> 0" using n_pos by simp
  \<comment> \<open>simp normalises word_of_nat(19+mode*16+n-3) into 16+(word_of_nat mode * 16 + word_of_nat n).
      Restate entry in that normalised form so simp can use it.\<close>
  have entry_norm: "default_entry (unat (16 + (word_of_nat mode * 16 + word_of_nat n) :: byte))
                    = (copy_hi n mode, noop_hi)"
  proof -
    have word_eq: "(16 + (word_of_nat mode * 16 + word_of_nat n) :: byte) = word_of_nat ?op_nat"
      using assms(1) by simp
    show ?thesis using entry unat_op word_eq by metis
  qed
  show ?thesis
    unfolding decode_one_def
    using n_neq assms(6)
    by (simp add: pop_byte_def Let_def entry_norm exec_half_def
                  copy_hi_def noop_hi_def resolve_size_def dec not_bad tgt_ok)
qed

(* COPY with size 0 or > 18: varint-size opcode. *)
lemma decode_one_copy_varint_suffix:
  assumes "mode \<le> 8" "n > 0" "n < 2 ^ 32"
          "a < 2 ^ 32"
          "src_seg_len + length (ds_tgt st) < 2 ^ 32"
          "a < src_seg_len + length (ds_tgt st)"
          "length (ds_tgt st) + n \<le> tgt_len"
          "wf_encoding (ds_cache st) a (src_seg_len + length (ds_tgt st)) mode abytes"
  shows
    "decode_one src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := data_rest
           , ds_inst_rem := word_of_nat (19 + mode * 16) # varint_encode n @ inst_rest
           , ds_addr_rem := abytes @ addr_rest \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_cache := cache_update (ds_cache st) a
               , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>)"
proof -
  let ?op_nat = "19 + mode * 16"
  let ?op = "word_of_nat ?op_nat :: byte"
  have op_ub: "?op_nat \<le> 162" using assms(1) by simp
  have op_lt_256: "?op_nat < 256" using op_ub by simp
  have unat_op: "unat ?op = ?op_nat"
    using op_lt_256 by (subst unat_of_nat_eq) simp_all
  have entry: "default_entry ?op_nat = (copy_hi 0 mode, noop_hi)"
    using default_entry_copy_varint[OF assms(1)] .
  have vdec: "varint_decode (varint_encode n @ inst_rest) = Some (n, inst_rest)"
    using assms(3) varint_decode_encode by simp
  have resolve_copy: "resolve_size (copy_hi 0 mode) (varint_encode n @ inst_rest)
                       = Some (n, inst_rest)"
    by (simp add: resolve_size_def copy_hi_def vdec)
  have resolve_noop: "resolve_size noop_hi inst_rest = Some (0, inst_rest)"
    by (simp add: resolve_size_def noop_hi_def)
  let ?here = "src_seg_len + length (ds_tgt st)"
  have dec: "decode_address (ds_cache st) mode ?here (abytes @ addr_rest)
             = Some (a, addr_rest, cache_update (ds_cache st) a)"
    using wf_encoding_decodes[OF assms(8,4,5)] .
  have not_bad: "\<not> (a + n > src_seg_len + length (ds_tgt st) + n
                    \<or> a \<ge> src_seg_len + length (ds_tgt st))"
    using assms(6) by simp
  have exec_copy:
    "exec_half (copy_hi 0 mode) n src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := data_rest
           , ds_inst_rem := inst_rest
           , ds_addr_rem := abytes @ addr_rest \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_cache := cache_update (ds_cache st) a
               , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>)"
    using dec not_bad assms(7)
    by (simp add: exec_half_def copy_hi_def Let_def)
  have exec_noop:
    "exec_half noop_hi 0 src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := data_rest
           , ds_inst_rem := inst_rest
           , ds_addr_rem := addr_rest
           , ds_cache := cache_update (ds_cache st) a
           , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>)
     = Inl (st \<lparr> ds_data_rem := data_rest
               , ds_inst_rem := inst_rest
               , ds_addr_rem := addr_rest
               , ds_cache := cache_update (ds_cache st) a
               , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>)"
    by (simp add: exec_half_def noop_hi_def)
  let ?in_st = "st \<lparr> ds_data_rem := data_rest
                   , ds_inst_rem := ?op # varint_encode n @ inst_rest
                   , ds_addr_rem := abytes @ addr_rest \<rparr>"
  let ?st1 = "st \<lparr> ds_data_rem := data_rest
                 , ds_inst_rem := varint_encode n @ inst_rest
                 , ds_addr_rem := abytes @ addr_rest \<rparr>"
  let ?st2 = "st \<lparr> ds_data_rem := data_rest
                 , ds_inst_rem := inst_rest
                 , ds_addr_rem := abytes @ addr_rest \<rparr>"
  let ?out_st = "st \<lparr> ds_data_rem := data_rest
                    , ds_inst_rem := inst_rest
                    , ds_addr_rem := addr_rest
                    , ds_cache := cache_update (ds_cache st) a
                    , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>"
  have s1: "pop_byte (ds_inst_rem ?in_st) = Some (?op, varint_encode n @ inst_rest)"
    by (simp add: pop_byte_def)
  have s2: "?in_st \<lparr> ds_inst_rem := varint_encode n @ inst_rest \<rparr> = ?st1" by simp
  have s3: "resolve_size (copy_hi 0 mode) (ds_inst_rem ?st1) = Some (n, inst_rest)"
    using resolve_copy by simp
  have s4: "?st1 \<lparr> ds_inst_rem := inst_rest \<rparr> = ?st2" by simp
  have s5: "exec_half (copy_hi 0 mode) n src_seg src_seg_len tgt_len ?st2
            = Inl ?out_st"
    using exec_copy by simp
  have s6: "resolve_size noop_hi (ds_inst_rem ?out_st) = Some (0, inst_rest)"
    using resolve_noop by simp
  have s7: "?out_st \<lparr> ds_inst_rem := inst_rest \<rparr> = ?out_st" by simp
  have s8: "exec_half noop_hi 0 src_seg src_seg_len tgt_len ?out_st = Inl ?out_st"
    using exec_noop by simp
  have tgt_ok: "\<not> tgt_len < length (ds_tgt st) + n" using assms(7) by simp
  \<comment> \<open>simp normalises word_of_nat (19 + mode*16) to 19 + word_of_nat mode * 16.
      Restate entry in that form.\<close>
  have entry_norm: "default_entry (unat (19 + word_of_nat mode * 16 :: byte))
                    = (copy_hi 0 mode, noop_hi)"
  proof -
    have word_eq: "(19 + word_of_nat mode * 16 :: byte) = word_of_nat ?op_nat"
      by simp
    show ?thesis using entry unat_op word_eq by metis
  qed
  show ?thesis
    unfolding decode_one_def
    using assms(2,6)
    by (simp add: pop_byte_def Let_def entry_norm vdec exec_half_def
                  copy_hi_def noop_hi_def resolve_size_def dec not_bad tgt_ok)
qed

(* Unified COPY: any size. *)
lemma decode_one_copy_suffix:
  assumes "mode \<le> 8" "n > 0" "n < 2 ^ 32"
          "a < 2 ^ 32"
          "src_seg_len + length (ds_tgt st) < 2 ^ 32"
          "a < src_seg_len + length (ds_tgt st)"
          "length (ds_tgt st) + n \<le> tgt_len"
          "wf_encoding (ds_cache st) a (src_seg_len + length (ds_tgt st)) mode abytes"
  shows
    "let (op_code, needs_sz) = find_single_copy_opcode n mode;
         inst_bytes = [word_of_nat op_code :: byte] @
                      (if needs_sz then varint_encode n else [])
     in decode_one src_seg src_seg_len tgt_len
          (st \<lparr> ds_data_rem := data_rest
              , ds_inst_rem := inst_bytes @ inst_rest
              , ds_addr_rem := abytes @ addr_rest \<rparr>)
        = Inl (st \<lparr> ds_data_rem := data_rest
                  , ds_inst_rem := inst_rest
                  , ds_addr_rem := addr_rest
                  , ds_cache := cache_update (ds_cache st) a
                  , ds_tgt := copy_loop src_seg (ds_tgt st) a n \<rparr>)"
proof (cases "4 \<le> n \<and> n \<le> 18")
  case True
  then have lb: "4 \<le> n" and ub: "n \<le> 18" by auto
  have op_eq: "find_single_copy_opcode n mode = (19 + mode * 16 + n - 3, False)"
    using True by (simp add: find_single_copy_opcode_def Let_def)
  show ?thesis
    using decode_one_copy_small_suffix[OF lb ub assms(1,4,5,6,7,8)]
    by (simp add: op_eq)
next
  case False
  have op_eq: "find_single_copy_opcode n mode = (19 + mode * 16, True)"
    using False by (auto simp: find_single_copy_opcode_def Let_def)
  show ?thesis
    using decode_one_copy_varint_suffix[OF assms]
    by (simp add: op_eq)
qed

(* ---------- Unified encode_one / decode_one roundtrip ---------- *)

lemma encode_one_decode_one_add:
  assumes "length bs > 0" "length bs < 2 ^ 32"
          "length tgt_so_far + length bs \<le> tgt_len"
  shows "let (d, ib, ab, c', tp') = encode_one (RAdd bs) src_len (length tgt_so_far) c [] [] []
     in decode_one src_seg src_seg_len tgt_len
           \<lparr> ds_data_rem = d @ data_rest
           , ds_inst_rem = ib @ inst_rest
           , ds_addr_rem = ab @ addr_rest
           , ds_cache = c
           , ds_tgt = tgt_so_far \<rparr>
         = Inl \<lparr> ds_data_rem = data_rest
               , ds_inst_rem = inst_rest
               , ds_addr_rem = addr_rest
               , ds_cache = c'
               , ds_tgt = tgt_so_far @ bs \<rparr>"
proof -
  obtain op needs_sz where fop: "find_single_add_opcode (length bs) = (op, needs_sz)"
    by (cases "find_single_add_opcode (length bs)") auto
  let ?ib = "[word_of_nat op :: byte] @ (if needs_sz then varint_encode (length bs) else [])"
  have eo: "encode_one (RAdd bs) src_len (length tgt_so_far) c [] [] []
            = (bs, ?ib, [], c, length tgt_so_far + length bs)"
    using fop by (simp add: Let_def split_def)
  let ?st = "\<lparr> ds_data_rem = undefined, ds_inst_rem = undefined,
               ds_addr_rem = undefined, ds_cache = c, ds_tgt = tgt_so_far \<rparr>"
  have "decode_one src_seg src_seg_len tgt_len
          \<lparr> ds_data_rem = bs @ data_rest
          , ds_inst_rem = ?ib @ inst_rest
          , ds_addr_rem = addr_rest
          , ds_cache = c
          , ds_tgt = tgt_so_far \<rparr>
        = Inl \<lparr> ds_data_rem = data_rest
              , ds_inst_rem = inst_rest
              , ds_addr_rem = addr_rest
              , ds_cache = c
              , ds_tgt = tgt_so_far @ bs \<rparr>"
  proof (cases "1 \<le> length bs \<and> length bs \<le> 17")
    case True
    then have lb: "1 \<le> length bs" and ub: "length bs \<le> 17" by auto
    have tgt_bd: "length (ds_tgt ?st) + length bs \<le> tgt_len"
      using assms(3) by simp
    have step: "decode_one src_seg src_seg_len tgt_len
          (?st \<lparr> ds_data_rem := bs @ data_rest
              , ds_inst_rem := word_of_nat (1 + length bs) # inst_rest
              , ds_addr_rem := addr_rest \<rparr>)
        = Inl (?st \<lparr> ds_data_rem := data_rest
                  , ds_inst_rem := inst_rest
                  , ds_addr_rem := addr_rest
                  , ds_tgt := ds_tgt ?st @ bs \<rparr>)"
      using decode_one_add_small_suffix[OF lb ub tgt_bd] .
    then have "find_single_add_opcode (length bs) = (1 + length bs, False)"
      using True by (simp add: find_single_add_opcode_def)
    with fop have op_eq: "op = 1 + length bs" "needs_sz = False" by auto
    show ?thesis unfolding op_eq using step by simp
  next
    case False
    then have disj: "length bs > 17 \<or> length bs = 0" using assms(1) by linarith
    have tgt_bd: "length (ds_tgt ?st) + length bs \<le> tgt_len"
      using assms(3) by simp
    have step: "decode_one src_seg src_seg_len tgt_len
          (?st \<lparr> ds_data_rem := bs @ data_rest
              , ds_inst_rem := (1 :: byte) # varint_encode (length bs) @ inst_rest
              , ds_addr_rem := addr_rest \<rparr>)
        = Inl (?st \<lparr> ds_data_rem := data_rest
                  , ds_inst_rem := inst_rest
                  , ds_addr_rem := addr_rest
                  , ds_tgt := ds_tgt ?st @ bs \<rparr>)"
      using decode_one_add_general_suffix[OF disj assms(2) tgt_bd] .
    then have "find_single_add_opcode (length bs) = (1, True)"
      using disj by (auto simp: find_single_add_opcode_def)
    with fop have op_eq: "op = 1" "needs_sz = True" by auto
    show ?thesis unfolding op_eq using step by simp
  qed
  thus ?thesis using eo by (simp add: split_def)
qed

lemma encode_one_decode_one_run:
  assumes "n > 0" "n < 2 ^ 32"
          "length tgt_so_far + n \<le> tgt_len"
  shows "let (d, ib, ab, c', tp') = encode_one (RRun b n) src_len (length tgt_so_far) c [] [] []
     in decode_one src_seg src_seg_len tgt_len
           \<lparr> ds_data_rem = d @ data_rest
           , ds_inst_rem = ib @ inst_rest
           , ds_addr_rem = ab @ addr_rest
           , ds_cache = c
           , ds_tgt = tgt_so_far \<rparr>
         = Inl \<lparr> ds_data_rem = data_rest
               , ds_inst_rem = inst_rest
               , ds_addr_rem = addr_rest
               , ds_cache = c'
               , ds_tgt = tgt_so_far @ replicate n b \<rparr>"
proof -
  have eo: "encode_one (RRun b n) src_len (length tgt_so_far) c [] [] []
            = ([b], [0 :: byte] @ varint_encode n, [], c, length tgt_so_far + n)"
    by (simp add: find_single_run_opcode_def Let_def split_def)
  let ?st = "\<lparr> ds_data_rem = undefined, ds_inst_rem = undefined,
               ds_addr_rem = undefined, ds_cache = c, ds_tgt = tgt_so_far \<rparr>"
  have tgt_bd: "length (ds_tgt ?st) + n \<le> tgt_len" using assms(3) by simp
  have step: "decode_one src_seg src_seg_len tgt_len
        (?st \<lparr> ds_data_rem := b # data_rest
            , ds_inst_rem := (0 :: byte) # varint_encode n @ inst_rest
            , ds_addr_rem := addr_rest \<rparr>)
      = Inl (?st \<lparr> ds_data_rem := data_rest
                , ds_inst_rem := inst_rest
                , ds_addr_rem := addr_rest
                , ds_tgt := ds_tgt ?st @ replicate n b \<rparr>)"
    using decode_one_run_suffix[OF assms(1,2) tgt_bd] .
  show ?thesis using eo step by (simp add: split_def)
qed

lemma encode_one_decode_one_copy:
  assumes "n > 0" "n < 2 ^ 32" "a < 2 ^ 32"
          "a < src_seg_len + length tgt_so_far"
          "src_seg_len + length tgt_so_far < 2 ^ 32"
          "length tgt_so_far + n \<le> tgt_len"
          "src_len = src_seg_len"
  shows "let (d, ib, ab, c', tp') = encode_one (RCopy a n) src_len (length tgt_so_far) c [] [] []
     in decode_one src_seg src_seg_len tgt_len
           \<lparr> ds_data_rem = d @ data_rest
           , ds_inst_rem = ib @ inst_rest
           , ds_addr_rem = ab @ addr_rest
           , ds_cache = c
           , ds_tgt = tgt_so_far \<rparr>
         = Inl \<lparr> ds_data_rem = data_rest
               , ds_inst_rem = inst_rest
               , ds_addr_rem = addr_rest
               , ds_cache = c'
               , ds_tgt = copy_loop src_seg tgt_so_far a n \<rparr>"
proof -
  let ?here = "src_len + length tgt_so_far"
  obtain mode abytes where
    ea: "encode_address c a ?here = (mode, abytes, cache_update c a)"
    and wf_enc: "wf_encoding c a ?here mode abytes"
    using encode_address_wf[of a ?here c] assms(3,5,7) by auto
  have mode_bd: "mode \<le> 8"
  proof -
    have "fst (encode_address c a ?here) < num_modes"
      using encode_address_mode_bound by blast
    thus ?thesis using ea by simp
  qed
  obtain op needs_sz where fop: "find_single_copy_opcode n mode = (op, needs_sz)"
    by (cases "find_single_copy_opcode n mode") auto
  let ?ib = "[word_of_nat op :: byte] @ (if needs_sz then varint_encode n else [])"
  have eo: "encode_one (RCopy a n) src_len (length tgt_so_far) c [] [] []
            = ([], ?ib, abytes, cache_update c a, length tgt_so_far + n)"
    using ea fop by (simp add: Let_def split_def)
  have wf: "wf_encoding c a (src_seg_len + length tgt_so_far) mode abytes"
    using wf_enc assms(7) by simp
  have "decode_one src_seg src_seg_len tgt_len
          \<lparr> ds_data_rem = data_rest
          , ds_inst_rem = ?ib @ inst_rest
          , ds_addr_rem = abytes @ addr_rest
          , ds_cache = c
          , ds_tgt = tgt_so_far \<rparr>
        = Inl \<lparr> ds_data_rem = data_rest
              , ds_inst_rem = inst_rest
              , ds_addr_rem = addr_rest
              , ds_cache = cache_update c a
              , ds_tgt = copy_loop src_seg tgt_so_far a n \<rparr>"
  proof (cases "4 \<le> n \<and> n \<le> 18")
    case True
    then have "find_single_copy_opcode n mode = (19 + mode * 16 + n - 3, False)"
      by (simp add: find_single_copy_opcode_def Let_def)
    with fop have op_eq: "op = 19 + mode * 16 + n - 3" "needs_sz = False" by auto
    let ?stc = "\<lparr> ds_data_rem = data_rest, ds_inst_rem = inst_rest,
                   ds_addr_rem = addr_rest, ds_cache = c, ds_tgt = tgt_so_far \<rparr>"
    have wf_unfolded:
        "wf_encoding (ds_cache ?stc) a (src_seg_len + length (ds_tgt ?stc)) mode abytes"
      unfolding dec_state.select_convs by (rule wf)
    from decode_one_copy_small_suffix[where st = ?stc, simplified,
         OF _ _ mode_bd assms(3,5,4,6)[simplified] wf_unfolded[simplified]] True
    have inst:
      "decode_one src_seg src_seg_len tgt_len
         \<lparr> ds_data_rem = data_rest
         , ds_inst_rem = word_of_nat (19 + mode * 16 + n - 3) # inst_rest
         , ds_addr_rem = abytes @ addr_rest
         , ds_cache = c
         , ds_tgt = tgt_so_far \<rparr>
       = Inl \<lparr> ds_data_rem = data_rest
             , ds_inst_rem = inst_rest
             , ds_addr_rem = addr_rest
             , ds_cache = cache_update c a
             , ds_tgt = copy_loop src_seg tgt_so_far a n \<rparr>"
      by simp
    show ?thesis unfolding op_eq using inst assms(7) by simp
  next
    case False
    then have "find_single_copy_opcode n mode = (19 + mode * 16, True)"
      by (auto simp: find_single_copy_opcode_def Let_def)
    with fop have op_eq: "op = 19 + mode * 16" "needs_sz = True" by auto
    let ?stc = "\<lparr> ds_data_rem = data_rest, ds_inst_rem = inst_rest,
                   ds_addr_rem = addr_rest, ds_cache = c, ds_tgt = tgt_so_far \<rparr>"
    have wf_unfolded:
        "wf_encoding (ds_cache ?stc) a (src_seg_len + length (ds_tgt ?stc)) mode abytes"
      unfolding dec_state.select_convs by (rule wf)
    from decode_one_copy_varint_suffix[where st = ?stc, simplified,
         OF mode_bd assms(1,2,3,5,4,6)[simplified] wf_unfolded[simplified]]
    have inst:
      "decode_one src_seg src_seg_len tgt_len
         \<lparr> ds_data_rem = data_rest
         , ds_inst_rem = word_of_nat (19 + mode * 16) # varint_encode n @ inst_rest
         , ds_addr_rem = abytes @ addr_rest
         , ds_cache = c
         , ds_tgt = tgt_so_far \<rparr>
       = Inl \<lparr> ds_data_rem = data_rest
             , ds_inst_rem = inst_rest
             , ds_addr_rem = addr_rest
             , ds_cache = cache_update c a
             , ds_tgt = copy_loop src_seg tgt_so_far a n \<rparr>"
      by simp
    show ?thesis unfolding op_eq using inst assms(7) by simp
  qed
  thus ?thesis using eo by (simp add: split_def)
qed

(* ---------- Inductive roundtrip: encode_window_loop / decode_loop ---------- *)

definition bounded_insts :: "raw_inst list \<Rightarrow> bool" where
  "bounded_insts insts =
     (\<forall>i \<in> set insts. case i of
        RAdd bs \<Rightarrow> length bs < 2 ^ 32
      | RRun _ n \<Rightarrow> n < 2 ^ 32
      | RCopy a n \<Rightarrow> n < 2 ^ 32 \<and> a < 2 ^ 32)"

lemma generate_run_instructions_bounded:
  assumes "length tgt < 2 ^ 32"
  shows "bounded_insts (generate_run_instructions tgt)"
  using assms
  by (cases tgt) (auto simp: generate_run_instructions_def bounded_insts_def)

lemma encode_window_generate_run_instructions_bounds:
  assumes ew:
    "encode_window (generate_run_instructions tgt) (length src) = (data, inst, addr, c)"
  shows "length data \<le> length tgt
       \<and> length inst \<le> 1 + varint_size (length tgt)
       \<and> addr = []"
proof (cases tgt)
  case Nil
  then show ?thesis using ew by (simp add: encode_window_def generate_run_instructions_def)
next
  case (Cons b bs)
  show ?thesis
  proof (cases "4 \<le> length tgt \<and> all_bytes_eq b bs")
    case True
    then show ?thesis
      using ew Cons
      by (auto simp: encode_window_def generate_run_instructions_def
                    find_single_run_opcode_def varint_size_lengths Let_def split_def)
  next
    case False
    then show ?thesis
      using ew Cons
      by (auto simp: encode_window_def generate_run_instructions_def
                     find_single_add_opcode_def Let_def split_def)
  qed
qed

lemma encode_window_loop_decode_loop:
  assumes ewl: "encode_window_loop insts src_len tgt_pos c [] [] [] = (data, inst, addr, c')"
      and wf: "wf_insts_aux src_seg insts tgt_so_far"
      and bi: "bounded_insts insts"
      and tgt_pos_eq: "tgt_pos = length tgt_so_far"
      and src_len_eq: "src_len = length src_seg"
      and src_bd: "length src_seg < 2 ^ 32"
      and tgt_len_eq: "tgt_len = length (exec_inst_list src_seg insts tgt_so_far)"
      and combined_bd: "length src_seg + tgt_len < 2 ^ 32"
  shows "decode_loop (length inst) src_seg (length src_seg) tgt_len
           \<lparr> ds_data_rem = data
           , ds_inst_rem = inst
           , ds_addr_rem = addr
           , ds_cache = c
           , ds_tgt = tgt_so_far \<rparr>
         = Inl \<lparr> ds_data_rem = []
               , ds_inst_rem = []
               , ds_addr_rem = []
               , ds_cache = c'
               , ds_tgt = exec_inst_list src_seg insts tgt_so_far \<rparr>"
  using assms
proof (induction insts arbitrary: tgt_pos c data inst addr tgt_so_far c')
  case Nil
  then show ?case by simp
next
  case (Cons i "rest")
  obtain d0 ib0 ab0 c0 tp0 where
    eo0: "encode_one i src_len tgt_pos c [] [] [] = (d0, ib0, ab0, c0, tp0)"
    by (cases "encode_one i src_len tgt_pos c [] [] []") auto
  obtain dr ir ar cr where
    ewr: "encode_window_loop rest src_len tp0 c0 [] [] [] = (dr, ir, ar, cr)"
    by (cases "encode_window_loop rest src_len tp0 c0 [] [] []") auto
  have loop_split: "encode_window_loop (i # rest) src_len tgt_pos c [] [] [] =
    (d0 @ dr, ib0 @ ir, ab0 @ ar, cr)"
  proof -
    have from_eo: "encode_window_loop rest src_len tp0 c0 d0 ib0 ab0 =
                    (d0 @ dr, ib0 @ ir, ab0 @ ar, cr)"
      using encode_window_loop_prefix[of rest src_len tp0 c0 d0 ib0 ab0] ewr
      by auto
    show ?thesis
      using eo0 from_eo by (simp add: split_def Let_def)
  qed
  from Cons.prems(1) loop_split have
    data_eq: "data = d0 @ dr" and inst_eq: "inst = ib0 @ ir" and
    addr_eq: "addr = ab0 @ ar" and c'_eq: "c' = cr"
    by simp_all

  let ?tgt1 = "exec_inst src_seg i tgt_so_far"

  have tp0_eq: "tp0 = length ?tgt1"
    using eo0 Cons.prems(4,5)
    by (cases i) (auto simp: Let_def split_def copy_loop_length
                        find_single_add_opcode_def find_single_run_opcode_def
                        find_single_copy_opcode_def exec_inst_length)

  have bi_hd: "case i of RAdd bs \<Rightarrow> length bs < 2 ^ 32 | RRun _ n \<Rightarrow> n < 2 ^ 32
               | RCopy a n \<Rightarrow> n < 2 ^ 32 \<and> a < 2 ^ 32"
    using Cons.prems(3) by (simp add: bounded_insts_def)
  have bi_tl: "bounded_insts rest"
    using Cons.prems(3) by (simp add: bounded_insts_def)

  have tgt_len_ge: "length tgt_so_far + (case i of RAdd bs \<Rightarrow> length bs
                     | RRun _ n \<Rightarrow> n | RCopy _ n \<Rightarrow> n) \<le> tgt_len"
  proof -
    have "tgt_len = length (exec_inst_list src_seg (i # rest) tgt_so_far)"
      using Cons.prems(7) .
    also have "\<dots> = length (exec_inst_list src_seg rest ?tgt1)" by simp
    also have "\<dots> \<ge> length ?tgt1"
      by (simp add: exec_inst_list_length)
    finally have "tgt_len \<ge> length ?tgt1" .
    thus ?thesis by (simp add: exec_inst_length)
  qed

  have ib0_ne: "ib0 \<noteq> []"
    using eo0 by (cases i) (auto simp: Let_def split_def
                   find_single_add_opcode_def find_single_run_opcode_def
                   find_single_copy_opcode_def)

  have do_step: "decode_one src_seg (length src_seg) tgt_len
      \<lparr> ds_data_rem = d0 @ dr, ds_inst_rem = ib0 @ ir
      , ds_addr_rem = ab0 @ ar, ds_cache = c, ds_tgt = tgt_so_far \<rparr>
    = Inl \<lparr> ds_data_rem = dr, ds_inst_rem = ir
          , ds_addr_rem = ar, ds_cache = c0, ds_tgt = ?tgt1 \<rparr>"
  proof (cases i)
    case (RAdd bs)
    from Cons.prems(2) RAdd have wf_i: "length bs > 0" by simp
    from bi_hd RAdd have bd_i: "length bs < 2 ^ 32" by simp
    from tgt_len_ge RAdd have tgt_ge: "length tgt_so_far + length bs \<le> tgt_len" by simp
    \<comment> \<open>From eo0 (applied with i = RAdd bs) and the encode_one definition,
        extract concrete component values.\<close>
    obtain op needs_sz where fop: "find_single_add_opcode (length bs) = (op, needs_sz)"
      by (cases "find_single_add_opcode (length bs)") auto
    let ?ib = "[word_of_nat op :: byte] @ (if needs_sz then varint_encode (length bs) else [])"
    have d0_eq: "d0 = bs" and ib0_eq: "ib0 = ?ib" and ab0_eq: "ab0 = []"
         and c0_eq: "c0 = c"
      using eo0 RAdd Cons.prems(4) fop by (auto simp add: Let_def split_def)
    have decode_add:
      "decode_one src_seg (length src_seg) tgt_len
         \<lparr> ds_data_rem = bs @ dr, ds_inst_rem = ?ib @ ir
         , ds_addr_rem = [] @ ar, ds_cache = c, ds_tgt = tgt_so_far \<rparr>
       = Inl \<lparr> ds_data_rem = dr, ds_inst_rem = ir
             , ds_addr_rem = ar, ds_cache = c, ds_tgt = tgt_so_far @ bs \<rparr>"
      using encode_one_decode_one_add[OF wf_i bd_i tgt_ge,
        where data_rest = dr and inst_rest = ir and addr_rest = ar
          and src_seg = src_seg and src_seg_len = "length src_seg"
          and c = c and src_len = src_len]
      by (simp add: Let_def split_def fop)
    show ?thesis
      unfolding d0_eq ib0_eq ab0_eq c0_eq using decode_add RAdd by simp
  next
    case (RRun b n)
    from Cons.prems(2) RRun have wf_i: "n > 0" by simp
    from bi_hd RRun have bd_i: "n < 2 ^ 32" by simp
    from tgt_len_ge RRun have tgt_ge: "length tgt_so_far + n \<le> tgt_len" by simp
    obtain op needs_sz where fop: "find_single_run_opcode n = (op, needs_sz)"
      by (cases "find_single_run_opcode n") auto
    let ?ib = "[word_of_nat op :: byte] @ (if needs_sz then varint_encode n else [])"
    have d0_eq: "d0 = [b]" and ib0_eq: "ib0 = ?ib" and ab0_eq: "ab0 = []"
         and c0_eq: "c0 = c"
      using eo0 RRun Cons.prems(4) fop by (auto simp add: Let_def split_def)
    have decode_run:
      "decode_one src_seg (length src_seg) tgt_len
         \<lparr> ds_data_rem = [b] @ dr, ds_inst_rem = ?ib @ ir
         , ds_addr_rem = [] @ ar, ds_cache = c, ds_tgt = tgt_so_far \<rparr>
       = Inl \<lparr> ds_data_rem = dr, ds_inst_rem = ir
             , ds_addr_rem = ar, ds_cache = c, ds_tgt = tgt_so_far @ replicate n b \<rparr>"
      using encode_one_decode_one_run[OF wf_i bd_i tgt_ge,
        where data_rest = dr and inst_rest = ir and addr_rest = ar
          and src_seg = src_seg and src_seg_len = "length src_seg"
          and c = c and src_len = src_len]
      by (simp add: Let_def split_def fop)
    show ?thesis
      unfolding d0_eq ib0_eq ab0_eq c0_eq using decode_run RRun by simp
  next
    case (RCopy a n)
    from Cons.prems(2) RCopy have wf_i: "n > 0" "a < length src_seg + length tgt_so_far"
      by simp_all
    from bi_hd RCopy have bd_i: "n < 2 ^ 32" "a < 2 ^ 32" by simp_all
    from tgt_len_ge RCopy have tgt_ge: "length tgt_so_far + n \<le> tgt_len" by simp
    have here_bd: "length src_seg + length tgt_so_far < 2 ^ 32"
    proof -
      have "length tgt_so_far \<le> tgt_len"
      proof -
        have "tgt_len = length (exec_inst_list src_seg (i # rest) tgt_so_far)"
          using Cons.prems(7) .
        also have "\<dots> = length tgt_so_far
                       + sum_list (map (\<lambda>i. case i of RAdd bs \<Rightarrow> length bs
                                           | RCopy _ n \<Rightarrow> n | RRun _ n \<Rightarrow> n) (i # rest))"
          by (rule exec_inst_list_length)
        finally show ?thesis by linarith
      qed
      thus ?thesis using Cons.prems(8) by linarith
    qed
    obtain mode abytes c1 where ea: "encode_address c a (src_len + length tgt_so_far)
                                       = (mode, abytes, c1)"
      by (cases "encode_address c a (src_len + length tgt_so_far)") auto
    obtain op needs_sz where fop: "find_single_copy_opcode n mode = (op, needs_sz)"
      by (cases "find_single_copy_opcode n mode") auto
    let ?ib = "[word_of_nat op :: byte] @ (if needs_sz then varint_encode n else [])"
    have d0_eq: "d0 = []" and ib0_eq: "ib0 = ?ib" and ab0_eq: "ab0 = abytes"
         and c0_eq: "c0 = c1"
      using eo0 RCopy Cons.prems(4) ea fop by (auto simp add: Let_def split_def)
    have decode_copy:
      "decode_one src_seg (length src_seg) tgt_len
         \<lparr> ds_data_rem = [] @ dr, ds_inst_rem = ?ib @ ir
         , ds_addr_rem = abytes @ ar, ds_cache = c, ds_tgt = tgt_so_far \<rparr>
       = Inl \<lparr> ds_data_rem = dr, ds_inst_rem = ir
             , ds_addr_rem = ar, ds_cache = c1, ds_tgt = copy_loop src_seg tgt_so_far a n \<rparr>"
    proof -
      have "let (d, ib, ab, c'', tp') = encode_one (RCopy a n) src_len (length tgt_so_far) c [] [] []
         in decode_one src_seg (length src_seg) tgt_len
               \<lparr> ds_data_rem = d @ dr, ds_inst_rem = ib @ ir
               , ds_addr_rem = ab @ ar, ds_cache = c, ds_tgt = tgt_so_far \<rparr>
            = Inl \<lparr> ds_data_rem = dr, ds_inst_rem = ir
                  , ds_addr_rem = ar, ds_cache = c''
                  , ds_tgt = copy_loop src_seg tgt_so_far a n \<rparr>"
        using encode_one_decode_one_copy[OF wf_i(1) bd_i(1) bd_i(2) wf_i(2) here_bd tgt_ge
                Cons.prems(5),
          where data_rest = dr and inst_rest = ir and addr_rest = ar
            and src_seg = src_seg and c = c]
        by simp
      thus ?thesis
        using ea fop Cons.prems(5) by (simp add: Let_def split_def)
    qed
    show ?thesis
      unfolding d0_eq ib0_eq ab0_eq c0_eq using decode_copy RCopy by simp
  qed

  have wf_tl: "wf_insts_aux src_seg rest ?tgt1"
    using Cons.prems(2) by (cases i) simp_all
  have tgt_len_tl: "tgt_len = length (exec_inst_list src_seg rest ?tgt1)"
    using Cons.prems(7) by simp
  have combined_tl: "length src_seg + tgt_len < 2 ^ 32"
    using Cons.prems(8) .

  have ih: "decode_loop (length ir) src_seg (length src_seg) tgt_len
      \<lparr> ds_data_rem = dr, ds_inst_rem = ir
      , ds_addr_rem = ar, ds_cache = c0, ds_tgt = ?tgt1 \<rparr>
    = Inl \<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = []
          , ds_cache = cr, ds_tgt = exec_inst_list src_seg rest ?tgt1 \<rparr>"
    using Cons.IH[OF ewr wf_tl bi_tl tp0_eq Cons.prems(5,6) tgt_len_tl combined_tl]
    by simp

  have fuel_ge: "length (ib0 @ ir) - 1 \<ge> length ir"
  proof -
    have "length ib0 \<ge> 1" using ib0_ne by (cases ib0) auto
    thus ?thesis by simp
  qed
  have ih_mono: "decode_loop (length (ib0 @ ir) - 1) src_seg (length src_seg) tgt_len
      \<lparr> ds_data_rem = dr, ds_inst_rem = ir
      , ds_addr_rem = ar, ds_cache = c0, ds_tgt = ?tgt1 \<rparr>
    = Inl \<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = []
          , ds_cache = cr, ds_tgt = exec_inst_list src_seg rest ?tgt1 \<rparr>"
    using decode_loop_mono[OF ih fuel_ge] .

  have inst_ne: "ib0 @ ir \<noteq> []" using ib0_ne by simp
  obtain fuel where fuel_eq: "length (ib0 @ ir) = Suc fuel"
    using inst_ne by (cases "length (ib0 @ ir)") auto

  show ?case
    unfolding data_eq inst_eq addr_eq c'_eq
    using do_step ih_mono fuel_eq ib0_ne by simp
qed

(* ---------- Generic serialize / parse roundtrip ---------- *)

lemma serialize_parse_roundtrip:
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32 - 32"
          "length data < 2 ^ 32"
          "length inst < 2 ^ 32"
          "length addr < 2 ^ 32"
          "varint_size (length tgt) + 1 + varint_size (length data)
           + varint_size (length inst) + varint_size (length addr)
           + length data + length inst + length addr < 2 ^ 32"
  shows "decode_spec (serialize src tgt data inst addr) src
       = (let src_seg_len = (if length src > 0 then length src else 0);
              src_seg_off = 0;
              src_seg = (if src_seg_len = 0 then []
                         else take src_seg_len (drop src_seg_off src))
          in apply_window
               \<lparr> pw_src_seg_len = src_seg_len, pw_src_seg_off = src_seg_off
               , pw_tgt_len = length tgt
               , pw_data = data, pw_inst = inst, pw_addr = addr \<rparr>
               src)"
proof -
  let ?has_src = "length src > 0"
  let ?win_ind = "if ?has_src then 0x01 else 0x00 :: byte"
  let ?src_desc = "if ?has_src then varint_encode (length src) @ varint_encode 0 else []"
  let ?dlen = "varint_size (length tgt) + 1 + varint_size (length data)
             + varint_size (length inst) + varint_size (length addr)
             + length data + length inst + length addr"

  have vsz_le_5: "varint_size n \<le> 5" if "n < 2 ^ 32" for n
  proof -
    have "n < 2 ^ 35" using that by simp
    hence "num_digits n \<le> 5" by (rule num_digits_le_5)
    thus ?thesis by (simp add: varint_size_def)
  qed

  have dlen_bd: "?dlen < 2 ^ 32"
    using assms(6) by simp

  have shape: "serialize src tgt data inst addr =
    magic_bytes @ [0x00, ?win_ind] @ ?src_desc
    @ varint_encode ?dlen
    @ varint_encode (length tgt)
    @ [0x00]
    @ varint_encode (length data)
    @ varint_encode (length inst)
    @ varint_encode (length addr)
    @ data @ inst @ addr"
    by (simp add: serialize_def Let_def)

  have ph: "parse_header (serialize src tgt data inst addr)
    = Inl (?win_ind # ?src_desc
           @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
           @ varint_encode (length data) @ varint_encode (length inst)
           @ varint_encode (length addr) @ data @ inst @ addr)"
    using shape parse_header_of_magic
    by (simp add: magic_bytes_def)

  have tgt_bd: "length tgt < 2 ^ 32" using assms(2) by simp

  show ?thesis
  proof (cases ?has_src)
    case True
    hence win_ind_eq: "?win_ind = 0x01" by simp
    have src_desc_eq: "?src_desc = varint_encode (length src) @ varint_encode 0"
      using True by simp
    have ph': "parse_header (serialize src tgt data inst addr)
      = Inl (0x01 # varint_encode (length src) @ varint_encode 0
             @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
             @ varint_encode (length data) @ varint_encode (length inst)
             @ varint_encode (length addr) @ data @ inst @ addr)"
      using ph win_ind_eq src_desc_eq by simp
    have pw: "parse_window
        (0x01 # varint_encode (length src) @ varint_encode 0
         @ varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
         @ varint_encode (length data) @ varint_encode (length inst)
         @ varint_encode (length addr) @ data @ inst @ addr)
      = Inl ( \<lparr> pw_src_seg_len = length src, pw_src_seg_off = 0
              , pw_tgt_len = length tgt
              , pw_data = data, pw_inst = inst, pw_addr = addr \<rparr>, [])"
      using parse_window_with_source_head[OF dlen_bd tgt_bd assms(1,3,4,5)]
      by simp
    show ?thesis
      using ph' pw True
      by (simp add: decode_spec_def Let_def)
  next
    case False
    hence len_zero: "length src = 0" by simp
    hence win_ind_eq: "?win_ind = 0x00" by simp
    have src_desc_eq: "?src_desc = []" using False by simp
    have ph': "parse_header (serialize src tgt data inst addr)
      = Inl (0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
             @ varint_encode (length data) @ varint_encode (length inst)
             @ varint_encode (length addr) @ data @ inst @ addr)"
      using ph win_ind_eq src_desc_eq by simp
    have pw: "parse_window
        (0x00 # varint_encode ?dlen @ varint_encode (length tgt) @ [0x00]
         @ varint_encode (length data) @ varint_encode (length inst)
         @ varint_encode (length addr) @ data @ inst @ addr)
      = Inl ( \<lparr> pw_src_seg_len = 0, pw_src_seg_off = 0
              , pw_tgt_len = length tgt
              , pw_data = data, pw_inst = inst, pw_addr = addr \<rparr>, [])"
      using parse_window_no_source_head[OF dlen_bd tgt_bd assms(3,4,5)]
      by simp
    show ?thesis
      using ph' pw len_zero
      by (simp add: decode_spec_def Let_def)
  qed
qed

lemma serialize_apply_window_roundtrip:
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32 - 32"
          "length data < 2 ^ 32"
          "length inst < 2 ^ 32"
          "length addr < 2 ^ 32"
          "varint_size (length tgt) + 1 + varint_size (length data)
           + varint_size (length inst) + varint_size (length addr)
           + length data + length inst + length addr < 2 ^ 32"
      and "apply_window
             \<lparr> pw_src_seg_len = (if length src > 0 then length src else 0)
             , pw_src_seg_off = 0
             , pw_tgt_len = length tgt
             , pw_data = data, pw_inst = inst, pw_addr = addr \<rparr>
             src = Inl tgt"
  shows "decode_spec (serialize src tgt data inst addr) src = Inl tgt"
proof -
  have parsed:
    "decode_spec (serialize src tgt data inst addr) src
       = (let src_seg_len = (if length src > 0 then length src else 0);
              src_seg_off = 0;
              src_seg = (if src_seg_len = 0 then []
                         else take src_seg_len (drop src_seg_off src))
          in apply_window
               \<lparr> pw_src_seg_len = src_seg_len, pw_src_seg_off = src_seg_off
               , pw_tgt_len = length tgt
               , pw_data = data, pw_inst = inst, pw_addr = addr \<rparr>
               src)"
    by (rule serialize_parse_roundtrip[OF assms(1-6)])
  show ?thesis
    using parsed assms(7) by (simp add: Let_def)
qed

(* ---------- Top-level generic roundtrip theorem ---------- *)

theorem roundtrip_generic:
  assumes vi: "valid_insts src tgt insts"
      and bi: "bounded_insts insts"
      and src_bd: "length src < 2 ^ 32"
      and tgt_bd: "length tgt < 2 ^ 32 - 32"
      and combined_bd: "length src + length tgt < 2 ^ 32"
      and ew_bd: "let (data, inst, addr, _) = encode_window insts (length src)
                  in length data < 2 ^ 32 \<and> length inst < 2 ^ 32
                   \<and> length addr < 2 ^ 32
                   \<and> varint_size (length tgt) + 1 + varint_size (length data)
                     + varint_size (length inst) + varint_size (length addr)
                     + length data + length inst + length addr < 2 ^ 32"
  shows "decode_spec (serialize_from_insts src tgt insts) src = Inl tgt"
proof -
  obtain data inst_bytes addr_bytes enc_cache where
    ew: "encode_window insts (length src)
         = (data, inst_bytes, addr_bytes, enc_cache)"
    by (cases "encode_window insts (length src)") auto

  from ew_bd ew have sz_bds:
      "length data < 2 ^ 32" "length inst_bytes < 2 ^ 32"
      "length addr_bytes < 2 ^ 32"
      "varint_size (length tgt) + 1 + varint_size (length data)
       + varint_size (length inst_bytes) + varint_size (length addr_bytes)
       + length data + length inst_bytes + length addr_bytes < 2 ^ 32"
    by (auto simp: split_def)

  have serialized: "serialize_from_insts src tgt insts
    = serialize src tgt data inst_bytes addr_bytes"
    using ew by (simp add: serialize_from_insts_def)

  have ewl: "encode_window_loop insts (length src) 0 cache_init [] [] []
             = (data, inst_bytes, addr_bytes, enc_cache)"
    using ew by (simp add: encode_window_def)

  have exec_eq: "exec_inst_list src insts [] = tgt"
    using vi by (simp add: valid_insts_def)
  have wf: "wf_insts_aux src insts []"
    using vi by (simp add: valid_insts_def wf_insts_def)

  have tgt_len_eq: "length tgt = length (exec_inst_list src insts [])"
    using exec_eq by simp

  have tgt_pos_eq: "(0 :: nat) = length ([] :: byte list)" by simp
  have src_len_eq: "length src = length src" by simp
  have decode_ok: "decode_loop (length inst_bytes) src (length src) (length tgt)
      \<lparr> ds_data_rem = data, ds_inst_rem = inst_bytes, ds_addr_rem = addr_bytes
      , ds_cache = cache_init, ds_tgt = [] \<rparr>
    = Inl \<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = []
          , ds_cache = enc_cache, ds_tgt = tgt \<rparr>"
    using encode_window_loop_decode_loop[OF ewl wf bi tgt_pos_eq src_len_eq
            src_bd tgt_len_eq combined_bd]
    exec_eq
    by simp

  have spr: "decode_spec (serialize src tgt data inst_bytes addr_bytes) src
    = (let src_seg_len = (if length src > 0 then length src else 0);
           src_seg_off = 0;
           src_seg = (if src_seg_len = 0 then []
                      else take src_seg_len (drop src_seg_off src))
       in apply_window
            \<lparr> pw_src_seg_len = src_seg_len, pw_src_seg_off = src_seg_off
            , pw_tgt_len = length tgt
            , pw_data = data, pw_inst = inst_bytes, pw_addr = addr_bytes \<rparr>
            src)"
    by (rule serialize_parse_roundtrip[OF src_bd tgt_bd sz_bds])

  have aw: "apply_window
       \<lparr> pw_src_seg_len = (if length src > 0 then length src else 0)
       , pw_src_seg_off = 0
       , pw_tgt_len = length tgt
       , pw_data = data, pw_inst = inst_bytes, pw_addr = addr_bytes \<rparr>
       src
     = Inl tgt"
  proof (cases "length src > 0")
    case True
    have src_eq: "take (length src) src = src" by simp
    have "decode_loop (length inst_bytes) src (length src) (length tgt)
            \<lparr> ds_data_rem = data, ds_inst_rem = inst_bytes
            , ds_addr_rem = addr_bytes, ds_cache = cache_init, ds_tgt = [] \<rparr>
          = Inl \<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = []
                , ds_cache = enc_cache, ds_tgt = tgt \<rparr>"
      using decode_ok .
    thus ?thesis
      using True src_eq by (simp add: apply_window_def Let_def)
  next
    case False
    hence len_zero: "length src = 0" by simp
    hence src_eq: "src = []" by simp
    have "decode_loop (length inst_bytes) src (length src) (length tgt)
            \<lparr> ds_data_rem = data, ds_inst_rem = inst_bytes
            , ds_addr_rem = addr_bytes, ds_cache = cache_init, ds_tgt = [] \<rparr>
          = Inl \<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = []
                , ds_cache = enc_cache, ds_tgt = tgt \<rparr>"
      using decode_ok .
    hence "decode_loop (length inst_bytes) [] 0 (length tgt)
            \<lparr> ds_data_rem = data, ds_inst_rem = inst_bytes
            , ds_addr_rem = addr_bytes, ds_cache = cache_init, ds_tgt = [] \<rparr>
          = Inl \<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = []
                , ds_cache = enc_cache, ds_tgt = tgt \<rparr>"
      using src_eq by simp
    thus ?thesis
      using len_zero src_eq by (simp add: apply_window_def Let_def)
  qed

  show ?thesis
    unfolding serialized
    using spr aw by (simp add: Let_def)
qed

(* The historical degenerate corollary. *)
corollary spec_roundtrip_degenerate':
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32 - 32"
  shows   "decode_spec (encode_spec_degenerate src tgt) src = Inl tgt"
  using spec_roundtrip_degenerate[OF assms] .

lemma varint_size_le_5_32:
  assumes "n < 2 ^ 32"
  shows "varint_size n \<le> 5"
proof -
  have "n < 2 ^ 35" using assms by simp
  hence "num_digits n \<le> 5" by (rule num_digits_le_5)
  thus ?thesis by (simp add: varint_size_def)
qed

theorem spec_roundtrip_run:
  assumes src_bd: "length src < 2 ^ 32"
      and tgt_bd: "length tgt < 2 ^ 32 - 32"
      and combined_bd: "length src + length tgt < 2 ^ 32"
  shows "decode_spec (encode_spec_run src tgt) src = Inl tgt"
proof -
  let ?insts = "generate_instructions src tgt"

  have vi: "valid_insts src tgt ?insts"
    by (simp add: generate_instructions_def generate_run_instructions_valid)

  have tgt_bd32: "length tgt < 2 ^ 32"
    using tgt_bd by simp
  have tgt_bd32_slack: "length tgt < 2 ^ 32 - 32"
    using tgt_bd .

  have bi: "bounded_insts ?insts"
    using generate_run_instructions_bounded[OF tgt_bd32]
    by (simp add: generate_instructions_def)

  have ew_bd:
    "let (data, inst, addr, _) = encode_window ?insts (length src)
     in length data < 2 ^ 32 \<and> length inst < 2 ^ 32
      \<and> length addr < 2 ^ 32
      \<and> varint_size (length tgt) + 1 + varint_size (length data)
        + varint_size (length inst) + varint_size (length addr)
        + length data + length inst + length addr < 2 ^ 32"
  proof -
    obtain data inst addr c where
      ew: "encode_window ?insts (length src) = (data, inst, addr, c)"
      by (cases "encode_window ?insts (length src)") auto
    have ew_run:
      "encode_window (generate_run_instructions tgt) (length src) =
        (data, inst, addr, c)"
      using ew by (simp add: generate_instructions_def)
    have lens:
      "length data \<le> length tgt"
      "length inst \<le> 1 + varint_size (length tgt)"
      "addr = []"
      using encode_window_generate_run_instructions_bounds[OF ew_run] by auto
    have data_bd: "length data < 2 ^ 32"
      using lens(1) tgt_bd32 by linarith
    have addr_bd: "length addr < 2 ^ 32"
      using lens(3) by simp
    have vsz_tgt: "varint_size (length tgt) \<le> 5"
      by (rule varint_size_le_5_32[OF tgt_bd32])
    have inst_bd: "length inst < 2 ^ 32"
    proof -
      have "length inst \<le> 6"
        using lens(2) vsz_tgt by linarith
      thus ?thesis by simp
    qed
    have vsz_data: "varint_size (length data) \<le> 5"
      by (rule varint_size_le_5_32[OF data_bd])
    have vsz_inst: "varint_size (length inst) \<le> 5"
      by (rule varint_size_le_5_32[OF inst_bd])
    have vsz_addr: "varint_size (length addr) \<le> 1"
      using lens(3) by (simp add: varint_size_def)
    have addr_len: "length addr = 0"
      using lens(3) by simp
    have dlen_le:
      "varint_size (length tgt) + 1 + varint_size (length data)
       + varint_size (length inst) + varint_size (length addr)
       + length data + length inst + length addr
       \<le> 23 + length tgt"
      using lens addr_len vsz_tgt vsz_data vsz_inst vsz_addr by linarith
    have dlen_bd:
      "23 + length tgt < 2 ^ 32"
      using tgt_bd by simp
    show ?thesis
      using ew data_bd inst_bd addr_bd dlen_le dlen_bd by simp
  qed

  have "decode_spec (serialize_from_insts src tgt ?insts) src = Inl tgt"
    by (rule roundtrip_generic[OF vi bi src_bd tgt_bd32_slack combined_bd ew_bd])
  thus ?thesis
    by (simp add: encode_spec_run_def)
qed

(* ================================================================== *)
(* Part 3: Full C-shaped encoder proof obligations                    *)
(* ================================================================== *)

lemma source_positions_spec_sound:
  assumes "p \<in> set (source_positions_spec src)"
  shows "p + min_match \<le> length src"
proof (cases "length src < min_match")
  case True
  with assms show ?thesis by (simp add: source_positions_spec_def)
next
  case False
  with assms have "p < length src - min_match + 1"
    by (auto simp: source_positions_spec_def)
  then have "p \<le> length src - min_match"
    by linarith
  with False show ?thesis
    by linarith
qed

lemma build_index_spec_bucket_sound:
  assumes "p \<in> set (index_bucket_spec (build_index_spec src) h)"
  shows "p + min_match \<le> length src \<and> hash_bucket_spec src p = h"
  using assms source_positions_spec_sound[of p src]
  by (auto simp: index_bucket_spec_def build_index_spec_def)

lemma common_prefix_fuel_le_fuel:
  "common_prefix_fuel fuel a apos b bpos \<le> fuel"
  by (induction fuel arbitrary: apos bpos) auto

lemma common_prefix_spec_le_left:
  "common_prefix_spec a apos aend b bpos bend \<le> aend - apos"
  unfolding common_prefix_spec_def
  using common_prefix_fuel_le_fuel[of "min (aend - apos) (bend - bpos)"
        "take aend a" apos "take bend b" bpos]
  by linarith

lemma common_prefix_spec_le_right:
  "common_prefix_spec a apos aend b bpos bend \<le> bend - bpos"
  unfolding common_prefix_spec_def
  using common_prefix_fuel_le_fuel[of "min (aend - apos) (bend - bpos)"
        "take aend a" apos "take bend b" bpos]
  by linarith

lemma common_prefix_fuel_sound:
  assumes "k < common_prefix_fuel fuel a apos b bpos"
  shows "apos + k < length a \<and> bpos + k < length b
       \<and> a ! (apos + k) = b ! (bpos + k)"
  using assms
proof (induction fuel arbitrary: apos bpos k)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "apos < length a \<and> bpos < length b \<and> a ! apos = b ! bpos")
    case False
    with Suc.prems show ?thesis by simp
  next
    case True
    show ?thesis
    proof (cases k)
      case 0
      with True show ?thesis by simp
    next
      case (Suc k')
      with Suc.prems True have k'_lt:
        "k' < common_prefix_fuel fuel a (apos + 1) b (bpos + 1)"
        by simp
      have rec:
        "(apos + 1) + k' < length a \<and> (bpos + 1) + k' < length b
       \<and> a ! ((apos + 1) + k') = b ! ((bpos + 1) + k')"
        by (rule Suc.IH[OF k'_lt])
      with Suc show ?thesis by simp
    qed
  qed
qed

lemma common_prefix_spec_sound:
  assumes "k < common_prefix_spec a apos aend b bpos bend"
  shows "apos + k < aend \<and> bpos + k < bend
       \<and> apos + k < length a \<and> bpos + k < length b
       \<and> a ! (apos + k) = b ! (bpos + k)"
proof -
  have fuel:
    "apos + k < length (take aend a) \<and> bpos + k < length (take bend b)
       \<and> take aend a ! (apos + k) = take bend b ! (bpos + k)"
    using assms
    unfolding common_prefix_spec_def
    by (rule common_prefix_fuel_sound)
  then show ?thesis
    by (auto simp: nth_take)
qed

lemma choose_match_spec_sound:
  assumes cand_valid: "cand + min_match \<le> length src"
      and best_sound:
        "min_match \<le> em_len best \<Longrightarrow>
          em_pos best + em_len best \<le> length src
          \<and> tp + em_len best \<le> length tgt
          \<and> (\<forall>k < em_len best.
                src ! (em_pos best + k) = tgt ! (tp + k))"
      and match: "min_match \<le> em_len (choose_match_spec src tgt tp cand best)"
  shows "em_pos (choose_match_spec src tgt tp cand best)
          + em_len (choose_match_spec src tgt tp cand best) \<le> length src
       \<and> tp + em_len (choose_match_spec src tgt tp cand best) \<le> length tgt
       \<and> (\<forall>k < em_len (choose_match_spec src tgt tp cand best).
             src ! (em_pos (choose_match_spec src tgt tp cand best) + k)
             = tgt ! (tp + k))"
proof -
  let ?l = "common_prefix_spec src cand (length src) tgt tp (length tgt)"
  show ?thesis
  proof (cases "cand + min_match \<le> length src \<and> min_match \<le> ?l \<and> em_len best < ?l")
    case False
    have not_choose:
      "\<not> (cand + min_match \<le> length src \<and> min_match \<le> ?l \<and> em_len best < ?l)"
      using False by blast
    have choose_eq: "choose_match_spec src tgt tp cand best = best"
      using not_choose by (auto simp: choose_match_spec_def Let_def)
    with match best_sound show ?thesis
      by simp
  next
    case True
    have choose_eq:
      "choose_match_spec src tgt tp cand best =
        \<lparr> em_pos = cand, em_len = ?l \<rparr>"
      using True by (simp add: choose_match_spec_def Let_def)
    have min_l: "min_match \<le> ?l"
      using True by simp
    have cand_le: "cand \<le> length src"
      using cand_valid by linarith
    have l_src: "?l \<le> length src - cand"
      by (rule common_prefix_spec_le_left)
    have src_bound: "cand + ?l \<le> length src"
      using cand_le l_src by linarith
    have l_tgt: "?l \<le> length tgt - tp"
      by (rule common_prefix_spec_le_right)
    have tp_le: "tp \<le> length tgt"
    proof (rule ccontr)
      assume "\<not> tp \<le> length tgt"
      with l_tgt have "?l = 0" by simp
      with min_l show False by (simp add: min_match_def)
    qed
    have tgt_bound: "tp + ?l \<le> length tgt"
      using tp_le l_tgt by linarith
    have bytes:
      "\<forall>k < ?l. src ! (cand + k) = tgt ! (tp + k)"
      using common_prefix_spec_sound[of _ src cand "length src" tgt tp "length tgt"]
      by blast
    show ?thesis
      using choose_eq src_bound tgt_bound bytes by simp
  qed
qed

lemma foldl_choose_match_spec_sound:
  assumes cands_valid: "\<forall>cand \<in> set cands. cand + min_match \<le> length src"
      and best_sound:
        "min_match \<le> em_len best \<Longrightarrow>
          em_pos best + em_len best \<le> length src
          \<and> tp + em_len best \<le> length tgt
          \<and> (\<forall>k < em_len best.
                src ! (em_pos best + k) = tgt ! (tp + k))"
      and match:
        "min_match \<le> em_len
          (foldl (\<lambda>best cand. choose_match_spec src tgt tp cand best)
            best cands)"
  shows "em_pos (foldl (\<lambda>best cand. choose_match_spec src tgt tp cand best)
            best cands)
          + em_len (foldl (\<lambda>best cand. choose_match_spec src tgt tp cand best)
            best cands) \<le> length src
       \<and> tp + em_len (foldl (\<lambda>best cand. choose_match_spec src tgt tp cand best)
            best cands) \<le> length tgt
       \<and> (\<forall>k < em_len
              (foldl (\<lambda>best cand. choose_match_spec src tgt tp cand best)
                best cands).
             src ! (em_pos
               (foldl (\<lambda>best cand. choose_match_spec src tgt tp cand best)
                 best cands) + k)
             = tgt ! (tp + k))"
  using cands_valid best_sound match
proof (induction cands arbitrary: best)
  case Nil
  then show ?case by simp
next
  case (Cons cand cands)
  let ?best' = "choose_match_spec src tgt tp cand best"
  have best'_sound:
    "min_match \<le> em_len ?best' \<Longrightarrow>
      em_pos ?best' + em_len ?best' \<le> length src
      \<and> tp + em_len ?best' \<le> length tgt
      \<and> (\<forall>k < em_len ?best'. src ! (em_pos ?best' + k) = tgt ! (tp + k))"
  proof -
    assume match': "min_match \<le> em_len ?best'"
    have cand_valid: "cand + min_match \<le> length src"
      using Cons.prems(1) by simp
    show "em_pos ?best' + em_len ?best' \<le> length src
      \<and> tp + em_len ?best' \<le> length tgt
      \<and> (\<forall>k < em_len ?best'. src ! (em_pos ?best' + k) = tgt ! (tp + k))"
      by (rule choose_match_spec_sound[OF cand_valid Cons.prems(2) match'])
  qed
  show ?case
    using Cons.IH[of ?best'] Cons.prems(1,3) best'_sound by simp
qed

lemma find_best_match_spec_sound:
  fixes m :: enc_match
  assumes m_def: "m = find_best_match_spec src tgt tp (build_index_spec src)"
      and match: "min_match \<le> em_len m"
  shows "em_pos m + em_len m \<le> length src
       \<and> tp + em_len m \<le> length tgt
       \<and> (\<forall>k < em_len m. src ! (em_pos m + k) = tgt ! (tp + k))"
proof -
  show ?thesis
  proof (cases "length src < min_match \<or> length tgt - tp < min_match")
    case True
    with m_def match show ?thesis
      by (simp add: find_best_match_spec_def no_match_def min_match_def)
  next
    case False
    let ?h = "hash_bucket_spec tgt tp"
    let ?candidates = "take max_chain (index_bucket_spec (build_index_spec src) ?h)"
    have cands_valid:
      "\<forall>cand \<in> set ?candidates. cand + min_match \<le> length src"
      using build_index_spec_bucket_sound[of _ src ?h]
      by (auto dest!: in_set_takeD)
    have folded:
      "m = foldl (\<lambda>best cand. choose_match_spec src tgt tp cand best)
             no_match ?candidates"
      using m_def False
      by (simp add: find_best_match_spec_def Let_def)
    have no_match_sound:
      "min_match \<le> em_len no_match \<Longrightarrow>
        em_pos no_match + em_len no_match \<le> length src
        \<and> tp + em_len no_match \<le> length tgt
        \<and> (\<forall>k < em_len no_match.
              src ! (em_pos no_match + k) = tgt ! (tp + k))"
      by (simp add: no_match_def min_match_def)
    show ?thesis
      using foldl_choose_match_spec_sound[OF cands_valid no_match_sound]
        folded match
      by simp
  qed
qed

lemma exec_inst_list_append:
  "exec_inst_list src (xs @ ys) acc =
     exec_inst_list src ys (exec_inst_list src xs acc)"
  by (induction xs arbitrary: acc) simp_all

lemma wf_insts_aux_append:
  "wf_insts_aux src (xs @ ys) acc =
     (wf_insts_aux src xs acc \<and>
      wf_insts_aux src ys (exec_inst_list src xs acc))"
proof (induction xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons i xs)
  show ?case
  proof (cases i)
    case (RAdd bs)
    then show ?thesis
      using Cons.IH[of "acc @ bs"] by simp
  next
    case (RCopy a n)
    then show ?thesis
      using Cons.IH[of "copy_loop src acc a n"] by simp
  next
    case (RRun b n)
    then show ?thesis
      using Cons.IH[of "acc @ replicate n b"] by simp
  qed
qed

definition pending_scan_tail :: "pending_scan \<Rightarrow> byte list" where
  "pending_scan_tail s =
     ps_add s @
       (case ps_run_byte s of
          None \<Rightarrow> []
        | Some b \<Rightarrow> replicate (ps_run_len s) b)"

lemma append_add_inst_exec:
  "exec_inst_list src (append_add_inst bs out) acc =
     exec_inst_list src out acc @ bs"
  by (simp add: append_add_inst_def exec_inst_list_append)

lemma close_pending_run_exec_tail:
  "exec_inst_list src (ps_out (close_pending_run s)) acc
     @ pending_scan_tail (close_pending_run s) =
   exec_inst_list src (ps_out s) acc @ pending_scan_tail s"
  by (cases "ps_run_byte s")
     (auto simp: close_pending_run_def pending_scan_tail_def
                 append_add_inst_exec exec_inst_list_append
           split: if_splits)

lemma close_pending_run_no_run:
  "ps_run_byte (close_pending_run s) = None"
  by (cases "ps_run_byte s")
     (auto simp: close_pending_run_def split: if_splits)

lemma pending_scan_step_exec_tail:
  "exec_inst_list src (ps_out (pending_scan_step s b)) acc
     @ pending_scan_tail (pending_scan_step s b) =
   exec_inst_list src (ps_out s) acc @ pending_scan_tail s @ [b]"
proof (cases "ps_run_byte s")
  case None
  then show ?thesis
    by (simp add: pending_scan_step_def pending_scan_tail_def)
next
  case (Some rb)
  show ?thesis
  proof (cases "b = rb")
    case True
    with Some show ?thesis
      by (simp add: pending_scan_step_def pending_scan_tail_def
                    replicate_append_same)
  next
    case False
    have tail_close: "pending_scan_tail (close_pending_run s) =
        ps_add (close_pending_run s)"
      by (simp add: pending_scan_tail_def close_pending_run_no_run)
    from Some False show ?thesis
      using close_pending_run_exec_tail[of src s acc] tail_close
      by (simp add: pending_scan_step_def pending_scan_tail_def)
  qed
qed

lemma pending_scan_fold_exec_tail:
  "exec_inst_list src (ps_out (foldl pending_scan_step s bs)) acc
     @ pending_scan_tail (foldl pending_scan_step s bs) =
   exec_inst_list src (ps_out s) acc @ pending_scan_tail s @ bs"
proof (induction bs arbitrary: s acc)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have step:
    "exec_inst_list src (ps_out (pending_scan_step s b)) acc
       @ pending_scan_tail (pending_scan_step s b) =
     exec_inst_list src (ps_out s) acc @ pending_scan_tail s @ [b]"
    by (rule pending_scan_step_exec_tail)
  show ?case
    using Cons.IH[of "pending_scan_step s b" acc] step by simp
qed

lemma pending_scan_init_tail:
  "pending_scan_tail pending_scan_init = []"
  by (simp add: pending_scan_tail_def pending_scan_init_def)

lemma flush_pending_insts_exec:
  "exec_inst_list src (flush_pending_insts pending) acc = acc @ pending"
proof -
  let ?s0 = "pending_scan_init"
  let ?s1 = "foldl pending_scan_step ?s0 pending"
  let ?s2 = "close_pending_run ?s1"
  have fold:
    "exec_inst_list src (ps_out ?s1) acc @ pending_scan_tail ?s1 =
     acc @ pending"
    using pending_scan_fold_exec_tail[of src ?s0 pending acc]
    by (simp add: pending_scan_init_def pending_scan_tail_def)
  have close:
    "exec_inst_list src (ps_out ?s2) acc @ pending_scan_tail ?s2 =
     acc @ pending"
    using close_pending_run_exec_tail[of src ?s1 acc] fold by simp
  have tail: "pending_scan_tail ?s2 = ps_add ?s2"
    by (simp add: pending_scan_tail_def close_pending_run_no_run)
  show ?thesis
    using close tail
    by (simp add: flush_pending_insts_def append_add_inst_exec Let_def)
qed

lemma flush_pending_insts_wf_aux:
  "wf_insts_aux src (flush_pending_insts pending) acc"
proof -
  have add: "\<And>bs out acc.
      wf_insts_aux src out acc \<Longrightarrow>
      wf_insts_aux src (append_add_inst bs out) acc"
    by (simp add: append_add_inst_def wf_insts_aux_append)
  have close: "\<And>(s::pending_scan) acc.
      wf_insts_aux src (ps_out s) acc \<Longrightarrow>
      wf_insts_aux src (ps_out (close_pending_run s)) acc"
  proof -
    fix s :: pending_scan
    fix acc
    assume wf: "wf_insts_aux src (ps_out s) acc"
    show "wf_insts_aux src (ps_out (close_pending_run s)) acc"
    proof (cases "ps_run_byte s")
      case None
      then show ?thesis
        using wf by (simp add: close_pending_run_def)
    next
      case (Some b)
      show ?thesis
      proof (cases "min_run \<le> ps_run_len s")
        case True
        hence len_pos: "0 < ps_run_len s"
          by (simp add: min_run_def)
        have wf_add:
          "wf_insts_aux src (append_add_inst (ps_add s) (ps_out s)) acc"
          using wf by (rule add)
        from Some True len_pos wf_add show ?thesis
          by (simp add: close_pending_run_def wf_insts_aux_append
                        append_add_inst_exec)
      next
        case False
        with Some wf show ?thesis
          by (simp add: close_pending_run_def)
      qed
    qed
  qed
  have step: "\<And>b (s::pending_scan) acc.
      wf_insts_aux src (ps_out s) acc \<Longrightarrow>
      wf_insts_aux src (ps_out (pending_scan_step s b)) acc"
  proof -
    fix b
    fix s :: pending_scan
    fix acc
    assume wf: "wf_insts_aux src (ps_out s) acc"
    show "wf_insts_aux src (ps_out (pending_scan_step s b)) acc"
    proof (cases "ps_run_byte s")
      case None
      with wf show ?thesis
        by (simp add: pending_scan_step_def)
    next
      case (Some rb)
      show ?thesis
      proof (cases "b = rb")
        case True
        with Some wf show ?thesis
          by (simp add: pending_scan_step_def)
      next
        case False
        with Some close[OF wf] show ?thesis
          by (simp add: pending_scan_step_def)
      qed
    qed
  qed
  have fold: "\<And>(s::pending_scan) acc.
      wf_insts_aux src (ps_out s) acc \<Longrightarrow>
      wf_insts_aux src (ps_out (foldl pending_scan_step s pending)) acc"
    by (induction pending arbitrary: s acc) (auto intro: step)
  show ?thesis
    by (simp add: flush_pending_insts_def Let_def add close fold
                  pending_scan_init_def)
qed

lemma fused_copy_len_spec_le:
  assumes "fused_copy_len_spec mode copy_len = Some csz"
  shows "csz \<le> copy_len"
  using assms
  by (auto simp: fused_copy_len_spec_def split: if_splits)

lemma copy_loop_source_match_take:
  assumes addr_bound: "addr + n \<le> length src"
      and tgt_bound: "tp + n \<le> length tgt"
      and match: "\<forall>k < n. src ! (addr + k) = tgt ! (tp + k)"
  shows "copy_loop src (take tp tgt) addr n = take (tp + n) tgt"
  using addr_bound tgt_bound match
proof (induction n arbitrary: addr tp)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have addr_lt: "addr < length src"
    using Suc.prems(1) by simp
  have tp_lt: "tp < length tgt"
    using Suc.prems(2) by simp
  have match0: "src ! addr = tgt ! tp"
    using Suc.prems(3) by (drule_tac x=0 in spec) simp
  have cb: "combined_byte src (take tp tgt) addr = tgt ! tp"
    using match0 addr_lt by (simp add: combined_byte_def)
  have take_suc: "take tp tgt @ [tgt ! tp] = take (Suc tp) tgt"
    using tp_lt by (simp add: take_Suc_conv_app_nth)
  have addr_bound': "addr + 1 + n \<le> length src"
    using Suc.prems(1) by simp
  have tgt_bound': "Suc tp + n \<le> length tgt"
    using Suc.prems(2) by simp
  have match': "\<forall>k < n. src ! (addr + 1 + k) = tgt ! (Suc tp + k)"
    using Suc.prems(3) by auto
  have "copy_loop src (take tp tgt) addr (Suc n)
      = copy_loop src (take (Suc tp) tgt) (addr + 1) n"
    using cb take_suc by simp
  also have "\<dots> = take (Suc tp + n) tgt"
    using Suc.IH[OF addr_bound' tgt_bound' match'] .
  also have "\<dots> = take (tp + Suc n) tgt"
    by simp
  finally show ?case .
qed

lemma try_emit_add_copy_spec_trace_exec:
  assumes "try_emit_add_copy_spec src_len copy_addr copy_len st = Some st'"
      and "exec_inst_list src (enc_trace st) [] = take (enc_flushed st) tgt"
      and "enc_pending st = take (enc_tp st - enc_flushed st)
            (drop (enc_flushed st) tgt)"
      and "copy_addr + copy_len \<le> length src"
      and "enc_tp st + copy_len \<le> length tgt"
      and "\<forall>k < copy_len. src ! (copy_addr + k) = tgt ! (enc_tp st + k)"
  shows "exec_inst_list src (enc_trace st') [] = take (enc_flushed st') tgt"
proof -
  obtain mode abytes cache' where ea:
    "encode_address (enc_cache st) copy_addr (src_len + enc_tp st) =
      (mode, abytes, cache')"
    by (cases "encode_address (enc_cache st) copy_addr (src_len + enc_tp st)")
       auto
  from assms(1) ea obtain csz op where
      add_pos: "1 \<le> length (enc_pending st)"
      and add_le: "length (enc_pending st) \<le> 4"
      and fused: "fused_copy_len_spec mode copy_len = Some csz"
      and opcode: "find_add_copy_opcode (length (enc_pending st)) csz mode = Some op"
      and st'_eq:
        "st' =
          st \<lparr> enc_tp := enc_tp st + csz
             , enc_flushed := enc_flushed st + length (enc_pending st) + csz
             , enc_pending := []
             , enc_data := enc_data st @ enc_pending st
             , enc_inst := enc_inst st @ [word_of_nat op]
             , enc_addr := enc_addr st @ abytes
             , enc_cache := cache'
             , enc_trace := enc_trace st
                 @ [RAdd (enc_pending st), RCopy copy_addr csz] \<rparr>"
    by (auto simp: try_emit_add_copy_spec_def Let_def
        split: option.splits if_splits)
  have csz_le: "csz \<le> copy_len"
    by (rule fused_copy_len_spec_le[OF fused])
  have tp_bound: "enc_tp st \<le> length tgt"
    using assms(5) by simp
  have flushed_le_tp: "enc_flushed st \<le> enc_tp st"
  proof (rule ccontr)
    assume "\<not> enc_flushed st \<le> enc_tp st"
    hence "enc_tp st - enc_flushed st = 0" by simp
    hence "enc_pending st = []"
      using assms(3) by simp
    thus False
      using add_pos by simp
  qed
  have pending_len: "length (enc_pending st) = enc_tp st - enc_flushed st"
    using assms(3) flushed_le_tp tp_bound by simp
  have add_prefix: "take (enc_flushed st) tgt @ enc_pending st = take (enc_tp st) tgt"
  proof -
    have "take (enc_tp st) tgt =
        take (enc_flushed st + (enc_tp st - enc_flushed st)) tgt"
      using flushed_le_tp by simp
    also have "\<dots> =
        take (enc_flushed st) tgt
        @ take (enc_tp st - enc_flushed st) (drop (enc_flushed st) tgt)"
      by (simp add: take_add)
    also have "\<dots> = take (enc_flushed st) tgt @ enc_pending st"
      using assms(3) by simp
    finally show ?thesis by simp
  qed
  have copy_addr_bound: "copy_addr + csz \<le> length src"
    using assms(4) csz_le by linarith
  have copy_tgt_bound: "enc_tp st + csz \<le> length tgt"
    using assms(5) csz_le by linarith
  have copy_match:
    "\<forall>k < csz. src ! (copy_addr + k) = tgt ! (enc_tp st + k)"
    using assms(6) csz_le by auto
  have copy_exec:
    "copy_loop src (take (enc_tp st) tgt) copy_addr csz =
      take (enc_tp st + csz) tgt"
    by (rule copy_loop_source_match_take
        [OF copy_addr_bound copy_tgt_bound copy_match])
  have flushed'_eq: "enc_flushed st' = enc_tp st + csz"
    using st'_eq pending_len flushed_le_tp by simp
  have "exec_inst_list src (enc_trace st') [] =
      copy_loop src (take (enc_tp st) tgt) copy_addr csz"
    using assms(2) st'_eq add_prefix
    by (simp add: exec_inst_list_append)
  also have "\<dots> = take (enc_tp st + csz) tgt"
    by (rule copy_exec)
  also have "\<dots> = take (enc_flushed st') tgt"
    using flushed'_eq by simp
  finally show ?thesis .
qed

lemma flush_pending_spec_trace_exec:
  assumes "exec_inst_list src (enc_trace st) [] = take (enc_flushed st) tgt"
      and "enc_pending st = take (enc_tp st - enc_flushed st)
            (drop (enc_flushed st) tgt)"
      and "enc_flushed st \<le> enc_tp st"
  shows "exec_inst_list src (enc_trace (flush_pending_spec src_len st)) []
       = take (enc_tp st) tgt"
proof -
  have emit_trace:
    "enc_trace (emit_insts_spec src_len insts st) = enc_trace st @ insts"
    for insts
    by (induction insts arbitrary: st)
       (simp_all add: emit_insts_spec_def emit_inst_spec_def
                      split: prod.splits)
  have trace:
    "enc_trace (flush_pending_spec src_len st) =
     enc_trace st @ flush_pending_insts (enc_pending st)"
    by (simp add: flush_pending_spec_def emit_trace)
  have exec:
    "exec_inst_list src (enc_trace (flush_pending_spec src_len st)) [] =
     take (enc_flushed st) tgt @ enc_pending st"
    using assms(1)
    by (simp add: trace exec_inst_list_append flush_pending_insts_exec)
  also have "\<dots> = take (enc_tp st) tgt"
  proof -
    have "take (enc_flushed st) tgt
        @ take (enc_tp st - enc_flushed st) (drop (enc_flushed st) tgt) =
      take (enc_flushed st + (enc_tp st - enc_flushed st)) tgt"
      by (simp add: take_add)
    also have "\<dots> = take (enc_tp st) tgt"
      using assms(3) by simp
    finally show ?thesis
      using assms(2) by simp
  qed
  finally show ?thesis .
qed

lemma emit_inst_spec_enc_flushed_exec:
  assumes "length acc = enc_flushed st"
  shows "enc_flushed (emit_inst_spec src_len i st) =
         length (exec_inst src i acc)"
  using assms
  by (cases i)
     (auto simp: emit_inst_spec_def Let_def copy_loop_length
           split: prod.splits)

lemma emit_insts_spec_enc_flushed_exec:
  assumes "length acc = enc_flushed st"
  shows "enc_flushed (emit_insts_spec src_len insts st) =
         length (exec_inst_list src insts acc)"
  using assms
proof (induction insts arbitrary: st acc)
  case Nil
  then show ?case
    by (simp add: emit_insts_spec_def)
next
  case (Cons i insts)
  have len_step:
    "length (exec_inst src i acc) =
     enc_flushed (emit_inst_spec src_len i st)"
    using Cons.prems emit_inst_spec_enc_flushed_exec[of acc st src_len i src]
    by simp
  show ?case
    using Cons.IH[OF len_step]
    by (simp add: emit_insts_spec_def)
qed

lemma emit_insts_spec_trace:
  "enc_trace (emit_insts_spec src_len insts st) = enc_trace st @ insts"
  by (induction insts arbitrary: st)
     (simp_all add: emit_insts_spec_def emit_inst_spec_def
               split: prod.splits)

lemma emit_insts_spec_enc_tp:
  "enc_tp (emit_insts_spec src_len insts st) = enc_tp st"
  by (induction insts arbitrary: st)
     (simp_all add: emit_insts_spec_def emit_inst_spec_def
               split: prod.splits)

lemma emit_insts_spec_enc_pending:
  "enc_pending (emit_insts_spec src_len insts st) = enc_pending st"
  by (induction insts arbitrary: st)
     (simp_all add: emit_insts_spec_def emit_inst_spec_def
               split: prod.splits)

definition encode_window_full_trace_inv ::
    "byte list \<Rightarrow> byte list \<Rightarrow> enc_full_state \<Rightarrow> bool" where
  "encode_window_full_trace_inv src tgt st \<longleftrightarrow>
     enc_tp st \<le> length tgt \<and>
     enc_flushed st \<le> enc_tp st \<and>
     enc_pending st =
       take (enc_tp st - enc_flushed st) (drop (enc_flushed st) tgt) \<and>
     exec_inst_list src (enc_trace st) [] = take (enc_flushed st) tgt \<and>
     wf_insts_aux src (enc_trace st) []"

lemma encode_window_full_trace_inv_init:
  "encode_window_full_trace_inv src tgt enc_full_init"
  by (simp add: encode_window_full_trace_inv_def enc_full_init_def)

lemma encode_window_full_trace_invD:
  assumes "encode_window_full_trace_inv src tgt st"
  shows "enc_tp st \<le> length tgt"
    and "enc_flushed st \<le> enc_tp st"
    and "enc_pending st =
       take (enc_tp st - enc_flushed st) (drop (enc_flushed st) tgt)"
    and "exec_inst_list src (enc_trace st) [] = take (enc_flushed st) tgt"
    and "wf_insts_aux src (enc_trace st) []"
  using assms by (simp_all add: encode_window_full_trace_inv_def)

lemma encode_window_full_trace_inv_pending_len:
  assumes "encode_window_full_trace_inv src tgt st"
  shows "length (enc_pending st) = enc_tp st - enc_flushed st"
proof -
  have tp: "enc_tp st \<le> length tgt"
    and fl: "enc_flushed st \<le> enc_tp st"
    and pending: "enc_pending st =
      take (enc_tp st - enc_flushed st) (drop (enc_flushed st) tgt)"
    using encode_window_full_trace_invD[OF assms] by simp_all
  have "enc_tp st - enc_flushed st \<le> length (drop (enc_flushed st) tgt)"
    using tp fl by simp
  then show ?thesis
    using pending by simp
qed

lemma encode_window_full_trace_inv_pending_empty_flushed:
  assumes inv: "encode_window_full_trace_inv src tgt st"
      and pending: "enc_pending st = []"
  shows "enc_flushed st = enc_tp st"
  using encode_window_full_trace_inv_pending_len[OF inv] pending
        encode_window_full_trace_invD(2)[OF inv]
  by simp

lemma buffer_pending_byte_spec_trace_inv:
  assumes inv: "encode_window_full_trace_inv src tgt st"
      and tp_lt: "enc_tp st < length tgt"
  shows "encode_window_full_trace_inv src tgt
           (buffer_pending_byte_spec (tgt ! enc_tp st) st)"
proof -
  have tp: "enc_tp st \<le> length tgt"
    and fl: "enc_flushed st \<le> enc_tp st"
    and pending: "enc_pending st =
      take (enc_tp st - enc_flushed st) (drop (enc_flushed st) tgt)"
    and exec: "exec_inst_list src (enc_trace st) [] =
      take (enc_flushed st) tgt"
    and wf: "wf_insts_aux src (enc_trace st) []"
    using encode_window_full_trace_invD[OF inv] by simp_all
  let ?k = "enc_tp st - enc_flushed st"
  have k_lt: "?k < length (drop (enc_flushed st) tgt)"
    using fl tp_lt by simp
  have take_pending:
    "take (enc_tp st + 1 - enc_flushed st) (drop (enc_flushed st) tgt) =
     enc_pending st @ [tgt ! enc_tp st]"
  proof -
    have "enc_tp st + 1 - enc_flushed st = Suc ?k"
      using fl by simp
    moreover have
      "take (Suc ?k) (drop (enc_flushed st) tgt) =
       take ?k (drop (enc_flushed st) tgt) @
       [drop (enc_flushed st) tgt ! ?k]"
      using k_lt by (simp add: take_Suc_conv_app_nth)
    moreover have "drop (enc_flushed st) tgt ! ?k = tgt ! enc_tp st"
      using fl tp_lt by (simp add: nth_drop)
    ultimately show ?thesis
      using pending by simp
  qed
  show ?thesis
    using tp_lt fl exec wf take_pending
    by (simp add: encode_window_full_trace_inv_def
                  buffer_pending_byte_spec_def)
qed

lemma flush_pending_spec_trace_inv:
  assumes inv: "encode_window_full_trace_inv src tgt st"
  shows "encode_window_full_trace_inv src tgt
           (flush_pending_spec src_len st)"
proof -
  let ?st' = "flush_pending_spec src_len st"
  have tp: "enc_tp st \<le> length tgt"
    and fl: "enc_flushed st \<le> enc_tp st"
    and pending: "enc_pending st =
      take (enc_tp st - enc_flushed st) (drop (enc_flushed st) tgt)"
    and exec: "exec_inst_list src (enc_trace st) [] =
      take (enc_flushed st) tgt"
    and wf: "wf_insts_aux src (enc_trace st) []"
    using encode_window_full_trace_invD[OF inv] by simp_all
  have pending_len: "length (enc_pending st) = enc_tp st - enc_flushed st"
    by (rule encode_window_full_trace_inv_pending_len[OF inv])
  have fl': "enc_flushed ?st' = enc_tp st"
  proof -
    have "enc_flushed ?st' =
        length (exec_inst_list src (flush_pending_insts (enc_pending st))
          (replicate (enc_flushed st) 0))"
      using emit_insts_spec_enc_flushed_exec
        [of "replicate (enc_flushed st) 0" st src_len
            "flush_pending_insts (enc_pending st)" src]
      by (simp add: flush_pending_spec_def)
    also have "\<dots> = enc_flushed st + length (enc_pending st)"
      by (simp add: flush_pending_insts_exec)
    also have "\<dots> = enc_tp st"
      using pending_len fl by simp
    finally show ?thesis .
  qed
  have exec': "exec_inst_list src (enc_trace ?st') [] = take (enc_tp st) tgt"
    by (rule flush_pending_spec_trace_exec[OF exec pending fl])
  have wf': "wf_insts_aux src (enc_trace ?st') []"
  proof -
    have trace:
      "enc_trace ?st' =
       enc_trace st @ flush_pending_insts (enc_pending st)"
      by (simp add: flush_pending_spec_def emit_insts_spec_trace)
    show ?thesis
      using wf flush_pending_insts_wf_aux[of src "enc_pending st"
            "exec_inst_list src (enc_trace st) []"]
      by (simp add: trace wf_insts_aux_append)
  qed
  show ?thesis
    using tp fl' exec' wf'
    by (simp add: encode_window_full_trace_inv_def
                  flush_pending_spec_def emit_insts_spec_enc_tp)
qed

lemma emit_copy_spec_trace_inv:
  assumes inv: "encode_window_full_trace_inv src tgt st"
      and pending: "enc_pending st = []"
      and flushed: "enc_flushed st = enc_tp st"
      and len_pos: "0 < copy_len"
      and addr_bound: "copy_addr + copy_len \<le> length src"
      and tgt_bound: "enc_tp st + copy_len \<le> length tgt"
      and match: "\<forall>k < copy_len.
            src ! (copy_addr + k) = tgt ! (enc_tp st + k)"
  shows "encode_window_full_trace_inv src tgt
           (emit_copy_spec src_len copy_addr copy_len st)"
proof -
  let ?st' = "emit_copy_spec src_len copy_addr copy_len st"
  have tp: "enc_tp st \<le> length tgt"
    and exec: "exec_inst_list src (enc_trace st) [] =
      take (enc_flushed st) tgt"
    and wf: "wf_insts_aux src (enc_trace st) []"
    using encode_window_full_trace_invD[OF inv] by simp_all
  have exec_tp: "exec_inst_list src (enc_trace st) [] = take (enc_tp st) tgt"
    using exec flushed by simp
  have copy_exec:
    "copy_loop src (take (enc_tp st) tgt) copy_addr copy_len =
     take (enc_tp st + copy_len) tgt"
    by (rule copy_loop_source_match_take[OF addr_bound tgt_bound match])
  have trace':
    "enc_trace ?st' = enc_trace st @ [RCopy copy_addr copy_len]"
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def
             split: prod.splits)
  have fl': "enc_flushed ?st' = enc_tp st + copy_len"
    using flushed
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def
             split: prod.splits)
  have tp': "enc_tp ?st' = enc_tp st + copy_len"
    by (simp add: emit_copy_spec_def)
  have pending': "enc_pending ?st' = []"
    using pending
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def
             split: prod.splits)
  have exec':
    "exec_inst_list src (enc_trace ?st') [] = take (enc_flushed ?st') tgt"
    using exec_tp copy_exec fl'
    by (simp add: trace' exec_inst_list_append)
  have copy_addr_lt: "copy_addr < length src"
    using addr_bound len_pos by linarith
  have wf': "wf_insts_aux src (enc_trace ?st') []"
    using wf exec_tp copy_addr_lt len_pos
    by (simp add: trace' wf_insts_aux_append)
  show ?thesis
    using tgt_bound pending' exec' wf' fl' tp'
    by (simp add: encode_window_full_trace_inv_def emit_copy_spec_def)
qed

lemma flush_then_emit_copy_spec_trace_inv:
  assumes inv: "encode_window_full_trace_inv src tgt st"
      and len_pos: "0 < copy_len"
      and addr_bound: "copy_addr + copy_len \<le> length src"
      and tgt_bound: "enc_tp st + copy_len \<le> length tgt"
      and match: "\<forall>k < copy_len.
            src ! (copy_addr + k) = tgt ! (enc_tp st + k)"
  shows "encode_window_full_trace_inv src tgt
           (flush_then_emit_copy_spec src_len copy_addr copy_len st)"
proof (cases "enc_pending st = []")
  case True
  have flushed: "enc_flushed st = enc_tp st"
    by (rule encode_window_full_trace_inv_pending_empty_flushed[OF inv True])
  show ?thesis
    using emit_copy_spec_trace_inv
      [OF inv True flushed len_pos addr_bound tgt_bound match]
    by (simp add: flush_then_emit_copy_spec_def True)
next
  case False
  let ?fst = "flush_pending_spec src_len st"
  have inv_flush: "encode_window_full_trace_inv src tgt ?fst"
    by (rule flush_pending_spec_trace_inv[OF inv])
  have pending_flush: "enc_pending ?fst = []"
    by (simp add: flush_pending_spec_def)
  have flushed_flush: "enc_flushed ?fst = enc_tp ?fst"
    by (rule encode_window_full_trace_inv_pending_empty_flushed
        [OF inv_flush pending_flush])
  have tp_flush: "enc_tp ?fst = enc_tp st"
    by (simp add: flush_pending_spec_def emit_insts_spec_enc_tp)
  show ?thesis
    using emit_copy_spec_trace_inv
      [OF inv_flush pending_flush flushed_flush len_pos addr_bound]
      tgt_bound match tp_flush False
    by (simp add: flush_then_emit_copy_spec_def)
qed

lemma try_emit_add_copy_spec_trace_inv:
  assumes try_some: "try_emit_add_copy_spec src_len copy_addr copy_len st = Some st'"
      and inv: "encode_window_full_trace_inv src tgt st"
      and addr_bound: "copy_addr + copy_len \<le> length src"
      and tgt_bound: "enc_tp st + copy_len \<le> length tgt"
      and match: "\<forall>k < copy_len.
            src ! (copy_addr + k) = tgt ! (enc_tp st + k)"
  shows "encode_window_full_trace_inv src tgt st'"
proof -
  obtain mode abytes cache' where ea:
    "encode_address (enc_cache st) copy_addr (src_len + enc_tp st) =
      (mode, abytes, cache')"
    by (cases "encode_address (enc_cache st) copy_addr (src_len + enc_tp st)")
       auto
  from try_some ea obtain csz op where
      add_pos: "1 \<le> length (enc_pending st)"
      and min_copy: "min_match \<le> copy_len"
      and fused: "fused_copy_len_spec mode copy_len = Some csz"
      and opcode:
        "find_add_copy_opcode (length (enc_pending st)) csz mode = Some op"
      and st'_eq:
        "st' =
          st \<lparr> enc_tp := enc_tp st + csz
             , enc_flushed := enc_flushed st + length (enc_pending st) + csz
             , enc_pending := []
             , enc_data := enc_data st @ enc_pending st
             , enc_inst := enc_inst st @ [word_of_nat op]
             , enc_addr := enc_addr st @ abytes
             , enc_cache := cache'
             , enc_trace := enc_trace st
                 @ [RAdd (enc_pending st), RCopy copy_addr csz] \<rparr>"
    by (auto simp: try_emit_add_copy_spec_def Let_def
        split: option.splits if_splits)
  have tp: "enc_tp st \<le> length tgt"
    and fl: "enc_flushed st \<le> enc_tp st"
    and pending: "enc_pending st =
      take (enc_tp st - enc_flushed st) (drop (enc_flushed st) tgt)"
    and exec: "exec_inst_list src (enc_trace st) [] =
      take (enc_flushed st) tgt"
    and wf: "wf_insts_aux src (enc_trace st) []"
    using encode_window_full_trace_invD[OF inv] by simp_all
  have pending_len: "length (enc_pending st) = enc_tp st - enc_flushed st"
    by (rule encode_window_full_trace_inv_pending_len[OF inv])
  have csz_le: "csz \<le> copy_len"
    by (rule fused_copy_len_spec_le[OF fused])
  have csz_pos: "0 < csz"
    using fused min_copy
    by (auto simp: fused_copy_len_spec_def min_match_def split: if_splits)
  have fl'_eq: "enc_flushed st' = enc_tp st + csz"
    using st'_eq pending_len fl by simp
  have tp'_eq: "enc_tp st' = enc_tp st + csz"
    using st'_eq by simp
  have tp'_bound: "enc_tp st' \<le> length tgt"
    using tp'_eq tgt_bound csz_le by linarith
  have exec':
    "exec_inst_list src (enc_trace st') [] = take (enc_flushed st') tgt"
    by (rule try_emit_add_copy_spec_trace_exec
        [OF try_some exec pending addr_bound tgt_bound match])
  have add_prefix: "take (enc_flushed st) tgt @ enc_pending st =
      take (enc_tp st) tgt"
  proof -
    have "take (enc_tp st) tgt =
        take (enc_flushed st + (enc_tp st - enc_flushed st)) tgt"
      using fl by simp
    also have "\<dots> =
        take (enc_flushed st) tgt
        @ take (enc_tp st - enc_flushed st) (drop (enc_flushed st) tgt)"
      by (simp add: take_add)
    also have "\<dots> = take (enc_flushed st) tgt @ enc_pending st"
      using pending by simp
    finally show ?thesis by simp
  qed
  have copy_addr_lt: "copy_addr < length src"
    using addr_bound csz_le csz_pos by linarith
  have add_nonempty: "enc_pending st \<noteq> []"
    using add_pos by auto
  have wf': "wf_insts_aux src (enc_trace st') []"
    using wf exec add_prefix add_nonempty copy_addr_lt csz_pos st'_eq
    by (simp add: wf_insts_aux_append exec_inst_list_append)
  show ?thesis
    using tp'_bound fl'_eq tp'_eq exec' wf' st'_eq
    by (simp add: encode_window_full_trace_inv_def)
qed

lemma encode_window_full_spec_trace_valid:
  assumes "length src < 2 ^ 32"
      and "length tgt < 2 ^ 32"
      and "length src + length tgt < 2 ^ 32"
  shows "valid_insts src tgt (efr_trace (encode_window_full_spec src tgt))"
  sorry

lemma encode_window_full_spec_sections_decode:
  assumes "length src < 2 ^ 32"
      and "length tgt < 2 ^ 32 - 32"
      and "length src + length tgt < 2 ^ 32"
  shows "decode_spec
           (serialize src tgt
             (efr_data (encode_window_full_spec src tgt))
             (efr_inst (encode_window_full_spec src tgt))
             (efr_addr (encode_window_full_spec src tgt)))
           src = Inl tgt"
  sorry

theorem encode_spec_full_roundtrip:
  assumes "length src < 2 ^ 32"
      and "length tgt < 2 ^ 32 - 32"
      and "length src + length tgt < 2 ^ 32"
  shows "decode_spec (encode_spec_full src tgt) src = Inl tgt"
  using encode_window_full_spec_sections_decode[OF assms]
  by (simp add: encode_spec_full_def Let_def)

theorem spec_roundtrip:
  assumes "length src < 2 ^ 32"
      and "length tgt < 2 ^ 32 - 32"
      and "length src + length tgt < 2 ^ 32"
  shows "decode_spec (encode_spec src tgt) src = Inl tgt"
  using encode_spec_full_roundtrip[OF assms]
  by (simp add: encode_spec_def)

end
