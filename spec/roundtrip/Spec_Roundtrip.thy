(*
  Top-level roundtrip theorem: decoding what the encoder produced recovers
  the target.

  The spec encoder uses a degenerate `generate_instructions` that emits a
  single RAdd covering the whole target. That's enough for the theorem —
  a smarter matcher is a refinement — but it keeps the proof tractable at
  the Phase A layer.

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

(* ---------- encode_spec for a target of length 1..17 and empty source ---------- *)
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
    by (simp add: vdlen vtgt vdata vinst vaddr wi_tests di_tests)
qed

(*
  The encoder, with the degenerate single-RAdd matcher, produces a
  concrete serialized byte list. Here we state and prove the shape of
  the output for the small (1..17) target, empty-source case.

  NB: for this lemma we only need the list-shape equation; the varint
  roundtrip is exercised transitively by parse_window.
*)
lemma encode_spec_small_empty_shape:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
  shows "encode_spec [] tgt =
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
  by (simp add: encode_spec_def serialize_from_insts_def generate_instructions_def serialize_def Let_def
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
  shows   "decode_spec (encode_spec [] tgt) [] = Inl tgt"
proof -
  let ?op = "word_of_nat (1 + length tgt) :: byte"
  let ?dlen = "1 + varint_size (length tgt) + varint_size (length tgt)
              + varint_size 1 + varint_size 0 + length tgt + 1"
  have shape: "encode_spec [] tgt =
                 magic_bytes @ [0x00, 0x00]
               @ varint_encode ?dlen
               @ varint_encode (length tgt)
               @ [0x00]
               @ varint_encode (length tgt)
               @ varint_encode 1
               @ varint_encode 0
               @ tgt
               @ [?op]"
    using encode_spec_small_empty_shape[OF assms(1,2)] by simp

  have ph: "parse_header (encode_spec [] tgt)
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

(* ---------- encode_window / encode_spec for the general case ---------- *)

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

lemma encode_spec_general_empty_shape:
  assumes "length tgt > 17 \<or> length tgt = 0"
  shows "encode_spec [] tgt =
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
  by (simp add: encode_spec_def serialize_from_insts_def generate_instructions_def serialize_def Let_def
                split_def magic_bytes_def add.commute add.left_commute)

(* Parse_window + apply_window for the general case. *)

lemma spec_roundtrip_empty_src_large:
  assumes "length tgt > 17 \<or> length tgt = 0"
          "length tgt < 2 ^ 32 - 32"
  shows   "decode_spec (encode_spec [] tgt) [] = Inl tgt"
proof -
  let ?inst = "(1 :: byte) # varint_encode (length tgt)"
  let ?tlen_sz = "varint_size (length tgt)"
  let ?inst_sz = "varint_size (length ?inst)"
  let ?dlen = "1 + ?tlen_sz + ?tlen_sz + ?inst_sz + varint_size 0
              + length tgt + length ?inst"

  have tgt_bd: "length tgt < 2 ^ 32" using assms(2) by simp
  have inst_len_eq: "length ?inst = 1 + length (varint_encode (length tgt))"
    by simp

  have shape: "encode_spec [] tgt =
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
    by (simp add: encode_spec_def serialize_from_insts_def generate_instructions_def serialize_def Let_def
                  split_def magic_bytes_def add.commute add.left_commute)

  have ph: "parse_header (encode_spec [] tgt)
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
  shows   "decode_spec (encode_spec [] tgt) [] = Inl tgt"
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
    by (simp add: vsl vso vdlen vtgt vdata vinst vaddr wi_tests_1 di_tests)
qed

(* ---------- encode_spec for non-empty source (small/large tgt) ---------- *)

lemma encode_spec_nonempty_src_shape_small:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
          "length src > 0"
  shows "encode_spec src tgt =
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
  by (simp add: encode_spec_def serialize_from_insts_def generate_instructions_def serialize_def Let_def
                split_def magic_bytes_def add.commute add.left_commute)

lemma encode_spec_nonempty_src_shape_large:
  assumes "length tgt > 17 \<or> length tgt = 0"
          "length src > 0"
  shows "encode_spec src tgt =
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
  by (simp add: encode_spec_def serialize_from_insts_def generate_instructions_def serialize_def Let_def
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
  shows   "decode_spec (encode_spec src tgt) src = Inl tgt"
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

  have shape: "encode_spec src tgt =
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
    using encode_spec_nonempty_src_shape_small[OF assms(1,2,4)] by simp

  have ph: "parse_header (encode_spec src tgt)
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
  shows   "decode_spec (encode_spec src tgt) src = Inl tgt"
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

  have shape: "encode_spec src tgt =
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
    using encode_spec_nonempty_src_shape_large[OF assms(1,3)] by simp

  have ph: "parse_header (encode_spec src tgt)
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

theorem spec_roundtrip:
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32 - 32"
  shows   "decode_spec (encode_spec src tgt) src = Inl tgt"
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
    have "let (d, ib, ab, c'', tp') = encode_one (RAdd bs) src_len (length tgt_so_far) c [] [] []
       in decode_one src_seg (length src_seg) tgt_len
             \<lparr> ds_data_rem = d @ dr, ds_inst_rem = ib @ ir
             , ds_addr_rem = ab @ ar, ds_cache = c, ds_tgt = tgt_so_far \<rparr>
          = Inl \<lparr> ds_data_rem = dr, ds_inst_rem = ir
                , ds_addr_rem = ar, ds_cache = c'', ds_tgt = tgt_so_far @ bs \<rparr>"
      using encode_one_decode_one_add[OF wf_i bd_i tgt_ge,
        where data_rest = dr and inst_rest = ir and addr_rest = ar
          and src_seg = src_seg and src_seg_len = "length src_seg"
          and c = c and src_len = src_len]
      by simp
    thus ?thesis using eo0 RAdd by (simp add: split_def Let_def)
  next
    case (RRun b n)
    from Cons.prems(2) RRun have wf_i: "n > 0" by simp
    from bi_hd RRun have bd_i: "n < 2 ^ 32" by simp
    from tgt_len_ge RRun have tgt_ge: "length tgt_so_far + n \<le> tgt_len" by simp
    have "let (d, ib, ab, c'', tp') = encode_one (RRun b n) src_len (length tgt_so_far) c [] [] []
       in decode_one src_seg (length src_seg) tgt_len
             \<lparr> ds_data_rem = d @ dr, ds_inst_rem = ib @ ir
             , ds_addr_rem = ab @ ar, ds_cache = c, ds_tgt = tgt_so_far \<rparr>
          = Inl \<lparr> ds_data_rem = dr, ds_inst_rem = ir
                , ds_addr_rem = ar, ds_cache = c'', ds_tgt = tgt_so_far @ replicate n b \<rparr>"
      using encode_one_decode_one_run[OF wf_i bd_i tgt_ge,
        where data_rest = dr and inst_rest = ir and addr_rest = ar
          and src_seg = src_seg and src_seg_len = "length src_seg"
          and c = c and src_len = src_len]
      by simp
    thus ?thesis using eo0 RRun by (simp add: split_def)
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
        also have "\<dots> \<ge> length tgt_so_far"
          by (simp add: exec_inst_list_length)
        finally show ?thesis .
      qed
      thus ?thesis using Cons.prems(8) by linarith
    qed
    have "let (d, ib, ab, c'', tp') = encode_one (RCopy a n) src_len (length tgt_so_far) c [] [] []
       in decode_one src_seg (length src_seg) tgt_len
             \<lparr> ds_data_rem = d @ dr, ds_inst_rem = ib @ ir
             , ds_addr_rem = ab @ ar, ds_cache = c, ds_tgt = tgt_so_far \<rparr>
          = Inl \<lparr> ds_data_rem = dr, ds_inst_rem = ir
                , ds_addr_rem = ar, ds_cache = c'', ds_tgt = copy_loop src_seg tgt_so_far a n \<rparr>"
      using encode_one_decode_one_copy[OF wf_i(1) bd_i(1) bd_i(2) wf_i(2) here_bd tgt_ge
              Cons.prems(5),
        where data_rest = dr and inst_rest = ir and addr_rest = ar
          and src_seg = src_seg and c = c]
      by simp
    thus ?thesis using eo0 RCopy by (simp add: split_def)
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
    using ib0_ne by simp
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
    using do_step ih_mono fuel_eq by simp
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
      using parse_window_no_source_head[OF dlen_bd tgt_bd assms(3,4,5)] .
    show ?thesis
      using ph' pw len_zero
      by (simp add: decode_spec_def Let_def)
  qed
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

  have decode_ok: "decode_loop (length inst_bytes) src (length src) (length tgt)
      \<lparr> ds_data_rem = data, ds_inst_rem = inst_bytes, ds_addr_rem = addr_bytes
      , ds_cache = cache_init, ds_tgt = [] \<rparr>
    = Inl \<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = []
          , ds_cache = enc_cache, ds_tgt = tgt \<rparr>"
    using encode_window_loop_decode_loop[OF ewl wf bi refl refl src_bd tgt_len_eq combined_bd]
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
    using decode_ok
    by (simp add: apply_window_def Let_def)

  show ?thesis
    unfolding serialized
    using spr aw by (simp add: Let_def)
qed

(* The matcher-parametric corollary. With the degenerate matcher
   generate_instructions src tgt = [RAdd tgt], this coincides with
   spec_roundtrip above when length tgt > 0. For length tgt = 0, the
   degenerate [RAdd []] fails wf_insts, so we delegate to spec_roundtrip
   unconditionally since it handles the empty case directly. *)
corollary spec_roundtrip':
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32 - 32"
          "length src + length tgt < 2 ^ 32"
  shows   "decode_spec (encode_spec src tgt) src = Inl tgt"
  using spec_roundtrip[OF assms(1,2)] .

end
