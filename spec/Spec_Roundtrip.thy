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
    Encoder_Spec
    Decoder_Spec
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

end
